"""Adapter: a bounded-model-checker run log -> receipt schema 2.0.0.

This module parses the console output of the Kani Rust verifier (a
bounded model checker built on CBMC) into one `Receipt` per harness. It
is written against the shape of that tool's output, and nothing else in
`autoprover_ref` depends on it; the rest of the package stays
tool-agnostic.

**What the log can and cannot tell you.** A verification log records what
the run FOUND. It does not record what the run WAS. Specifically, none of
the following appear anywhere in the output, at any verbosity:

  * which build of the verifier ran (the banner gives a release version,
    which does not distinguish two builds of that release), which solver
    and backend versions were in play, or which unstable-feature flags
    were in force — and those flags change what a verdict MEANS, not
    merely how it was reached;
  * which repository and commit the checked source was at;
  * which claim this run is evidence for.

So `parse_kani_log` takes an `invocation` mapping supplying exactly
those, and records them as given. It never infers them from paths in the
log, from the working directory, or from anything else in scope. If the
caller's invocation record is wrong, the receipts are wrong — that is a
property of any provenance record, and the honest response is to make
the record explicit rather than to manufacture one.

**Cover properties are not the solver's satisfiability.** The tool's
output contains, from its own solver, lines of the form ``SAT checker:
instance is UNSATISFIABLE``. That is a statement about one propositional
query the solver just answered, not about any property in the harness,
and reading it as a cover-property outcome would turn ordinary solver
progress output into a fabricated vacuity finding. This parser only ever
reads a status from a ``Status:`` line inside a ``RESULTS:``/``SUMMARY:``
section, bound to a preceding ``Check N: <name>`` line, and it maps
``UNSATISFIABLE`` to the `vacuous` obligation status ONLY for a check
whose name marks it as a cover property. An ``UNSATISFIABLE`` status on
anything else is an error, not a guess.

**Tool failure is not property failure.** A check that fails because the
tool does not support a construct it reached says nothing about the code;
it says the tool declined to reason. Such a run becomes verdict `error`
with `failure_kind="unsupported-construct"` — but only when EVERY failing
check is of that kind. A run that also refuted a genuine property is a
genuine `rejected`, and the unsupported-construct failure is reported
alongside as a diagnostic rather than being allowed to mask the red.

**Counts are cross-checked.** The run's own trailer ("Complete - N
successfully verified harnesses, M failures, T total.") is compared with
what this parser produced. A mismatch raises `KaniAdapterError`: it means
the parser and the tool disagree about what happened, and quietly
returning the parser's answer would be exactly the silent-drop failure
the receipt discipline exists to prevent.

**Unclassified lines are findings.** Every line is either matched by a
structural rule, matched by a known-noise rule (build progress, solver
progress, CBMC instrumentation chatter), or reported in
`KaniParse.unclassified_lines` with its line number. New tool output the
parser has never seen shows up there instead of vanishing.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Mapping, Optional, Sequence

from ..receipts import (
    Checker,
    Control,
    Dependency,
    Obligation,
    Receipt,
    Subject,
    Tool,
    Toolchain,
    now_iso,
)

__all__ = [
    "KaniAdapterError",
    "KaniParse",
    "parse_kani_log",
    "parse_kani_log_detailed",
]


class KaniAdapterError(Exception):
    """Raised when the log cannot be parsed into receipts the parser is
    willing to stand behind: a malformed invocation record, a status the
    parser does not recognize, or a disagreement between the run's own
    reported counts and what was parsed."""


# --------------------------------------------------------------------------
# Line grammar
# --------------------------------------------------------------------------

_CHECKING_HARNESS = re.compile(r"^(?:Thread (?P<thread>\d+): )?Checking harness (?P<name>.+?)\.\.\.$")
# A bare "Thread N: " line (note the trailing space) is how the parallel
# driver announces "the following block belongs to thread N".
_THREAD_SWITCH = re.compile(r"^Thread (?P<thread>\d+):\s*$")
_RESULTS_HEADER = re.compile(r"^(?:RESULTS|SUMMARY|VERIFICATION RESULT):$")
_CHECK_HEADER = re.compile(r"^Check (?P<number>\d+): (?P<id>.+)$")
_CHECK_STATUS = re.compile(r"^\s+- Status: (?P<status>[A-Z_]+)$")
_CHECK_DESCRIPTION = re.compile(r"^\s+- Description: (?P<rest>.*)$")
_CHECK_LOCATION = re.compile(r"^\s+- Location: ")
_FAILED_SUMMARY = re.compile(
    r"^\s*\*\* (?P<failed>\d+) of (?P<total>\d+) failed(?: \((?P<unreachable>\d+) unreachable\))?$"
)
_COVER_SUMMARY = re.compile(
    r"^\s*\*\* (?P<satisfied>\d+) of (?P<total>\d+) cover properties satisfied$"
)
_FAILED_CHECKS = re.compile(r"^Failed Checks: (?P<message>.*)$")
_FAILED_CHECKS_FILE = re.compile(r'^\s*File: ".*", line \d+,')
_VERIFICATION_RESULT = re.compile(
    r"^VERIFICATION:- (?P<result>SUCCESSFUL|FAILED)(?: \((?P<note>.*)\))?$"
)
_VERIFICATION_FAILED_FOR = re.compile(r"^Verification failed for - (?P<name>.+)$")
_TRAILER = re.compile(
    r"^Complete - (?P<successful>\d+) successfully verified harnesses, "
    r"(?P<failures>\d+) failures, (?P<total>\d+) total\.$"
)
_ERROR_DIAGNOSTIC = re.compile(r"^error(?:\[[^\]]+\])?: (?P<message>.*)$")

# Output that carries no verdict information: package build progress,
# solver progress, and the model checker's own instrumentation chatter.
# Deliberately a closed list — anything not here is reported as
# unclassified rather than assumed harmless.
_NOISE = tuple(re.compile(p) for p in (
    r"^$",
    r"^\s*(?:Compiling|Updating|Downloading|Downloaded|Finished|Adding|Installing|Blocking) ",
    r"^\s*Fresh ",
    r"^warning: ",
    r"^note: ",
    r"^help: ",
    r"^Kani Rust Verifier ",
    r"^CBMC \d",
    r"^CBMC version ",
    r"^Reading GOTO program",
    r"^Generating GOTO Program",
    r"^Removal of function pointers",
    r"^Generic Property Instrumentation",
    r"^Running with \d+ object bits",
    r"^Starting Bounded Model Checking",
    r"^Passing problem to propositional reduction",
    r"^Post-processing",
    r"^Running propositional reduction",
    r"^Solving with ",
    r"^\d+ variables, \d+ clauses",
    r"^SAT checker: instance is (?:SATISFIABLE|UNSATISFIABLE)",
    r"^Runtime [A-Za-z -]+: ",
    r"^Generated \d+ VCC\(s\)",
    r"^converting SSA",
    r"^slicing removed \d+ assignments",
    r"^size of program expression: ",
    r"^aborting path on assume\(false\)",
    r"^Unwinding loop ",
    r"^Unwinding recursion ",
    r"^Verification Time: ",
    r"^Manual Harness Summary:$",
    r"^Autoharness Summary:$",
    r"^\*\*\*\* WARNING: ",
    r"^Building error trace",
    r"^Solver: ",
))

_COVER_STATUSES = {
    "SATISFIED": "held",
    # A cover the solver could not satisfy is the one that MATTERS here:
    # the interesting case the harness claimed to reach is unreachable,
    # so anything proved "about" it was proved about nothing.
    "UNSATISFIABLE": "vacuous",
    "UNREACHABLE": "not-exercised",
    "UNDETERMINED": "not-exercised",
}

_ASSERTION_STATUSES = {
    "SUCCESS": "held",
    "FAILURE": "failed",
    "UNREACHABLE": "not-exercised",
    "UNDETERMINED": "not-exercised",
}

# A property whose failure means "the tool declined to reason about
# something it reached", not "the code is wrong".
_UNSUPPORTED_MARKER = ".unsupported_construct."
_UNSUPPORTED_TEXT = "is not currently supported by"

# The success line a harness gets when its whole point was to observe a
# failure (the tool's should-panic mode). The run passed, and a failing
# check inside it is the evidence of that.
_EXPECTED_PANIC_NOTE = "panics as expected"

_COVER_MARKER = ".cover."


@dataclass
class _Check:
    id: str
    status: str
    description: Optional[str]
    line: int


@dataclass
class _Block:
    name: str
    start_line: int
    result: Optional[str] = None
    result_note: Optional[str] = None
    checks: list = field(default_factory=list)
    failed_check_messages: list = field(default_factory=list)
    failed_properties: Optional[int] = None
    total_properties: Optional[int] = None
    unreachable_properties: Optional[int] = None
    covers_satisfied: Optional[int] = None
    covers_total: Optional[int] = None


@dataclass(frozen=True)
class KaniParse:
    """Everything the parser learned, including what it could not
    classify. `parse_kani_log` returns just `receipts`; callers that have
    to report on a real run (how many, what was odd, what was unreadable)
    want this."""

    receipts: tuple
    trailer: Optional[dict]
    unclassified_lines: tuple
    diagnostics: tuple
    harness_count: int

    @property
    def verdict_counts(self) -> dict:
        counts = {"accepted": 0, "rejected": 0, "error": 0}
        for receipt in self.receipts:
            counts[receipt.verdict] += 1
        return counts


# --------------------------------------------------------------------------
# Invocation record
# --------------------------------------------------------------------------

_INVOCATION_KEYS = {
    "claim_id", "candidate_id", "subject", "toolchain", "checker",
    "bound", "env_assumptions", "target_id_prefix", "control",
}
_REQUIRED_INVOCATION_KEYS = {
    "claim_id", "candidate_id", "subject", "toolchain", "checker",
    "bound", "env_assumptions",
}


def _require(mapping: Mapping, key: str, where: str):
    if key not in mapping:
        raise KaniAdapterError(f"invocation {where} is missing required key {key!r}")
    return mapping[key]


def _build_invocation(invocation: Mapping) -> dict:
    """Validate the caller-supplied invocation record and turn it into
    the receipt objects it describes. Strict on purpose: an unknown key
    is a typo that would otherwise silently produce receipts missing the
    provenance the caller thought they had supplied."""
    if not isinstance(invocation, Mapping):
        raise KaniAdapterError(
            f"invocation must be a mapping, got {type(invocation).__name__}"
        )
    unknown = sorted(set(invocation) - _INVOCATION_KEYS)
    if unknown:
        raise KaniAdapterError(
            f"unknown invocation key(s) {unknown}; known keys: {sorted(_INVOCATION_KEYS)}"
        )
    missing = sorted(_REQUIRED_INVOCATION_KEYS - set(invocation))
    if missing:
        raise KaniAdapterError(
            f"invocation is missing required key(s) {missing}. The log cannot supply these — "
            f"it records what the run found, not which build ran, on which source state, for "
            f"which claim"
        )

    subject_doc = _require(invocation, "subject", "subject")
    subject = Subject(
        repo=_require(subject_doc, "repo", "subject"),
        commit=_require(subject_doc, "commit", "subject"),
        unit=subject_doc.get("unit"),
    )

    toolchain_doc = _require(invocation, "toolchain", "toolchain")
    tool_doc = _require(toolchain_doc, "tool", "toolchain.tool")
    features = toolchain_doc.get("features", "__missing__")
    if features == "__missing__":
        raise KaniAdapterError(
            "invocation toolchain is missing required key 'features'. Use null if the tool has "
            "no feature-selection concept and [] if it has one and none were enabled — the two "
            "are different statements"
        )
    toolchain = Toolchain(
        tool=Tool(
            name=_require(tool_doc, "name", "toolchain.tool"),
            commit_or_version=_require(tool_doc, "commit_or_version", "toolchain.tool"),
        ),
        dependencies=tuple(
            Dependency(name=_require(d, "name", "toolchain.dependencies"),
                       version=_require(d, "version", "toolchain.dependencies"))
            for d in _require(toolchain_doc, "dependencies", "toolchain")
        ),
        flags=tuple(_require(toolchain_doc, "flags", "toolchain")),
        features=None if features is None else tuple(features),
    )

    checker_doc = _require(invocation, "checker", "checker")
    checker = Checker(
        kind="model-checker",
        name=_require(checker_doc, "name", "checker"),
        version=_require(checker_doc, "version", "checker"),
    )

    control_doc = invocation.get("control")
    control_spec = None
    if control_doc is not None:
        if "observed" in control_doc:
            raise KaniAdapterError(
                "invocation control must not declare 'observed': what a control showed is "
                "measured from the run, never declared alongside the prediction. Supply kind, "
                "expectation and of_claim only"
            )
        control_spec = {
            "kind": _require(control_doc, "kind", "control"),
            "expectation": _require(control_doc, "expectation", "control"),
            "of_claim": control_doc.get("of_claim", invocation["claim_id"]),
        }

    return {
        "claim_id": invocation["claim_id"],
        "candidate_id": invocation["candidate_id"],
        "subject": subject,
        "toolchain": toolchain,
        "checker": checker,
        "bound": invocation["bound"],
        "env_assumptions": invocation["env_assumptions"],
        "target_id_prefix": invocation.get("target_id_prefix", ""),
        "control_spec": control_spec,
    }


# --------------------------------------------------------------------------
# Parsing
# --------------------------------------------------------------------------


def _parse_blocks(log_text: str) -> tuple:
    """Split the log into per-harness blocks, returning
    (blocks, trailer, failed_for_names, unclassified, diagnostics)."""
    blocks: list = []
    thread_blocks: dict = {}
    current: Optional[_Block] = None
    trailer: Optional[dict] = None
    failed_for: list = []
    unclassified: list = []
    diagnostics: list = []

    pending_check: Optional[_Check] = None
    # A Description value is a quoted string that may run over several
    # lines; a Failed Checks message likewise runs until its File: line.
    description_buffer: Optional[list] = None
    failed_message_buffer: Optional[list] = None

    lines = log_text.splitlines()
    for index, line in enumerate(lines, start=1):
        if description_buffer is not None:
            description_buffer.append(line)
            if line.rstrip().endswith('"'):
                text = "\n".join(description_buffer).strip()
                if pending_check is not None:
                    pending_check.description = text.strip('"')
                description_buffer = None
            continue

        if failed_message_buffer is not None:
            if _FAILED_CHECKS_FILE.match(line) or not line.strip():
                message = "\n".join(failed_message_buffer).strip()
                if current is not None:
                    current.failed_check_messages.append(message)
                failed_message_buffer = None
                if not line.strip():
                    continue
                continue
            failed_message_buffer.append(line)
            continue

        match = _CHECKING_HARNESS.match(line)
        if match:
            block = _Block(name=match.group("name"), start_line=index)
            blocks.append(block)
            if match.group("thread") is not None:
                thread_blocks[match.group("thread")] = block
            else:
                current = block
            continue

        match = _THREAD_SWITCH.match(line)
        if match:
            thread = match.group("thread")
            if thread not in thread_blocks:
                raise KaniAdapterError(
                    f"line {index}: output attributed to thread {thread}, which never announced "
                    f"a harness — the parser cannot say which harness this block belongs to"
                )
            current = thread_blocks[thread]
            continue

        if _RESULTS_HEADER.match(line):
            if current is None:
                raise KaniAdapterError(
                    f"line {index}: a results section began before any harness was announced"
                )
            continue

        match = _CHECK_HEADER.match(line)
        if match:
            if current is None:
                raise KaniAdapterError(
                    f"line {index}: a check was reported before any harness was announced"
                )
            pending_check = _Check(
                id=match.group("id"), status="", description=None, line=index
            )
            current.checks.append(pending_check)
            continue

        match = _CHECK_STATUS.match(line)
        if match:
            if pending_check is None:
                raise KaniAdapterError(
                    f"line {index}: a status line with no preceding 'Check N:' line"
                )
            pending_check.status = match.group("status")
            continue

        match = _CHECK_DESCRIPTION.match(line)
        if match:
            rest = match.group("rest")
            if rest.startswith('"') and not (len(rest) > 1 and rest.rstrip().endswith('"')):
                description_buffer = [rest]
            elif pending_check is not None:
                pending_check.description = rest.strip().strip('"')
            continue

        if _CHECK_LOCATION.match(line):
            continue

        match = _COVER_SUMMARY.match(line)
        if match:
            if current is None:
                raise KaniAdapterError(f"line {index}: cover summary outside any harness block")
            current.covers_satisfied = int(match.group("satisfied"))
            current.covers_total = int(match.group("total"))
            continue

        match = _FAILED_SUMMARY.match(line)
        if match:
            if current is None:
                raise KaniAdapterError(f"line {index}: failure summary outside any harness block")
            current.failed_properties = int(match.group("failed"))
            current.total_properties = int(match.group("total"))
            unreachable = match.group("unreachable")
            current.unreachable_properties = int(unreachable) if unreachable else 0
            continue

        match = _FAILED_CHECKS.match(line)
        if match:
            if current is None:
                raise KaniAdapterError(f"line {index}: failed-check line outside any harness block")
            failed_message_buffer = [match.group("message")]
            continue

        match = _VERIFICATION_RESULT.match(line)
        if match:
            if current is None:
                raise KaniAdapterError(f"line {index}: a verdict line outside any harness block")
            if current.result is not None:
                raise KaniAdapterError(
                    f"line {index}: harness {current.name!r} reported a second verdict "
                    f"({match.group('result')}) after {current.result}"
                )
            current.result = match.group("result")
            current.result_note = match.group("note")
            current = None
            continue

        match = _VERIFICATION_FAILED_FOR.match(line)
        if match:
            failed_for.append(match.group("name"))
            continue

        match = _TRAILER.match(line)
        if match:
            trailer = {
                "successful": int(match.group("successful")),
                "failures": int(match.group("failures")),
                "total": int(match.group("total")),
                "line": index,
            }
            continue

        match = _ERROR_DIAGNOSTIC.match(line)
        if match:
            diagnostics.append({
                "line": index, "kind": "tool-error-diagnostic",
                "text": match.group("message"),
            })
            continue

        if any(pattern.match(line) for pattern in _NOISE):
            continue

        unclassified.append({"line": index, "text": line})

    if description_buffer is not None:
        raise KaniAdapterError(
            "log ended inside an unterminated check description — the run was truncated"
        )
    if failed_message_buffer is not None and current is not None:
        current.failed_check_messages.append("\n".join(failed_message_buffer).strip())

    return blocks, trailer, failed_for, unclassified, diagnostics


def _obligation_status(check: _Check) -> str:
    is_cover = _COVER_MARKER in check.id
    if is_cover:
        try:
            return _COVER_STATUSES[check.status]
        except KeyError:
            raise KaniAdapterError(
                f"line {check.line}: unrecognized status {check.status!r} on cover property "
                f"{check.id!r}"
            ) from None
    if check.status == "UNSATISFIABLE" or check.status == "SATISFIED":
        # These belong to cover properties. Meeting one on an ordinary
        # assertion means either the tool changed its vocabulary or this
        # parser mis-identified the property — either way, guessing which
        # is how a solver's progress line becomes a fabricated vacuity
        # finding.
        raise KaniAdapterError(
            f"line {check.line}: status {check.status!r} on {check.id!r}, which this parser "
            f"does not recognize as a cover property. Refusing to map it to an obligation "
            f"status by guessing"
        )
    try:
        return _ASSERTION_STATUSES[check.status]
    except KeyError:
        raise KaniAdapterError(
            f"line {check.line}: unrecognized check status {check.status!r} on {check.id!r}"
        ) from None


def _is_unsupported(check: _Check) -> bool:
    if _UNSUPPORTED_MARKER in check.id:
        return True
    return bool(check.description) and _UNSUPPORTED_TEXT in check.description


def _unique(ids: list) -> list:
    """Disambiguate repeated obligation ids (a tool may report the same
    failing check text more than once) rather than collapsing them, which
    would lose the fact that it failed twice."""
    seen: dict = {}
    out = []
    for value in ids:
        seen[value] = seen.get(value, 0) + 1
        out.append(value if seen[value] == 1 else f"{value} #{seen[value]}")
    return out


def _obligations_for(block: _Block) -> tuple:
    """Build the exhaustive obligation list for one harness.

    When the run reported per-check results, every check becomes an
    obligation. When it did not (the terse/parallel output format prints
    only aggregate counts), the parser cannot name individual properties,
    so it emits ONE aggregate entry plus one per named failing check —
    and says so in the ids rather than pretending to a per-property
    account it does not have.
    """
    obligations = []

    if block.checks:
        for check in block.checks:
            if not check.status:
                raise KaniAdapterError(
                    f"line {check.line}: check {check.id!r} has no status line"
                )
        ids = _unique([c.id for c in block.checks])
        for check, oid in zip(block.checks, ids):
            obligations.append(Obligation(id=oid, status=_obligation_status(check)))
    else:
        if block.failed_properties is None:
            raise KaniAdapterError(
                f"harness {block.name!r} (line {block.start_line}) reported neither per-check "
                f"results nor an aggregate failure count; there is nothing to build an "
                f"obligation account from"
            )
        obligations.append(Obligation(
            id=f"{block.name}::all-properties",
            status="held" if block.failed_properties == 0 else "failed",
        ))
        for oid in _unique([f"{block.name}::{m}" for m in block.failed_check_messages]):
            obligations.append(Obligation(id=oid, status="failed"))
        if block.covers_total is not None:
            obligations.append(Obligation(
                id=f"{block.name}::cover-properties",
                # Fewer satisfied than declared means at least one cover
                # the harness claimed to reach is unreachable.
                status="held" if block.covers_satisfied == block.covers_total else "vacuous",
            ))

    if block.result_note and _EXPECTED_PANIC_NOTE in block.result_note:
        # An inverted-expectation harness passes BY failing. Both facts
        # are kept: the failing checks stay `failed` (they did fail), and
        # this entry records why the run is nonetheless accepted, so a
        # reader is never left inferring it from a contradiction.
        obligations.append(Obligation(id=f"{block.name}::expected-panic", status="held"))

    return tuple(obligations)


def _verdict_for(block: _Block) -> tuple:
    """Return (verdict, failure_kind, unsupported_notes)."""
    unsupported = [c for c in block.checks if c.status == "FAILURE" and _is_unsupported(c)]
    genuine = [c for c in block.checks if c.status == "FAILURE" and not _is_unsupported(c)]

    if not block.checks:
        unsupported_messages = [
            m for m in block.failed_check_messages if _UNSUPPORTED_TEXT in m
        ]
        genuine_messages = [
            m for m in block.failed_check_messages if _UNSUPPORTED_TEXT not in m
        ]
    else:
        unsupported_messages = [c.id for c in unsupported]
        genuine_messages = [c.id for c in genuine]

    notes = list(unsupported_messages)

    if block.result is None:
        return "error", "tool-error", notes + [
            "no verdict line for this harness; the run did not finish it"
        ]

    if unsupported_messages and not genuine_messages:
        # Everything that failed was the tool declining to reason. That
        # is a scope fact about the tool, not a refutation of the code.
        return "error", "unsupported-construct", notes

    if block.result == "FAILED":
        return "rejected", None, notes
    return "accepted", None, notes


def _control_for(spec: Optional[dict], verdict: str, obligations: Sequence[Obligation]) -> Optional[Control]:
    if spec is None:
        return None
    expectation = spec["expectation"]
    if expectation == "sat":
        covers = [o for o in obligations if o.id.endswith("::cover-properties") or _COVER_MARKER in o.id]
        if not covers:
            observed = "no-cover-property"
        elif all(o.status == "held" for o in covers):
            observed = "sat"
        else:
            observed = "unsat"
    else:
        observed = {"accepted": "green", "rejected": "red", "error": "error"}[verdict]
    return Control(
        kind=spec["kind"],
        expectation=expectation,
        observed=observed,
        of_claim=spec["of_claim"],
    )


def parse_kani_log_detailed(
    log_text: str, invocation: Mapping, *, require_trailer: bool = True
) -> KaniParse:
    """Parse ``log_text`` into receipts, and report everything else the
    parser learned along the way (the run's own trailer, unclassified
    lines, tool diagnostics).

    `require_trailer=False` allows a truncated log (a run killed by a
    wall-clock limit, say) to be parsed without its final count line. Use
    it deliberately: the trailer is the only independent check that the
    parser saw every harness the run did.
    """
    context = _build_invocation(invocation)
    blocks, trailer, failed_for, unclassified, diagnostics = _parse_blocks(log_text)

    receipts = []
    for block in blocks:
        obligations = _obligations_for(block)
        verdict, failure_kind, notes = _verdict_for(block)

        if block.checks and block.failed_properties is not None:
            reported_failures = sum(1 for c in block.checks if c.status == "FAILURE")
            if reported_failures != block.failed_properties:
                raise KaniAdapterError(
                    f"harness {block.name!r}: the run reported {block.failed_properties} failing "
                    f"propert(ies) but {reported_failures} check(s) carry a FAILURE status; the "
                    f"parser and the tool disagree about this harness"
                )

        for note in notes:
            diagnostics.append({
                "harness": block.name,
                "kind": "unsupported-construct" if verdict != "error" or failure_kind ==
                        "unsupported-construct" else "no-verdict",
                "text": note,
            })

        control = _control_for(context["control_spec"], verdict, obligations)

        receipts.append(Receipt(
            target_id=f"{context['target_id_prefix']}{block.name}",
            candidate_id=context["candidate_id"],
            checker=context["checker"],
            verdict=verdict,
            certificate=None,
            harness=block.name,
            bound=context["bound"],
            env_assumptions=context["env_assumptions"],
            obligations=obligations,
            produced_at=now_iso(),
            claim_id=context["claim_id"],
            subject=context["subject"],
            toolchain=context["toolchain"],
            failure_kind=failure_kind,
            # Per-obligation hypothesis coverage is genuinely absent from
            # this tool's output: it reports whether a property held, not
            # how the explored states split across its precondition. Null
            # here says "the checker reported none", which is true.
            control=control,
        ))

    _cross_check_counts(blocks, receipts, trailer, failed_for, require_trailer)

    return KaniParse(
        receipts=tuple(receipts),
        trailer=trailer,
        unclassified_lines=tuple(unclassified),
        diagnostics=tuple(diagnostics),
        harness_count=len(blocks),
    )


def _cross_check_counts(blocks, receipts, trailer, failed_for, require_trailer) -> None:
    if trailer is None:
        if require_trailer:
            raise KaniAdapterError(
                "the log carries no 'Complete - N successfully verified harnesses, M failures, "
                "T total.' trailer, so the parser's harness count cannot be cross-checked "
                "against the run's own. Pass require_trailer=False only if you intend to "
                "accept a truncated log"
            )
        return

    successful = sum(1 for b in blocks if b.result == "SUCCESSFUL")
    failed = sum(1 for b in blocks if b.result == "FAILED")
    problems = []
    if len(blocks) != trailer["total"]:
        problems.append(
            f"the run reports {trailer['total']} harness(es) in total, the parser found "
            f"{len(blocks)}"
        )
    if successful != trailer["successful"]:
        problems.append(
            f"the run reports {trailer['successful']} successful, the parser found {successful}"
        )
    if failed != trailer["failures"]:
        problems.append(
            f"the run reports {trailer['failures']} failure(s), the parser found {failed}"
        )
    if failed_for:
        named = sorted(failed_for)
        parsed_failed = sorted(b.name for b in blocks if b.result == "FAILED")
        if named != parsed_failed:
            problems.append(
                f"the run names {named} as failed, the parser found {parsed_failed}"
            )
    if problems:
        raise KaniAdapterError(
            "the parser and the run disagree about what happened: "
            + "; ".join(problems)
            + ". Refusing to return receipts that would silently drop or invent harnesses"
        )


def parse_kani_log(log_text: str, invocation: Mapping) -> list:
    """Parse ``log_text`` into one receipt per harness.

    ``invocation`` supplies what the log cannot: `claim_id`,
    `candidate_id`, `subject` (repo/commit/unit), `toolchain`
    (tool name + build identity, dependency versions, flags, features),
    `checker` (name/version), `bound`, `env_assumptions`, and optionally
    `target_id_prefix` and a `control` block (kind, expectation,
    of_claim — never `observed`, which is measured from the run).

    Raises `KaniAdapterError` if the invocation record is incomplete, if
    a status is unrecognized, or if the run's own harness counts disagree
    with what was parsed. See `parse_kani_log_detailed` for the residue
    (unclassified lines, diagnostics) this convenience wrapper discards.
    """
    return list(parse_kani_log_detailed(log_text, invocation).receipts)
