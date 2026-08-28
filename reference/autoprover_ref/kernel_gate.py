"""The kernel gate: a checker as a sound oracle (ARCHITECTURE.md §4).

A candidate is never accepted on the strength of the prover's own claim
about it — only a checker process's exit status counts. This module
wraps an *injectable* checker command so the gate is not tied to any one
proof system: the default wiring happens to invoke Lean, because that is
what this repository's corpus is written in, but `KernelGate` itself
knows nothing about Lean syntax or semantics. Any command that reports
acceptance/rejection via its exit status can be plugged in through the
`checker_command` parameter.

The gate also enforces, in code rather than only in the schema, the
kernel-vs-model-checker distinction from ARCHITECTURE.md §4: a
`kind="kernel"` gate refuses to accept a harness/bound/env_assumptions
triple (a proof kernel's verdict is not relative to any of those), and a
`kind="model-checker"` gate refuses to omit them (its verdict is only
valid relative to that triple, never portable the way a kernel's
re-runnable proof object is).

**Tool failure is not property failure.** A checker that times out, runs
out of memory, or meets a construct it cannot model has produced no
verdict at all. If such a run were reported as `rejected`, a scheduler
would read it as "the candidate is wrong" and requeue for a new
candidate — chasing a ghost, when the honest response is "give this one
more resources" or "this clause is out of scope for this tool". So the
seam carries a `failure_kind`, the gate maps any non-null one to
verdict `error` with the kind recorded, and the seam takes a `timeout`
so a hung checker becomes a recorded `timeout` error rather than a
process nobody bounded. `error` is a legacy 1.0.0 verdict too (the
schema always had it in its enum), so a gate emitting 1.0.0 receipts
maps a reported `failure_kind` to that same `error` verdict — it just
cannot record *which kind* of failure, since 1.0.0 predates that field.
Either way an unlaunchable or crashed checker always leaves a receipt
behind; it never strands the queue with an exception and no artifact.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Mapping, Optional, Sequence, Union

from .receipts import (
    Certificate,
    Checker,
    Control,
    Coverage,
    Obligation,
    Receipt,
    Subject,
    Toolchain,
    now_iso,
)

__all__ = [
    "CheckerResult",
    "CheckerCommand",
    "lean_checker_command",
    "KernelGate",
]

_FAILURE_KINDS = ("timeout", "oom", "unsupported-construct", "tool-error")


@dataclass(frozen=True)
class CheckerResult:
    """What a pluggable checker command reports back to the gate. The
    gate trusts nothing here except `accepted` (derived from the
    process's own exit status by the command implementation), the
    optional per-obligation detail, and `failure_kind`; `stdout`/`stderr`
    are kept only for diagnostics, never interpreted as part of the
    verdict.
    """

    accepted: bool
    exit_code: int
    stdout: str = ""
    stderr: str = ""
    # Optional per-obligation status detail a richer checker (e.g. a
    # model checker that can report per-property coverage) may supply.
    # A plain kernel invocation (a whole-file accept/reject) typically
    # leaves this None, and the gate falls back to reducing every
    # requested obligation to the file-level verdict.
    obligation_statuses: Optional[dict] = None
    # Optional per-obligation hypothesis coverage, keyed by obligation
    # id, as `receipts.Coverage` values (or plain dicts of the same
    # shape). Before receipt 2.0.0 a checker that measured this had
    # nowhere to put it, so the semantic audit's unexercised-hypothesis
    # check abstained on everything the pipeline drove through it; it
    # rides on the receipt now.
    obligation_coverage: Optional[Mapping[str, object]] = None
    # Non-null exactly when the checker FAILED TO PRODUCE A VERDICT, and
    # then it says which way: "timeout" | "oom" | "unsupported-construct"
    # | "tool-error". `accepted` is meaningless in that case and the gate
    # ignores it. "unsupported-construct" in particular is a fact about
    # the tool's scope, not about the candidate, and must never be
    # routed as if a property had been refuted.
    failure_kind: Optional[str] = None

    def __post_init__(self) -> None:
        if self.failure_kind is not None and self.failure_kind not in _FAILURE_KINDS:
            raise ValueError(
                f"failure_kind must be null or one of {_FAILURE_KINDS}, got {self.failure_kind!r}"
            )


# A checker command takes the candidate file path and a timeout in
# seconds (None meaning "no timeout imposed by the caller"), and returns
# a result. This is the entire seam the gate depends on — swap this out
# and the gate works against any checker, Lean or otherwise. The timeout
# is part of the seam rather than an implementation detail of one command
# because an unbounded checker run is how a tool failure gets mistaken
# for a property that is merely "still being checked".
CheckerCommand = Callable[[Path, Optional[float]], CheckerResult]


def lean_checker_command(
    lean_executable: str = "lean", extra_args: Sequence[str] = ()
) -> CheckerCommand:
    """Default checker command: runs ``lean <extra_args...> <file>`` and
    treats a zero exit code as kernel acceptance. This is *a* default
    value for `checker_command`, not machinery baked into `KernelGate` —
    nothing in this module besides this one function knows what "lean"
    is. Pass `extra_args=("--", ...)` or point `lean_executable` at
    ``lake env lean`` (as a shell wrapper) for a project that needs its
    dependencies on the path; both are just different argv choices for a
    subprocess call.

    A run that exceeds `timeout` returns `failure_kind="timeout"` — the
    gate turns that into an `error` verdict, never a `rejected` one. Two
    more ways a run produces no verdict are reported the same way, as
    `failure_kind="tool-error"`:

      * the process was killed by a SIGNAL (a crash, an OOM kill, an
        operator's `kill`). POSIX reports that as a NEGATIVE returncode,
        which is not the checker answering "no" — it is the checker not
        finishing. Reading it as a non-zero exit would file a crash as a
        refutation of the candidate.
      * the executable could not be launched at all (not installed, not
        executable, wrong path). Raising there would leave the caller
        with an exception and no receipt, so the one artifact recording
        that the run happened would not exist. A missing checker says
        nothing about the candidate, and that "nothing" has to be
        recorded like any other verdict-less run.
    """

    def run(file_path: Path, timeout: Optional[float] = None) -> CheckerResult:
        cmd = [lean_executable, *extra_args, str(file_path)]
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            return CheckerResult(
                accepted=False,
                exit_code=-1,
                stdout=exc.stdout if isinstance(exc.stdout, str) else "",
                stderr=exc.stderr if isinstance(exc.stderr, str) else "",
                failure_kind="timeout",
            )
        except OSError as exc:
            # FileNotFoundError, PermissionError, and friends: the
            # checker never ran.
            return CheckerResult(
                accepted=False,
                exit_code=-1,
                stderr=f"could not launch checker {cmd[0]!r}: {exc}",
                failure_kind="tool-error",
            )
        if proc.returncode < 0:
            return CheckerResult(
                accepted=False,
                exit_code=proc.returncode,
                stdout=proc.stdout,
                stderr=proc.stderr,
                failure_kind="tool-error",
            )
        return CheckerResult(
            accepted=(proc.returncode == 0),
            exit_code=proc.returncode,
            stdout=proc.stdout,
            stderr=proc.stderr,
        )

    return run


class KernelGate:
    """Wraps a checker command as a sound oracle and emits a Receipt.

    Never treats the prover's own claim as a verdict: `check()` invokes
    `checker_command` and reads the resulting `CheckerResult.accepted`
    (which the command implementation must derive from the checker
    process's own exit status), and nothing else determines the verdict —
    except a reported `failure_kind`, which means no verdict was produced
    at all.

    **Which receipt version this gate emits** is decided at construction,
    explicitly. Supply `subject`, `toolchain` and `claim_id` and the gate
    emits receipt schema 2.0.0; supply none of them and it emits 1.0.0.
    Supplying only some of them is a construction error rather than a
    silent downgrade: 2.0.0 provenance is all-or-nothing, and a gate that
    quietly dropped two thirds of it would produce receipts that look
    fully attributed and are not.
    """

    def __init__(
        self,
        *,
        checker_command: CheckerCommand,
        checker_name: str,
        checker_version: str,
        kind: str = "kernel",
        toolchain_id: str,
        timeout: Optional[float] = None,
        subject: Optional[Subject] = None,
        toolchain: Optional[Toolchain] = None,
        claim_id: Optional[str] = None,
    ):
        if kind not in ("kernel", "model-checker"):
            raise ValueError(f"kind must be 'kernel' or 'model-checker', got {kind!r}")
        provenance = {"subject": subject, "toolchain": toolchain, "claim_id": claim_id}
        supplied = [name for name, value in provenance.items() if value]
        if supplied and len(supplied) != 3:
            missing = sorted(set(provenance) - set(supplied))
            raise ValueError(
                f"receipt schema 2.0.0 provenance is all-or-nothing: got {sorted(supplied)} "
                f"but not {missing}. Supply all three to emit 2.0.0 receipts, or none to emit "
                f"1.0.0 ones — never a receipt that looks attributed and is not"
            )
        self.checker_command = checker_command
        self.checker_name = checker_name
        self.checker_version = checker_version
        self.kind = kind
        self.toolchain_id = toolchain_id
        self.timeout = timeout
        self.subject = subject
        self.toolchain = toolchain
        self.claim_id = claim_id
        self.receipt_schema_version = "2.0.0" if supplied else "1.0.0"

    def check(
        self,
        *,
        target_id: str,
        candidate_id: str,
        candidate_file: Union[str, Path],
        obligation_ids: Sequence[str] = (),
        harness: Optional[str] = None,
        bound: Optional[Union[str, float, int]] = None,
        env_assumptions: Optional[str] = None,
        control: Optional[Control] = None,
    ) -> Receipt:
        """Run the checker on ``candidate_file`` and produce a Receipt.

        For a `kind="kernel"` gate, `harness`/`bound`/`env_assumptions`
        must all be omitted (a kernel's verdict is not relative to any
        of those). For a `kind="model-checker"` gate they are all
        required, and are recorded on the receipt so its verdict's
        scope is explicit (ARCHITECTURE.md §4).

        `control` marks this run as a control for another claim (an
        ablation, a mutation, a planted twin) and requires a gate
        configured for 2.0.0 receipts, since 1.0.0 has no field for it.
        """
        candidate_file = Path(candidate_file)

        if self.kind == "kernel":
            if harness is not None or bound is not None or env_assumptions is not None:
                raise ValueError(
                    "a kernel gate does not accept harness/bound/env_assumptions"
                )
        else:
            if not harness or bound is None or not env_assumptions:
                raise ValueError(
                    "a model-checker gate requires harness, bound, and env_assumptions"
                )

        if control is not None and self.receipt_schema_version != "2.0.0":
            raise ValueError(
                "a control receipt requires a gate configured for receipt schema 2.0.0 "
                "(subject + toolchain + claim_id); 1.0.0 has no field to record a control in"
            )

        result = self.checker_command(candidate_file, self.timeout)

        if result.failure_kind is not None:
            # verdict 'error' is in the 1.0.0 enum too (it was always
            # reachable in the schema, just unreachable in code before
            # this gate existed - see maintainers/divergences-from-
            # architecture.md). What 1.0.0 has no field for is the
            # `failure_kind` detail itself, so a 1.0.0 gate still emits
            # a legacy `error`-shaped receipt - never a receiptless
            # exception that strands the queue - it just cannot say
            # *which kind* of tool failure this was; a 2.0.0 gate
            # records the kind on the receipt as before.
            verdict = "error"
        else:
            verdict = "accepted" if result.accepted else "rejected"

        certificate = None
        if self.kind == "kernel" and verdict == "accepted":
            certificate = Certificate(
                checked_file=str(candidate_file), toolchain_id=self.toolchain_id
            )

        ids = tuple(obligation_ids) or (target_id,)
        coverage_by_id = _normalize_coverage(result.obligation_coverage)

        if verdict == "error":
            # The checker produced no verdict, so no obligation was
            # decided. Reporting them as `failed` would be the same
            # category error as reporting the run as `rejected`.
            statuses = {oid: "not-exercised" for oid in ids}
        elif result.obligation_statuses:
            default = "held" if verdict == "accepted" else "failed"
            statuses = {oid: result.obligation_statuses.get(oid, default) for oid in ids}
        else:
            # A plain whole-file kernel/model-checker run only tells us
            # the file-level verdict; every requested obligation is
            # reduced to that same held/failed status. Distinguishing
            # "vacuous" or "not-exercised" at the obligation level
            # requires a checker that reports per-obligation detail
            # (via `obligation_statuses`) — the audit layer (audit.py)
            # is where vacuity is actually detected in this reference
            # implementation.
            status = "held" if verdict == "accepted" else "failed"
            statuses = {oid: status for oid in ids}

        obligations = tuple(
            Obligation(
                id=oid,
                status=statuses[oid],
                coverage=coverage_by_id.get(oid) if self.receipt_schema_version == "2.0.0" else None,
            )
            for oid in ids
        )

        return Receipt(
            target_id=target_id,
            candidate_id=candidate_id,
            checker=Checker(kind=self.kind, name=self.checker_name, version=self.checker_version),
            verdict=verdict,
            certificate=certificate,
            harness=harness if self.kind == "model-checker" else None,
            bound=bound if self.kind == "model-checker" else None,
            env_assumptions=env_assumptions if self.kind == "model-checker" else None,
            obligations=obligations,
            produced_at=now_iso(),
            schema_version=self.receipt_schema_version,
            claim_id=self.claim_id,
            subject=self.subject,
            toolchain=self.toolchain,
            failure_kind=result.failure_kind if self.receipt_schema_version == "2.0.0" else None,
            control=control,
        )


def _normalize_coverage(reported: Optional[Mapping[str, object]]) -> dict:
    """Accept either `Coverage` values or plain dicts of the same shape,
    and reject anything else loudly — a coverage record the gate cannot
    read is not silently treated as "no coverage measured", because those
    two say opposite things about the evidence."""
    if not reported:
        return {}
    normalized = {}
    for obligation_id, value in reported.items():
        if isinstance(value, Coverage):
            normalized[obligation_id] = value
        elif isinstance(value, dict):
            normalized[obligation_id] = Coverage.from_dict(value)
        else:
            raise ValueError(
                f"obligation_coverage[{obligation_id!r}] must be a Coverage or a dict of the "
                f"same shape, got {type(value).__name__}"
            )
    return normalized
