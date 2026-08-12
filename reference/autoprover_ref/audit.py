"""The semantic audit layer (ARCHITECTURE.md §5).

A proof checker answers exactly one question: does this proof term
establish this formal statement, given these definitions? It answers
nothing about whether that statement is the theorem anyone wanted, or
whether it says anything at all. This module implements three structural
checks that catch what the kernel structurally cannot see:

  (a) vacuity  — does the target's provenance ship evidence that its
      declared preconditions can actually fire, or could the "theorem"
      hold for the trivial reason that its hypothesis is never
      satisfiable?
  (b) name/content mismatch — do the claim keywords a target's name or
      changelog entry would use show up reflected in the formal
      statement text, or does the name overclaim what was actually
      proved?
  (c) scope narrower than claimed — if the target's provenance declares a
      claimed scope that asserts generality ("for all n", "arbitrary
      graph"), does the formal statement text show structural evidence
      of being restricted to a fixed instance instead (a quantified
      variable pinned to one concrete numeral, a named single-instance
      carrier standing in for "arbitrary X", or no quantified-variable
      binder at all)?

All three checks are HONEST HEURISTICS, not sound verification. They
operate on provenance metadata and statement *text*, not on formal
semantics: "no non-vacuity witness recorded" proves the provenance record
didn't demonstrate satisfiability, not that the precondition truly is
unsatisfiable; "no expected keyword found in the statement text" is a
lexical check, not a proof that the name overclaims; "no quantified
binder found" is a syntactic pattern match, not a proof the statement is
actually about a single instance. A target can pass all three checks and
still be wrong in a way a human would catch immediately, and a target can
fail one on a false positive (an unusual but legitimate phrasing). This is
exactly the trade-off ARCHITECTURE.md §7 draws between a kernel verdict
(machine-checkable, independently re-derivable) and an audit verdict
(machine-readable, a judgment, re-running it can legitimately produce a
different answer). Nothing in this module re-derives the kernel's
verdict; it only ever adds a second, different, structured judgment on
top of it.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from .receipts import AuditVerdict, now_iso

__all__ = [
    "TargetProvenance",
    "check_vacuity",
    "check_name_content",
    "check_scope",
    "run_audit",
]


@dataclass(frozen=True)
class TargetProvenance:
    """What target selection (ARCHITECTURE.md §1) is expected to hand
    the audit layer: the claim the target is allowed to make, and (per
    the vacuity discipline) a record of whether any declared
    precondition has a witness showing it can actually fire.

    `claim_keywords` are the words a target's name/changelog entry would
    use to describe it to a human (e.g. a target named `sorted_output`
    might declare `claim_keywords=("sorted",)`). `statement_text` is the
    formal statement rendered as text, which the name/content check
    scans for evidence the claim keyword is actually reflected.
    `preconditions` names any declared hypotheses a "genuinely
    interesting" instance is expected to satisfy; `non_vacuity_witness`,
    if present, is a human-or-tool-readable record of a witness showing
    at least one such instance exists (e.g. "decide-checked instance:
    n = 3" or a reference to a satisfiability example) — see
    `reference/examples/` for a worked pair of targets, one with and one
    without such a witness.

    `claimed_scope`, if present, is free text describing the breadth of
    instance the target's name/changelog entry would claim to cover (e.g.
    "for all n : Nat" or "arbitrary finite graph"). It is what
    `check_scope` compares against `statement_text`'s structure. Leaving
    it unset means "no scope claim was declared to check against" — see
    `check_scope`'s docstring for why that makes the check abstain rather
    than guess.
    """

    source: str
    statement_text: str
    claim_keywords: tuple[str, ...] = ()
    preconditions: tuple[str, ...] = ()
    non_vacuity_witness: str | None = None
    claimed_scope: str | None = None


# A small, explicit lexicon mapping a claim keyword to substrings whose
# presence in the statement text would count as "this claim is at least
# lexically reflected". A keyword with an empty tuple is one the
# heuristic declines to judge at all (too vague to check by text alone,
# e.g. "correct") — the check *abstains* on it rather than treating
# absence-of-evidence as a pass. Extending this lexicon is exactly the
# kind of ordinary, contributable engineering ARCHITECTURE.md/
# INTERFACES.md describe; it is intentionally small here, not exhaustive.
CLAIM_KEYWORD_SIGNALS: dict[str, tuple[str, ...]] = {
    "sorted": ("sorted", "≤", "<=", "monotone", "sortedlist"),
    "correct": (),
    "terminates": ("terminates", "halts", "decreasing", "wellfounded", "well-founded"),
    "unique": ("unique", "injective", "="),
    "commutative": ("comm", "="),
    "injective": ("injective", "injectiv"),
    "surjective": ("surjective", "surject"),
    "safe": ("safe", "invariant"),
    "deadlock-free": ("deadlock",),
    "consistent": ("consistent", "consisten"),
}


def check_vacuity(provenance: TargetProvenance) -> tuple[bool, dict]:
    """Heuristic (a). Flags a target that declares preconditions but
    ships no non-vacuity witness for them. This checks provenance
    *completeness* — a declared precondition without a recorded witness
    — it does not itself decide satisfiability; a witness is exactly the
    artifact ARCHITECTURE.md §5 calls for ("the precondition is
    satisfiable, the interesting case is actually exercised").
    """
    if provenance.preconditions and not provenance.non_vacuity_witness:
        return False, {
            "check": "vacuity",
            "missing_witness_for": list(provenance.preconditions),
        }
    return True, {"check": "vacuity", "preconditions_checked": list(provenance.preconditions)}


def check_name_content(provenance: TargetProvenance) -> tuple[bool, dict]:
    """Heuristic (b). For each declared claim keyword with a judgeable
    entry in `CLAIM_KEYWORD_SIGNALS`, flags a mismatch if none of its
    expected signal substrings appear (case-insensitively) in the
    statement text. Keywords not in the lexicon are skipped (the
    heuristic abstains rather than guessing).
    """
    lowered = provenance.statement_text.lower()
    mismatches = []
    judged = []
    for keyword in provenance.claim_keywords:
        signals = CLAIM_KEYWORD_SIGNALS.get(keyword.lower())
        if not signals:
            continue
        judged.append(keyword)
        if not any(signal.lower() in lowered for signal in signals):
            mismatches.append({"claim_keyword": keyword, "expected_any_of": list(signals)})
    if mismatches:
        return False, {"check": "name_content", "mismatches": mismatches, "keywords_judged": judged}
    return True, {"check": "name_content", "keywords_judged": judged}


# Signals that a target's declared `claimed_scope` asserts generality —
# "this holds for every instance", not "this holds for the one instance
# named below". A `claimed_scope` that doesn't contain any of these is
# not itself a universality claim, so there is nothing for this check to
# compare the statement's narrowness against.
UNIVERSAL_SCOPE_SIGNALS: tuple[str, ...] = (
    "forall", "for all", "for every", "for any", "arbitrary", "every ",
    "any ", "all ",
)

# A Lean-style quantified-variable binder, e.g. "(n : Nat)" or
# "(l : List Nat)" — structural evidence the statement is actually stated
# about a variable, not a fixed instance. Intentionally narrow (matches
# this project's corpus style, see corpus/); a statement written in a
# different surface syntax may need a different pattern, which is exactly
# the kind of ordinary, contributable engineering the other two checks in
# this module already describe.
_BINDER_PATTERN = re.compile(r"\(\s*[a-zA-Z_][a-zA-Z0-9_]*\s*:\s*[A-Za-z]")

# A would-be-universal variable pinned to one concrete numeral, e.g.
# "n = 5" — structural evidence the statement narrows to a single value
# rather than ranging over all of them.
_FIXED_NUMERAL_PATTERN = re.compile(r"\b[a-zA-Z_][a-zA-Z0-9_]*\s*=\s*\d+\b")

# A small, explicit lexicon of named single-instance carriers that
# sometimes stand in for an "arbitrary graph/group/list" claim. Extending
# this lexicon is exactly the kind of ordinary, contributable engineering
# CLAIM_KEYWORD_SIGNALS above already describes; it is intentionally
# small here, not exhaustive.
_SINGLE_CARRIER_SIGNALS: tuple[str, ...] = (
    "k4", "k3,3", "k5", "petersen graph", "trivial group", "empty graph",
    "singleton list", "the fixed", "the specific", "this particular",
    "one particular",
)


def check_scope(provenance: TargetProvenance) -> tuple[bool, dict]:
    """Heuristic (c). Flags a target whose `claimed_scope` asserts
    generality but whose formal statement text shows structural evidence
    of being restricted to a fixed instance: a would-be-universal
    variable pinned to one concrete numeral, a named single-instance
    carrier standing in for "arbitrary X", or the complete absence of any
    quantified-variable binder despite the claim. This is a STRUCTURAL
    heuristic over statement *text*, not a semantic generality checker —
    it can be fooled by unusual phrasing in either direction, exactly
    like `check_vacuity` and `check_name_content` can.

    If `claimed_scope` is not supplied, or is supplied but does not
    itself contain a recognized universal-scope signal, this check
    ABSTAINS — it returns a pass, mirroring `check_name_content`'s
    abstain-on-unjudgeable-keyword behavior. An abstain here is evidence
    this heuristic had nothing to compare against, never evidence the
    scope is actually fine.
    """
    if not provenance.claimed_scope:
        return True, {"check": "scope", "judged": False, "reason": "no claimed_scope declared"}

    claimed_lowered = provenance.claimed_scope.lower()
    if not any(signal in claimed_lowered for signal in UNIVERSAL_SCOPE_SIGNALS):
        return True, {
            "check": "scope", "judged": False,
            "reason": "claimed_scope does not assert universality/generality",
        }

    statement = provenance.statement_text
    lowered = statement.lower()
    narrowing_evidence: list[dict] = []

    fixed_numeral_match = _FIXED_NUMERAL_PATTERN.search(statement)
    if fixed_numeral_match:
        narrowing_evidence.append({
            "signal": "fixed-numeral-instantiation",
            "match": fixed_numeral_match.group(0),
        })

    matched_carriers = [s for s in _SINGLE_CARRIER_SIGNALS if s in lowered]
    if matched_carriers:
        narrowing_evidence.append({
            "signal": "named-single-carrier",
            "matches": matched_carriers,
        })

    has_binder = _BINDER_PATTERN.search(statement) is not None
    has_inline_universal_signal = any(
        sig in lowered for sig in ("forall", "for all", "∀")
    )
    if not has_binder and not has_inline_universal_signal:
        narrowing_evidence.append({"signal": "no-quantified-variable-binder"})

    if narrowing_evidence:
        return False, {
            "check": "scope",
            "judged": True,
            "claimed_scope": provenance.claimed_scope,
            "narrowing_evidence": narrowing_evidence,
        }
    return True, {
        "check": "scope", "judged": True, "claimed_scope": provenance.claimed_scope,
    }


def run_audit(target_id: str, candidate_id: str, provenance: TargetProvenance) -> AuditVerdict:
    """Run all three structural checks in order and produce a single
    structured AuditVerdict. Vacuity is checked first, then name/content,
    then scope: a vacuous precondition makes the name/content and scope
    questions moot (there is no "content" or "scope" worth judging if the
    theorem never really fires), so the first failing check
    short-circuits and is reported — never multiple reasons flattened
    into one ambiguous verdict.
    """
    vacuity_ok, vacuity_details = check_vacuity(provenance)
    if not vacuity_ok:
        return AuditVerdict(
            target_id=target_id,
            candidate_id=candidate_id,
            verdict="fail",
            failure_reason="vacuous-precondition",
            details=vacuity_details,
            produced_at=now_iso(),
        )

    name_content_ok, name_content_details = check_name_content(provenance)
    if not name_content_ok:
        return AuditVerdict(
            target_id=target_id,
            candidate_id=candidate_id,
            verdict="fail",
            failure_reason="name-content-mismatch",
            details=name_content_details,
            produced_at=now_iso(),
        )

    scope_ok, scope_details = check_scope(provenance)
    if not scope_ok:
        return AuditVerdict(
            target_id=target_id,
            candidate_id=candidate_id,
            verdict="fail",
            failure_reason="scope-narrower-than-claimed",
            details=scope_details,
            produced_at=now_iso(),
        )

    return AuditVerdict(
        target_id=target_id,
        candidate_id=candidate_id,
        verdict="pass",
        failure_reason=None,
        details={
            "checks_run": ["vacuity", "name_content", "scope"],
            "vacuity": vacuity_details,
            "name_content": name_content_details,
            "scope": scope_details,
        },
        produced_at=now_iso(),
    )
