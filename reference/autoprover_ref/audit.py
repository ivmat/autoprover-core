"""The semantic audit layer (ARCHITECTURE.md §5).

A proof checker answers exactly one question: does this proof term
establish this formal statement, given these definitions? It answers
nothing about whether that statement is the theorem anyone wanted, or
whether it says anything at all. This module implements six checks that
catch what the kernel structurally cannot see:

  (a) vacuity  — does the target's provenance ship evidence that its
      declared preconditions can actually fire, or could the "theorem"
      hold for the trivial reason that its hypothesis is never
      satisfiable?
  (b) unexercised hypothesis — for a target checked by enumeration
      (a bounded model checker), did any enumerated state actually
      VIOLATE the obligation's precondition? A precondition that every
      explored state satisfies never pruned anything, so the implication
      was never exercised as an implication. This is the mirror image of
      (a) and a distinct failure mode: (a) asks whether the hypothesis
      ever fired, (b) asks whether it ever failed to.
  (c) name/content mismatch — do the claim keywords a target's name or
      changelog entry would use show up reflected in the formal
      statement text, or does the name overclaim what was actually
      proved?
  (d) scope narrower than claimed — if the target's provenance declares a
      claimed scope that asserts generality ("for all n", "arbitrary
      graph"), does the formal statement text show structural evidence
      of being restricted to a fixed instance instead (a quantified
      variable pinned to one concrete numeral, a named single-instance
      carrier standing in for "arbitrary X", or no quantified-variable
      binder at all)?
  (e) missing control — for a claim presented as CONTRACT-grade, does the
      evidence set gathered under its claim_id contain a control receipt
      that was watched to fail: a mutation whose prediction was "red" and
      whose measured observation matched? A check nobody has ever seen
      fail is untested. A postcondition that is too weak to falsify, or
      an oracle wired to a value it always computes correctly, passes
      every ordinary run indistinguishably from a real one; only a
      deliberately-broken run tells the two apart.
  (f) obligation status — does the CURRENT candidate's receipt report
      every obligation as `held`, or does the checker's own per-obligation
      bucket say one was `vacuous` or `not-exercised`? A run can be
      accepted overall and still say, obligation by obligation, that
      nothing was established there; the accepted set must not be
      reachable from such a receipt. Unlike its five neighbours this one
      is not a heuristic — it reads what the checker itself reported.

Checks (a)-(e) are HONEST HEURISTICS, not sound verification. They
operate on provenance metadata, statement *text*, reported enumeration
counts, and the shape of an evidence set, not on formal semantics: "no
non-vacuity witness recorded" proves the provenance record didn't
demonstrate satisfiability, not that the precondition truly is
unsatisfiable; "no explored state violated this precondition" is a fact
about the states one run happened to enumerate, not a proof that the
hypothesis is redundant; "no expected keyword found in the statement
text" is a lexical check, not a proof that the name overclaims; "no
quantified binder found" is a syntactic pattern match, not a proof the
statement is actually about a single instance; "no observed-red mutation
control in this evidence set" says the set on offer contains no such
artifact, not that the oracle is in fact unfalsifiable. Check (f) is the
exception: it reports the checker's own per-obligation statuses, so it is
as sound as the receipt it reads and no sounder. A
target can pass all six checks and
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
from typing import Optional, Sequence

from .receipts import AuditVerdict, Receipt, now_iso

__all__ = [
    "CLAIM_GRADES",
    "ObligationHypothesisEvidence",
    "TargetProvenance",
    "check_vacuity",
    "check_obligation_statuses",
    "check_unexercised_hypothesis",
    "check_name_content",
    "check_scope",
    "check_controls",
    "run_audit",
]

# What a claim is being presented AS, which decides how much evidence it
# owes. A "contract" claim is one another party is expected to rely on;
# a "probe" is exploratory — a measurement taken to learn something, not
# a promise. Grading is a declaration made by target selection, not
# something this module infers: nothing in a statement's text says
# whether anyone is meant to depend on it.
CLAIM_GRADES = ("contract", "probe")


@dataclass(frozen=True)
class ObligationHypothesisEvidence:
    """What an enumerating checker (a bounded model checker) reports back
    about ONE obligation's precondition, so the audit layer can ask
    whether the implication was ever exercised.

    `states_satisfying` and `states_violating` are counts over exactly the
    states that run enumerated — not over the system's reachable set,
    unless `exhaustive` is True. `has_precondition` distinguishes "this
    obligation is an implication whose guard we counted" from "this
    obligation is unconditional, so there is no hypothesis to exercise";
    an unconditional obligation is never flagged by
    `check_unexercised_hypothesis`, because it makes no conditional claim
    to begin with.

    `model_checker.hypothesis_coverage` builds these records from an
    `ExplorationResult`; nothing in this module computes them, and nothing
    in this module re-runs the checker.
    """

    obligation_id: str
    has_precondition: bool
    states_satisfying: int
    states_violating: int
    exhaustive: bool


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

    `obligation_evidence`, if present, is what an enumerating checker
    reported about each obligation's precondition (see
    `ObligationHypothesisEvidence`). It is only available for targets
    discharged by enumeration; a target checked by a proof kernel has no
    enumerated state space and therefore records none, which makes
    `check_unexercised_hypothesis` abstain rather than guess.

    `claim_id` is the key this target's evidence is gathered under (the
    same key receipt schema 2.0.0 records), and `claim_grade` is what the
    claim is being presented AS: "contract" (another party is expected to
    rely on it) or "probe" (exploratory — a measurement, not a promise).
    Both are declarations made by target selection; nothing in a
    statement's text says whether anyone is meant to depend on it, so
    this module never infers them. Leaving `claim_grade` unset means "no
    grade was declared", and `check_controls` abstains — a target nobody
    called contract-grade is not held to contract-grade evidence. A
    contract-grade claim MUST carry a claim_id: without one there is no
    key to gather its evidence under, and a contract claim whose evidence
    cannot be located would silently escape the check rather than fail
    it.
    """

    source: str
    statement_text: str
    claim_keywords: tuple[str, ...] = ()
    preconditions: tuple[str, ...] = ()
    non_vacuity_witness: str | None = None
    claimed_scope: str | None = None
    obligation_evidence: tuple[ObligationHypothesisEvidence, ...] = ()
    claim_id: str | None = None
    claim_grade: str | None = None

    def __post_init__(self) -> None:
        if self.claim_grade is not None and self.claim_grade not in CLAIM_GRADES:
            raise ValueError(
                f"claim_grade must be null (undeclared) or one of {CLAIM_GRADES}, "
                f"got {self.claim_grade!r}"
            )
        if self.claim_grade == "contract" and not self.claim_id:
            raise ValueError(
                "a contract-grade claim requires a claim_id: it is the key its evidence "
                "(including its controls) is gathered under, and a contract claim whose "
                "evidence cannot be located would escape the control check rather than fail it"
            )


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


def check_unexercised_hypothesis(provenance: TargetProvenance) -> tuple[bool, dict]:
    """Heuristic (b). For a target discharged by enumeration, flags an
    obligation whose precondition NO enumerated state violated: the guard
    pruned nothing, so the implication `pre(s) -> prop(s)` was never
    exercised as an implication — every state the checker looked at went
    down the `pre` branch. What was actually established over the explored
    set is the unconditional property; the stated hypothesis is untested,
    and a hypothesis that is accidentally always true (a typo, a
    tautological guard, a fixture too narrow to generate a violating
    state) is indistinguishable from a genuine one at the verdict level.
    This is the "unexercised precondition" pattern (cf. formal-verification
    review practice), and it is a DIFFERENT risk from the one
    `check_vacuity` covers: that check asks whether the hypothesis can
    ever fire at all, this one asks whether it ever failed to.

    Three deliberate non-flags, each an abstain rather than a guess:

      * no `obligation_evidence` recorded — nothing was enumerated (a
        proof-kernel target, say), so there are no counts to judge;
      * an obligation with `has_precondition=False` — an unconditional
        obligation makes no conditional claim, so it has no hypothesis to
        exercise;
      * an obligation whose precondition held on ZERO enumerated states —
        that is the vacuity/not-exercised case, already reported per
        obligation by the checker itself (`model_checker.check_obligations`
        returns `vacuous` or `not-exercised` there) and by `check_vacuity`
        upstream. Reporting it again here would flatten two distinct
        findings into one ambiguous verdict.

    `exhaustive` is carried into the details rather than gating the flag,
    because it changes what the finding MEANS, not whether there is one:
    on an exhaustive exploration "no state violates this precondition"
    says the hypothesis is redundant over the system's whole reachable
    set; on a bound-truncated one it says only that this run never
    enumerated a violating state. Either way the implication went
    unexercised in the evidence on offer.
    """
    evidence = provenance.obligation_evidence
    if not evidence:
        return True, {
            "check": "unexercised_hypothesis",
            "judged": False,
            "reason": "no enumerated-obligation evidence recorded",
        }

    unexercised: list[dict] = []
    judged: list[str] = []
    skipped: list[dict] = []
    for record in evidence:
        if not record.has_precondition:
            skipped.append({
                "obligation_id": record.obligation_id,
                "reason": "unconditional obligation (no hypothesis to exercise)",
            })
            continue
        if record.states_satisfying == 0:
            skipped.append({
                "obligation_id": record.obligation_id,
                "reason": "precondition never fired; reported as vacuous/not-exercised, "
                          "not as an unexercised hypothesis",
            })
            continue
        judged.append(record.obligation_id)
        if record.states_violating == 0:
            unexercised.append({
                "obligation_id": record.obligation_id,
                "states_satisfying_precondition": record.states_satisfying,
                "states_violating_precondition": 0,
                "exploration_exhaustive": record.exhaustive,
            })

    if unexercised:
        return False, {
            "check": "unexercised_hypothesis",
            "judged": True,
            "obligations_judged": judged,
            "unexercised": unexercised,
            "skipped": skipped,
        }
    return True, {
        "check": "unexercised_hypothesis",
        "judged": bool(judged),
        "obligations_judged": judged,
        "skipped": skipped,
    }


def check_obligation_statuses(receipt: Optional[Receipt]) -> tuple[bool, dict]:
    """Heuristic (f) — and the one check in this module that is not a
    heuristic at all. It reads what the checker itself said, per
    obligation, on the receipt for THIS candidate: an obligation reported
    `vacuous` (its precondition held in no state of an exhaustively
    explored space) or `not-exercised` (the same, on a bound-truncated
    one) was never established, and the run's overall verdict does not
    overrule the checker's own account of it.

    This closes the gap between a checker's obligation bucket and the
    ratchet. `model_checker.model_checker_command` deliberately reports
    an overall `accepted` for a run in which some obligation came back
    vacuous — collapsing those into an overall failure would defeat the
    point of surfacing them as distinct statuses — and leaves them
    "visible per-obligation for a caller to act on directly". THIS is
    that caller. Without this check, "accepted receipt + vacuous
    obligation + audit pass" is a reachable path into the accepted set,
    which is precisely the failure mode ARCHITECTURE.md §5 says the audit
    layer exists to stop.

    Abstains (passes, judged=False) when no receipt is supplied: this
    module never judges evidence it was not shown, exactly as
    `check_controls` abstains on an unsupplied receipt set.

    Scope limit, stated rather than implied: an obligation reported
    `failed` on a receipt whose overall verdict is `accepted` is a
    checker self-contradiction, not a vacuity finding. It is recorded in
    the details under `contradictory` so it cannot pass unseen, but this
    check does not convert it into a vacuity verdict — the audit's
    closed failure-reason vocabulary has no code for it, and reusing a
    vacuity code for a different finding is the kind of category collapse
    this package exists to avoid.
    """
    if receipt is None:
        return True, {
            "check": "obligation_status",
            "judged": False,
            "reason": "no kernel receipt supplied to judge obligation statuses",
        }

    statuses = {o.id: o.status for o in receipt.obligations}
    unestablished = [
        {"obligation_id": o.id, "status": o.status}
        for o in receipt.obligations
        if o.status in ("vacuous", "not-exercised")
    ]
    contradictory = [
        {"obligation_id": o.id, "status": o.status}
        for o in receipt.obligations
        if o.status == "failed" and receipt.verdict == "accepted"
    ]

    details = {
        "check": "obligation_status",
        "judged": True,
        "receipt_verdict": receipt.verdict,
        "obligation_statuses": statuses,
        "contradictory": contradictory,
    }
    if unestablished:
        details["unestablished"] = unestablished
        return False, details
    return True, details


def check_name_content(provenance: TargetProvenance) -> tuple[bool, dict]:
    """Heuristic (c). For each declared claim keyword with a judgeable
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
    """Heuristic (d). Flags a target whose `claimed_scope` asserts
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


def check_controls(
    provenance: TargetProvenance, receipts: Optional[Sequence[Receipt]] = None
) -> tuple[bool, dict]:
    """Heuristic (e). For a claim presented as CONTRACT-grade, flags an
    evidence set that contains no control receipt anyone watched fail:
    no receipt whose `control` block names this claim, is of kind
    "mutation", predicted "red", and observed what it predicted.

    A check nobody has ever seen fail is untested. An oracle that reads
    the value it is supposed to be checking, a postcondition too weak to
    exclude anything, a fixture that never reaches the interesting path —
    all of them pass every ordinary run indistinguishably from a real
    proof. The only artifact that separates them is a deliberately-broken
    run in which the check DID fire: a mutation whose prediction was red
    and whose measurement was red.

    Why kind "mutation" specifically, and why expectation "red": those
    two together are what demonstrate FALSIFIABILITY of this claim's
    oracle. An ablation attests something adjacent but different (that a
    precondition is load-bearing), and a control predicted green — the
    revert leg of a mutation experiment, say — confirms the experiment
    was reversible without ever showing the oracle can fail. Accepting a
    green-predicted control here would let a claim satisfy "somebody
    watched this fail" with evidence that nobody ever did. Controls of
    other kinds and other predictions are still reported in the details:
    they are evidence, they are just not evidence OF THIS.

    Three deliberate abstains, each a pass that is not a judgment:

      * `claim_grade` unset — nobody declared this a contract, and a
        target not presented as one is not held to contract-grade
        evidence;
      * `claim_grade == "probe"` — an exploratory measurement makes no
        promise for anyone to rely on;
      * `receipts is None` — no evidence set was supplied at all, so
        there is nothing to look in. Note the distinction from an EMPTY
        set, which is supplied evidence that happens to contain no
        control, and does fail: "I have no store to search" and "I
        searched and there is nothing" are different statements
        (INTERFACES.md property 3), so they get different encodings.

    Like every check in this module this is a statement about the
    evidence on offer, not about the world: "no observed-red mutation
    control in this set" does not prove the oracle is unfalsifiable, only
    that nothing here shows it isn't.
    """
    if provenance.claim_grade != "contract":
        return True, {
            "check": "controls",
            "judged": False,
            "reason": (
                "no claim_grade declared" if provenance.claim_grade is None
                else f"claim_grade is {provenance.claim_grade!r}, not 'contract'"
            ),
        }

    if receipts is None:
        return True, {
            "check": "controls",
            "judged": False,
            "claim_id": provenance.claim_id,
            "reason": "no receipt set supplied to search for controls",
        }

    claim_id = provenance.claim_id
    controls = [r.control for r in receipts if r.control is not None and r.control.of_claim == claim_id]
    qualifying = [
        c for c in controls
        if c.kind == "mutation" and c.expectation == "red" and c.passed()
    ]

    other_controls = [
        {
            "kind": c.kind,
            "expectation": c.expectation,
            "observed": c.observed,
            "behaved_as_predicted": c.passed(),
        }
        for c in controls if c not in qualifying
    ]

    if qualifying:
        return True, {
            "check": "controls",
            "judged": True,
            "claim_id": claim_id,
            "observed_red_mutation_controls": len(qualifying),
            "other_controls": other_controls,
        }

    return False, {
        "check": "controls",
        "judged": True,
        "claim_id": claim_id,
        "receipts_searched": len(receipts),
        "controls_found": len(controls),
        "observed_red_mutation_controls": 0,
        "other_controls": other_controls,
        "required": (
            "at least one control receipt of kind 'mutation' with expectation 'red' whose "
            "observation matched — a check nobody watched fail is untested"
        ),
    }


def run_audit(
    target_id: str,
    candidate_id: str,
    provenance: TargetProvenance,
    receipts: Optional[Sequence[Receipt]] = None,
    *,
    receipt: Optional[Receipt] = None,
) -> AuditVerdict:
    """Run all six structural checks in order and produce a single
    structured AuditVerdict. The order is vacuity, then obligation
    statuses, then unexercised hypothesis, then name/content, then scope,
    then controls, and the first failing check short-circuits and is
    reported — never multiple reasons flattened into one ambiguous
    verdict.

    Note the two receipt parameters, which are different things.
    `receipt` (keyword-only) is the CURRENT candidate's kernel receipt —
    the artifact this audit is about, whose per-obligation statuses
    `check_obligation_statuses` reads. `receipts` is the evidence SET
    gathered under this claim across many runs, which `check_controls`
    searches. Both default to None and both make their check abstain
    rather than judge evidence it was never shown.

    Why that order: the two hypothesis checks come first because they ask
    whether the claim has any content at all, and a claim that never
    fires makes the name/content and scope questions moot. Between them,
    vacuity comes first because "the hypothesis can never hold" is the
    more basic failure than "the hypothesis never failed to hold": a
    target with no non-vacuity witness has nothing for the enumeration
    counts to be about. Controls come LAST because they are a question
    about the evidence SET, not about this target's statement: asking
    "has anyone watched this oracle fail" is only worth answering once
    the statement itself has survived every check of what it says. A
    target that overclaims in its name should be reported as
    overclaiming, not as short of controls.

    `receipts` is the evidence set gathered under this claim, which only
    the caller can supply — this module owns no store. Passing None (the
    default) makes `check_controls` abstain; see its docstring for why
    that differs from passing an empty set.
    """
    if receipt is not None and (
        receipt.target_id != target_id or receipt.candidate_id != candidate_id
    ):
        raise ValueError(
            f"the receipt handed to run_audit is about "
            f"({receipt.target_id!r}, {receipt.candidate_id!r}), but the audit is of "
            f"({target_id!r}, {candidate_id!r}) — auditing one candidate against another's "
            f"receipt is a wiring error, and passing it would be a verdict about nothing"
        )

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

    obligation_ok, obligation_details = check_obligation_statuses(receipt)
    if not obligation_ok:
        return AuditVerdict(
            target_id=target_id,
            candidate_id=candidate_id,
            verdict="fail",
            failure_reason="vacuous-precondition",
            details=obligation_details,
            produced_at=now_iso(),
        )

    unexercised_ok, unexercised_details = check_unexercised_hypothesis(provenance)
    if not unexercised_ok:
        return AuditVerdict(
            target_id=target_id,
            candidate_id=candidate_id,
            verdict="fail",
            failure_reason="unexercised-hypothesis",
            details=unexercised_details,
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

    controls_ok, controls_details = check_controls(provenance, receipts)
    if not controls_ok:
        return AuditVerdict(
            target_id=target_id,
            candidate_id=candidate_id,
            verdict="fail",
            failure_reason="missing-control",
            details=controls_details,
            produced_at=now_iso(),
        )

    return AuditVerdict(
        target_id=target_id,
        candidate_id=candidate_id,
        verdict="pass",
        failure_reason=None,
        details={
            "checks_run": [
                "vacuity", "obligation_status", "unexercised_hypothesis", "name_content",
                "scope", "controls",
            ],
            "vacuity": vacuity_details,
            "obligation_status": obligation_details,
            "unexercised_hypothesis": unexercised_details,
            "name_content": name_content_details,
            "scope": scope_details,
            "controls": controls_details,
        },
        produced_at=now_iso(),
    )
