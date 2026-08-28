"""Tests for audit.py: catches a synthetic vacuously-true target, a
synthetic unexercised hypothesis, a synthetic overclaiming name, a
synthetic narrowed-scope target, and a synthetic contract-grade claim
with no control anyone watched fail - all on pure Python text/metadata,
reported counts and receipt shapes; no Lean, no kernel gate needed. See
reference/examples/ for a Lean-backed worked version of the vacuity
case."""

from __future__ import annotations

import unittest

from autoprover_ref.audit import (
    ObligationHypothesisEvidence,
    TargetProvenance,
    check_controls,
    check_scope,
    check_unexercised_hypothesis,
    run_audit,
)
from autoprover_ref.receipts import (
    Checker,
    Control,
    Obligation,
    Receipt,
    Subject,
    Tool,
    Toolchain,
    now_iso,
)


def evidence_receipt(claim_id="claim-1", control=None, target_id="t") -> Receipt:
    """A minimal 2.0.0 model-checker receipt, optionally a control."""
    went_red = bool(control) and control.observed == "red"
    return Receipt(
        target_id=target_id,
        candidate_id="cand1",
        checker=Checker(kind="model-checker", name="checker-x", version="0.1.0"),
        verdict="rejected" if went_red else "accepted",
        certificate=None,
        harness="harness_x",
        bound=8,
        env_assumptions="synthetic",
        obligations=(Obligation(id=target_id, status="failed" if went_red else "held"),),
        produced_at=now_iso(),
        claim_id=claim_id,
        subject=Subject(repo="example/subject", commit="0" * 40, unit=None),
        toolchain=Toolchain(
            tool=Tool(name="checker-x", commit_or_version="0" * 40),
            dependencies=(), flags=(), features=None,
        ),
        control=control,
    )


class VacuityCheckTests(unittest.TestCase):
    def test_flags_vacuous_precondition_without_witness(self):
        # "if a list has negative length then it is sorted" - the
        # precondition is unsatisfiable, so the "theorem" is vacuously
        # true, and no witness is recorded to show otherwise.
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (l : List Nat), length l < 0 -> Sorted l",
            claim_keywords=(),
            preconditions=("length l < 0",),
            non_vacuity_witness=None,
        )
        verdict = run_audit("vacuous_target", "cand1", provenance)
        self.assertEqual(verdict.verdict, "fail")
        self.assertEqual(verdict.failure_reason, "vacuous-precondition")
        self.assertIn("missing_witness_for", verdict.details)

    def test_passes_when_witness_is_recorded(self):
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (l : List Nat), 0 < length l -> length l >= 1",
            claim_keywords=(),
            preconditions=("0 < length l",),
            non_vacuity_witness="decide-checked instance: l = [1]",
        )
        verdict = run_audit("non_vacuous_target", "cand1", provenance)
        self.assertEqual(verdict.verdict, "pass")
        self.assertIsNone(verdict.failure_reason)

    def test_passes_when_no_preconditions_declared(self):
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (n : Nat), n + 0 = n",
            claim_keywords=(),
            preconditions=(),
            non_vacuity_witness=None,
        )
        verdict = run_audit("unconditional_target", "cand1", provenance)
        self.assertEqual(verdict.verdict, "pass")


class UnexercisedHypothesisTests(unittest.TestCase):
    """The mirror image of the vacuity check: the hypothesis fires, but
    nothing the checker enumerated ever failed to satisfy it, so the
    implication was never exercised as an implication."""

    @staticmethod
    def provenance_with(*evidence: ObligationHypothesisEvidence) -> TargetProvenance:
        return TargetProvenance(
            source="synthetic",
            statement_text="forall (s : State), Ready s -> Safe s",
            claim_keywords=(),
            preconditions=("Ready s",),
            non_vacuity_witness="model-checked: 12 states satisfy Ready",
            obligation_evidence=evidence,
        )

    def test_flags_precondition_no_explored_state_violated(self):
        # Every one of the 12 explored states satisfied `Ready`, so the
        # guard pruned nothing: what was checked is the unconditional
        # property, and `Ready` itself was never put to work.
        provenance = self.provenance_with(ObligationHypothesisEvidence(
            obligation_id="ready_implies_safe",
            has_precondition=True,
            states_satisfying=12,
            states_violating=0,
            exhaustive=True,
        ))
        verdict = run_audit("ready_implies_safe", "cand1", provenance)
        self.assertEqual(verdict.verdict, "fail")
        self.assertEqual(verdict.failure_reason, "unexercised-hypothesis")
        flagged = verdict.details["unexercised"]
        self.assertEqual(flagged[0]["obligation_id"], "ready_implies_safe")
        self.assertEqual(flagged[0]["states_violating_precondition"], 0)
        # `exhaustive` changes what the finding means, so it is recorded.
        self.assertTrue(flagged[0]["exploration_exhaustive"])

    def test_flags_on_a_bound_truncated_exploration_too_but_records_it(self):
        provenance = self.provenance_with(ObligationHypothesisEvidence(
            obligation_id="ready_implies_safe",
            has_precondition=True,
            states_satisfying=5,
            states_violating=0,
            exhaustive=False,
        ))
        verdict = run_audit("ready_implies_safe", "cand1", provenance)
        self.assertEqual(verdict.failure_reason, "unexercised-hypothesis")
        self.assertFalse(verdict.details["unexercised"][0]["exploration_exhaustive"])

    def test_passes_when_some_explored_state_violated_the_precondition(self):
        # The guard pruned 7 of 19 states: the implication was genuinely
        # exercised on both sides.
        provenance = self.provenance_with(ObligationHypothesisEvidence(
            obligation_id="ready_implies_safe",
            has_precondition=True,
            states_satisfying=12,
            states_violating=7,
            exhaustive=True,
        ))
        verdict = run_audit("ready_implies_safe", "cand1", provenance)
        self.assertEqual(verdict.verdict, "pass")
        self.assertIsNone(verdict.failure_reason)
        self.assertTrue(verdict.details["unexercised_hypothesis"]["judged"])

    def test_abstains_when_no_obligation_evidence_recorded(self):
        # A proof-kernel target has no enumerated state space at all, so
        # there is nothing to count and nothing to judge.
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (n : Nat), 0 < n -> 1 <= n",
            claim_keywords=(),
            preconditions=("0 < n",),
            non_vacuity_witness="decide-checked instance: n = 1",
        )
        ok, details = check_unexercised_hypothesis(provenance)
        self.assertTrue(ok)
        self.assertFalse(details["judged"])

    def test_unconditional_obligation_is_skipped_not_flagged(self):
        # An obligation with no precondition never claimed to be
        # restricted, so it has no hypothesis to leave unexercised.
        provenance = self.provenance_with(ObligationHypothesisEvidence(
            obligation_id="always_safe",
            has_precondition=False,
            states_satisfying=0,
            states_violating=0,
            exhaustive=True,
        ))
        ok, details = check_unexercised_hypothesis(provenance)
        self.assertTrue(ok)
        self.assertEqual(details["obligations_judged"], [])
        self.assertEqual(details["skipped"][0]["obligation_id"], "always_safe")

    def test_never_fired_precondition_defers_to_the_vacuity_reporting(self):
        # Zero satisfying states is the vacuous/not-exercised case the
        # checker already reports per obligation; flagging it again here
        # would flatten two distinct findings into one verdict.
        provenance = self.provenance_with(ObligationHypothesisEvidence(
            obligation_id="ready_implies_safe",
            has_precondition=True,
            states_satisfying=0,
            states_violating=9,
            exhaustive=True,
        ))
        ok, details = check_unexercised_hypothesis(provenance)
        self.assertTrue(ok)
        self.assertEqual(details["obligations_judged"], [])
        self.assertIn("vacuous/not-exercised", details["skipped"][0]["reason"])

    def test_one_flagged_obligation_among_several_fails_the_audit(self):
        provenance = self.provenance_with(
            ObligationHypothesisEvidence(
                obligation_id="exercised", has_precondition=True,
                states_satisfying=4, states_violating=2, exhaustive=True,
            ),
            ObligationHypothesisEvidence(
                obligation_id="unexercised", has_precondition=True,
                states_satisfying=6, states_violating=0, exhaustive=True,
            ),
        )
        verdict = run_audit("t", "c", provenance)
        self.assertEqual(verdict.failure_reason, "unexercised-hypothesis")
        flagged_ids = [e["obligation_id"] for e in verdict.details["unexercised"]]
        self.assertEqual(flagged_ids, ["unexercised"])
        self.assertEqual(verdict.details["obligations_judged"], ["exercised", "unexercised"])

    def test_vacuity_is_reported_before_unexercised_hypothesis(self):
        # Both checks would fail; the more basic one short-circuits, and
        # exactly one reason is reported.
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (s : State), Ready s -> Safe s",
            claim_keywords=(),
            preconditions=("Ready s",),
            non_vacuity_witness=None,
            obligation_evidence=(ObligationHypothesisEvidence(
                obligation_id="ready_implies_safe", has_precondition=True,
                states_satisfying=12, states_violating=0, exhaustive=True,
            ),),
        )
        verdict = run_audit("t", "c", provenance)
        self.assertEqual(verdict.failure_reason, "vacuous-precondition")

    def test_unexercised_hypothesis_is_reported_before_name_content(self):
        provenance = TargetProvenance(
            source="synthetic",
            # Would also fail name/content: claims "sorted", states nothing of the kind.
            statement_text="forall (s : State), Ready s -> length (f s) = length s",
            claim_keywords=("sorted",),
            preconditions=("Ready s",),
            non_vacuity_witness="model-checked: 12 states satisfy Ready",
            obligation_evidence=(ObligationHypothesisEvidence(
                obligation_id="ready_implies_safe", has_precondition=True,
                states_satisfying=12, states_violating=0, exhaustive=True,
            ),),
        )
        verdict = run_audit("t", "c", provenance)
        self.assertEqual(verdict.failure_reason, "unexercised-hypothesis")


class NameContentMismatchTests(unittest.TestCase):
    def test_flags_overclaiming_name(self):
        # Named/claimed "sorted", but the statement only constrains length.
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (l : List Nat), length (myFunc l) = length l",
            claim_keywords=("sorted",),
            preconditions=(),
            non_vacuity_witness=None,
        )
        verdict = run_audit("sort_is_correct", "cand1", provenance)
        self.assertEqual(verdict.verdict, "fail")
        self.assertEqual(verdict.failure_reason, "name-content-mismatch")
        mismatches = verdict.details["mismatches"]
        self.assertEqual(mismatches[0]["claim_keyword"], "sorted")

    def test_passes_when_claim_keyword_is_reflected(self):
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (l : List Nat), Sorted (myFunc l)",
            claim_keywords=("sorted",),
            preconditions=(),
            non_vacuity_witness=None,
        )
        verdict = run_audit("sort_is_correct", "cand1", provenance)
        self.assertEqual(verdict.verdict, "pass")

    def test_abstains_on_keyword_not_in_lexicon(self):
        # "correct" is intentionally judgeable=vague -> the heuristic
        # abstains rather than flagging it, and abstaining is not the
        # same as fabricating a pass on the underlying claim.
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (n : Nat), n = n",
            claim_keywords=("correct",),
            preconditions=(),
            non_vacuity_witness=None,
        )
        verdict = run_audit("trivially_correct", "cand1", provenance)
        self.assertEqual(verdict.verdict, "pass")
        self.assertEqual(verdict.details["name_content"]["keywords_judged"], [])
        self.assertEqual(
            verdict.details["checks_run"],
            ["vacuity", "obligation_status", "unexercised_hypothesis", "name_content",
             "scope", "controls"],
        )

    def test_vacuity_checked_before_name_content_short_circuits(self):
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (l : List Nat), False -> Sorted l",
            claim_keywords=("terminates",),  # would also fail name/content
            preconditions=("False",),
            non_vacuity_witness=None,
        )
        verdict = run_audit("t", "c", provenance)
        # Vacuity is reported, not name/content - one clear failure
        # reason, never two flattened together.
        self.assertEqual(verdict.failure_reason, "vacuous-precondition")


class ScopeCheckTests(unittest.TestCase):
    def test_flags_scope_narrowed_to_a_fixed_numeral(self):
        # Claimed as holding for arbitrary n, but the statement pins n
        # to the single concrete value 5.
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="theorem holds_for_a_number (h : n = 5) : n + 0 = n",
            claim_keywords=(),
            preconditions=(),
            non_vacuity_witness=None,
            claimed_scope="for all n : Nat, n + 0 = n",
        )
        verdict = run_audit("holds_for_all_n", "cand1", provenance)
        self.assertEqual(verdict.verdict, "fail")
        self.assertEqual(verdict.failure_reason, "scope-narrower-than-claimed")
        evidence_signals = {e["signal"] for e in verdict.details["narrowing_evidence"]}
        self.assertIn("fixed-numeral-instantiation", evidence_signals)

    def test_flags_scope_narrowed_to_a_named_single_carrier(self):
        # Claimed as holding for an arbitrary finite graph, but the
        # statement is only about one specific, named graph (K4) and has
        # no quantified variable binder at all.
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="theorem k4_is_planar : Planar K4",
            claim_keywords=(),
            preconditions=(),
            non_vacuity_witness=None,
            claimed_scope="for every finite graph G, this graph family is planar",
        )
        verdict = run_audit("planarity_holds", "cand1", provenance)
        self.assertEqual(verdict.verdict, "fail")
        self.assertEqual(verdict.failure_reason, "scope-narrower-than-claimed")
        evidence_signals = {e["signal"] for e in verdict.details["narrowing_evidence"]}
        self.assertIn("named-single-carrier", evidence_signals)
        self.assertIn("no-quantified-variable-binder", evidence_signals)

    def test_honest_universal_statement_passes(self):
        # Claimed and actually stated over an arbitrary n : Nat, with a
        # real quantified-variable binder and no fixed-instance evidence.
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (n : Nat), n + 0 = n",
            claim_keywords=(),
            preconditions=(),
            non_vacuity_witness=None,
            claimed_scope="for all n : Nat, n + 0 = n",
        )
        verdict = run_audit("holds_for_all_n", "cand1", provenance)
        self.assertEqual(verdict.verdict, "pass")
        self.assertIsNone(verdict.failure_reason)
        self.assertTrue(verdict.details["scope"]["judged"])

    def test_abstains_when_no_claimed_scope_declared(self):
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="theorem k4_is_planar : Planar K4",
            claim_keywords=(),
            preconditions=(),
            non_vacuity_witness=None,
            claimed_scope=None,
        )
        ok, details = check_scope(provenance)
        self.assertTrue(ok)
        self.assertFalse(details["judged"])

    def test_abstains_when_claimed_scope_is_not_itself_universal(self):
        # claimed_scope doesn't assert generality in the first place, so
        # there is nothing to compare the statement's narrowness against.
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="theorem k4_is_planar : Planar K4",
            claim_keywords=(),
            preconditions=(),
            non_vacuity_witness=None,
            claimed_scope="the specific graph K4 is planar",
        )
        ok, details = check_scope(provenance)
        self.assertTrue(ok)
        self.assertFalse(details["judged"])

    def test_scope_checked_after_vacuity_and_name_content(self):
        # A target that fails vacuity should short-circuit before scope
        # is ever judged, even if the scope would also have failed.
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (l : List Nat), False -> Sorted l",
            claim_keywords=(),
            preconditions=("False",),
            non_vacuity_witness=None,
            claimed_scope="for all lists l, this holds",
        )
        verdict = run_audit("t", "c", provenance)
        self.assertEqual(verdict.failure_reason, "vacuous-precondition")


if __name__ == "__main__":
    unittest.main()


class MissingControlTests(unittest.TestCase):
    """A check nobody has watched fail is untested: a contract-grade
    claim must carry a mutation control that was predicted red and
    observed red."""

    @staticmethod
    def contract_provenance(**overrides) -> TargetProvenance:
        fields = dict(
            source="synthetic",
            statement_text="forall (s : State), Ready s -> Safe s",
            claim_keywords=(),
            preconditions=("Ready s",),
            non_vacuity_witness="model-checked: 12 states satisfy Ready",
            claim_id="claim-1",
            claim_grade="contract",
        )
        fields.update(overrides)
        return TargetProvenance(**fields)

    @staticmethod
    def mutation(expectation="red", observed="red", of_claim="claim-1") -> Control:
        return Control(
            kind="mutation", expectation=expectation, observed=observed, of_claim=of_claim,
        )

    def test_passes_when_an_observed_red_mutation_control_is_present(self):
        receipts = [evidence_receipt(), evidence_receipt(control=self.mutation())]
        verdict = run_audit("t", "c", self.contract_provenance(), receipts)
        self.assertEqual(verdict.verdict, "pass")
        self.assertEqual(verdict.details["controls"]["observed_red_mutation_controls"], 1)

    def test_fails_when_the_evidence_set_has_no_control_at_all(self):
        receipts = [evidence_receipt(), evidence_receipt()]
        verdict = run_audit("t", "c", self.contract_provenance(), receipts)
        self.assertEqual(verdict.verdict, "fail")
        self.assertEqual(verdict.failure_reason, "missing-control")
        self.assertEqual(verdict.details["controls_found"], 0)
        self.assertEqual(verdict.details["receipts_searched"], 2)

    def test_fails_on_an_empty_but_supplied_evidence_set(self):
        # Supplied-and-empty is a searched store with nothing in it,
        # which is a finding - unlike "no store supplied", below.
        verdict = run_audit("t", "c", self.contract_provenance(), [])
        self.assertEqual(verdict.failure_reason, "missing-control")

    def test_fails_when_the_mutation_control_did_not_behave_as_predicted(self):
        # Predicted red, came back green: the oracle did NOT catch the
        # planted defect. That is the opposite of reassurance.
        receipts = [evidence_receipt(control=self.mutation(observed="green"))]
        verdict = run_audit("t", "c", self.contract_provenance(), receipts)
        self.assertEqual(verdict.failure_reason, "missing-control")
        [other] = verdict.details["other_controls"]
        self.assertFalse(other["behaved_as_predicted"])

    def test_fails_when_only_an_ablation_control_is_present(self):
        # An ablation attests something adjacent (that a precondition is
        # load-bearing), not that this claim's oracle can fail.
        ablation = Control(
            kind="ablation", expectation="red", observed="red", of_claim="claim-1",
        )
        verdict = run_audit(
            "t", "c", self.contract_provenance(), [evidence_receipt(control=ablation)]
        )
        self.assertEqual(verdict.failure_reason, "missing-control")
        self.assertEqual(verdict.details["other_controls"][0]["kind"], "ablation")

    def test_fails_when_only_a_green_predicted_mutation_control_is_present(self):
        # The revert leg of a mutation experiment: it confirms the
        # experiment was reversible, and shows nobody watching the oracle
        # fail. Accepting it would let "somebody watched this fail" be
        # satisfied by evidence that nobody ever did.
        receipts = [evidence_receipt(control=self.mutation(expectation="green", observed="green"))]
        verdict = run_audit("t", "c", self.contract_provenance(), receipts)
        self.assertEqual(verdict.failure_reason, "missing-control")
        self.assertTrue(verdict.details["other_controls"][0]["behaved_as_predicted"])

    def test_fails_when_the_only_control_attests_a_different_claim(self):
        # `of_claim` is what binds a control to a claim, and it is an
        # explicit pointer - a control for someone else's claim is not
        # evidence for this one.
        receipts = [evidence_receipt(control=self.mutation(of_claim="claim-2"))]
        verdict = run_audit("t", "c", self.contract_provenance(), receipts)
        self.assertEqual(verdict.failure_reason, "missing-control")
        self.assertEqual(verdict.details["controls_found"], 0)

    @staticmethod
    def accepted_receipt_carrying(control: Control) -> Receipt:
        """A receipt whose own verdict is `accepted` while its control
        block claims the run was observed RED. Nobody watched this
        oracle fail: the two halves of the same artifact contradict
        each other."""
        return Receipt(
            target_id="t",
            candidate_id="cand1",
            checker=Checker(kind="model-checker", name="checker-x", version="0.1.0"),
            verdict="accepted",
            certificate=None,
            harness="harness_x",
            bound=8,
            env_assumptions="synthetic",
            obligations=(Obligation(id="t", status="held"),),
            produced_at=now_iso(),
            claim_id="claim-1",
            subject=Subject(repo="example/subject", commit="0" * 40, unit=None),
            toolchain=Toolchain(
                tool=Tool(name="checker-x", commit_or_version="0" * 40),
                dependencies=(), flags=(), features=None,
            ),
            control=control,
        )

    def test_a_red_control_on_an_accepted_receipt_never_qualifies(self):
        # The control block says "observed: red"; the receipt carrying it
        # says the run was accepted. A control block is metadata a caller
        # writes - it is the CHECKER's verdict that says whether anything
        # actually went red.
        receipts = [self.accepted_receipt_carrying(self.mutation())]
        verdict = run_audit("t", "c", self.contract_provenance(), receipts)
        self.assertEqual(verdict.verdict, "fail")
        self.assertEqual(verdict.failure_reason, "missing-control")
        self.assertEqual(verdict.details["observed_red_mutation_controls"], 0)
        self.assertEqual(len(verdict.details["contradictions"]), 1)
        self.assertEqual(
            verdict.details["contradictions"][0]["carrying_receipt_verdict"], "accepted",
        )

    def test_a_contradictory_twin_is_reported_alongside_a_genuine_control(self):
        # Two byte-identical control blocks, one on a rejected receipt
        # (genuine) and one on an accepted receipt (contradictory). The
        # genuine one qualifies; the contradictory one must still be
        # reported, not silently folded into its twin.
        receipts = [
            evidence_receipt(control=self.mutation()),
            self.accepted_receipt_carrying(self.mutation()),
        ]
        verdict = run_audit("t", "c", self.contract_provenance(), receipts)
        self.assertEqual(verdict.verdict, "pass")
        self.assertEqual(verdict.details["controls"]["observed_red_mutation_controls"], 1)
        self.assertEqual(len(verdict.details["controls"]["contradictions"]), 1)
        self.assertEqual(len(verdict.details["controls"]["other_controls"]), 1)

    def test_a_red_control_on_a_rejected_receipt_qualifies(self):
        # The legitimate case, stated explicitly: the carrying receipt is
        # a non-acceptance, so the oracle really was watched to fail.
        receipts = [evidence_receipt(control=self.mutation())]
        self.assertEqual(receipts[0].verdict, "rejected")
        verdict = run_audit("t", "c", self.contract_provenance(), receipts)
        self.assertEqual(verdict.verdict, "pass")
        self.assertEqual(verdict.details["controls"]["observed_red_mutation_controls"], 1)
        self.assertEqual(verdict.details["controls"]["contradictions"], [])

    def test_abstains_for_a_probe_grade_claim(self):
        provenance = self.contract_provenance(claim_grade="probe")
        ok, details = check_controls(provenance, [evidence_receipt()])
        self.assertTrue(ok)
        self.assertFalse(details["judged"])
        self.assertIn("probe", details["reason"])

    def test_abstains_when_no_grade_is_declared(self):
        provenance = self.contract_provenance(claim_grade=None)
        ok, details = check_controls(provenance, [evidence_receipt()])
        self.assertTrue(ok)
        self.assertFalse(details["judged"])

    def test_abstains_when_no_receipt_set_is_supplied(self):
        # Distinct from the empty set above: "I have no store to search"
        # and "I searched and found nothing" are different statements.
        ok, details = check_controls(self.contract_provenance(), None)
        self.assertTrue(ok)
        self.assertFalse(details["judged"])
        self.assertIn("no receipt set supplied", details["reason"])

    def test_run_audit_defaults_to_abstaining(self):
        verdict = run_audit("t", "c", self.contract_provenance())
        self.assertEqual(verdict.verdict, "pass")
        self.assertFalse(verdict.details["controls"]["judged"])

    def test_contract_grade_requires_a_claim_id_at_construction(self):
        # Otherwise a contract claim whose evidence cannot be located
        # would escape the check rather than fail it.
        with self.assertRaises(ValueError):
            self.contract_provenance(claim_id=None)

    def test_unknown_claim_grade_rejected_at_construction(self):
        with self.assertRaises(ValueError):
            self.contract_provenance(claim_grade="pretty-sure")


class ObligationStatusTests(unittest.TestCase):
    """The audit reads the CURRENT receipt's obligation statuses. A
    checker that reports an obligation as `vacuous` or `not-exercised`
    has said the obligation was never established; the run's overall
    `accepted` verdict does not overrule that, and the audit must not
    pass a target whose own receipt says so."""

    @staticmethod
    def provenance() -> TargetProvenance:
        return TargetProvenance(
            source="synthetic",
            statement_text="forall (s : State), Ready s -> Safe s",
            claim_keywords=(),
            preconditions=(),
        )

    @staticmethod
    def receipt_with(*statuses: str, verdict="accepted") -> Receipt:
        return Receipt(
            target_id="t",
            candidate_id="c",
            checker=Checker(kind="model-checker", name="checker-x", version="0.1.0"),
            verdict=verdict,
            certificate=None,
            harness="harness_x",
            bound=8,
            env_assumptions="synthetic",
            obligations=tuple(
                Obligation(id=f"o{i}", status=status) for i, status in enumerate(statuses)
            ),
            produced_at=now_iso(),
            schema_version="1.0.0",
        )

    def test_passes_when_every_obligation_held(self):
        verdict = run_audit(
            "t", "c", self.provenance(), receipt=self.receipt_with("held", "held"),
        )
        self.assertEqual(verdict.verdict, "pass")
        self.assertTrue(verdict.details["obligation_status"]["judged"])

    def test_fails_on_a_vacuous_obligation_even_though_the_checker_accepted(self):
        verdict = run_audit(
            "t", "c", self.provenance(), receipt=self.receipt_with("held", "vacuous"),
        )
        self.assertEqual(verdict.verdict, "fail")
        self.assertEqual(verdict.failure_reason, "vacuous-precondition")
        self.assertEqual(verdict.details["receipt_verdict"], "accepted")
        self.assertEqual(
            verdict.details["unestablished"], [{"obligation_id": "o1", "status": "vacuous"}],
        )

    def test_fails_on_a_not_exercised_obligation(self):
        verdict = run_audit(
            "t", "c", self.provenance(), receipt=self.receipt_with("not-exercised"),
        )
        self.assertEqual(verdict.failure_reason, "vacuous-precondition")
        self.assertEqual(verdict.details["unestablished"][0]["status"], "not-exercised")

    def test_abstains_when_no_receipt_is_supplied(self):
        verdict = run_audit("t", "c", self.provenance())
        self.assertEqual(verdict.verdict, "pass")
        self.assertFalse(verdict.details["obligation_status"]["judged"])

    def test_refuses_a_receipt_about_another_target_or_candidate(self):
        # Auditing target/candidate X against Y's receipt is not a
        # judgment about anything - it is a wiring bug, and a silent
        # pass is the worst possible response to one.
        with self.assertRaises(ValueError):
            run_audit("other", "c", self.provenance(), receipt=self.receipt_with("held"))
        with self.assertRaises(ValueError):
            run_audit("t", "other", self.provenance(), receipt=self.receipt_with("held"))


class CheckOrderingTests(unittest.TestCase):
    """The control check runs LAST: it asks about the evidence set, not
    about what the statement says, and every question about the statement
    itself is more specific."""

    @staticmethod
    def provenance(**overrides) -> TargetProvenance:
        fields = dict(
            source="synthetic",
            statement_text="forall (n : Nat), 0 < n -> 1 <= n",
            claim_keywords=(),
            preconditions=("0 < n",),
            non_vacuity_witness="decide-checked instance: n = 1",
            claim_id="claim-1",
            claim_grade="contract",
        )
        fields.update(overrides)
        return TargetProvenance(**fields)

    def test_vacuity_is_reported_before_missing_control(self):
        verdict = run_audit(
            "t", "c", self.provenance(non_vacuity_witness=None), [],
        )
        self.assertEqual(verdict.failure_reason, "vacuous-precondition")

    def test_unexercised_hypothesis_is_reported_before_missing_control(self):
        verdict = run_audit(
            "t", "c",
            self.provenance(obligation_evidence=(ObligationHypothesisEvidence(
                obligation_id="o1", has_precondition=True,
                states_satisfying=9, states_violating=0, exhaustive=True,
            ),)),
            [],
        )
        self.assertEqual(verdict.failure_reason, "unexercised-hypothesis")

    def test_name_content_is_reported_before_missing_control(self):
        verdict = run_audit(
            "t", "c",
            self.provenance(
                # Claims "sorted", constrains only length.
                statement_text="forall (l : List Nat), 0 < length l -> length (f l) = length l",
                preconditions=("0 < length l",),
                claim_keywords=("sorted",),
            ),
            [],
        )
        self.assertEqual(verdict.failure_reason, "name-content-mismatch")

    def test_scope_is_reported_before_missing_control(self):
        verdict = run_audit(
            "t", "c",
            self.provenance(
                statement_text="theorem k4_is_planar : Planar K4",
                preconditions=(), non_vacuity_witness=None,
                claimed_scope="for every finite graph G, this holds",
            ),
            [],
        )
        self.assertEqual(verdict.failure_reason, "scope-narrower-than-claimed")

    def test_missing_control_is_reported_once_everything_else_passes(self):
        verdict = run_audit("t", "c", self.provenance(), [])
        self.assertEqual(verdict.failure_reason, "missing-control")

    def test_passing_audit_records_all_six_checks_in_order(self):
        receipts = [evidence_receipt(control=Control(
            kind="mutation", expectation="red", observed="red", of_claim="claim-1",
        ))]
        verdict = run_audit("t", "c", self.provenance(), receipts)
        self.assertEqual(verdict.verdict, "pass")
        self.assertEqual(
            verdict.details["checks_run"],
            ["vacuity", "obligation_status", "unexercised_hypothesis", "name_content",
             "scope", "controls"],
        )
