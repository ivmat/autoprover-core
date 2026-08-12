"""Tests for audit.py: catches a synthetic vacuously-true target, a
synthetic overclaiming name, and a synthetic narrowed-scope target, all on
pure Python text/metadata - no Lean, no kernel gate needed. See
reference/examples/ for a Lean-backed worked version of the vacuity
case."""

from __future__ import annotations

import unittest

from autoprover_ref.audit import TargetProvenance, check_scope, run_audit


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
