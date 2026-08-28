"""Integration tests for pipeline.py driving a target end-to-end through
queue -> kernel_gate -> audit -> ratchet, using an injected fake checker
command. Pure Python - no Lean needed. This is the same wiring
reference/examples/run_example.py uses against a real Lean checker."""

from __future__ import annotations

import unittest
from pathlib import Path

from autoprover_ref.audit import TargetProvenance
from autoprover_ref.kernel_gate import CheckerResult, KernelGate
from autoprover_ref.pipeline import Pipeline
from autoprover_ref.queue import State, TargetQueue
from autoprover_ref.ratchet import Ratchet

from _tmpdir import TempDirCase


def fake_accepting_checker(_path: Path, _timeout=None) -> CheckerResult:
    return CheckerResult(accepted=True, exit_code=0)


def fake_rejecting_checker(_path: Path, _timeout=None) -> CheckerResult:
    return CheckerResult(accepted=False, exit_code=1)


class PipelineTests(TempDirCase):
    def _make_pipeline(self, checker_command) -> Pipeline:
        gate = KernelGate(
            checker_command=checker_command,
            checker_name="fake-lean",
            checker_version="0.0.0",
            kind="kernel",
            toolchain_id="fake-toolchain",
        )
        return Pipeline(
            queue=TargetQueue(self.tmp_path("queue.jsonl")),
            gate=gate,
            ratchet=Ratchet(self.tmp_path("ratchet.jsonl")),
            receipts_dir=self.tmp_path("receipts"),
        )

    def test_genuine_target_reaches_accepted(self):
        pipeline = self._make_pipeline(fake_accepting_checker)
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (n : Nat), n + 0 = n",
            claim_keywords=(),
            preconditions=(),
        )
        result = pipeline.run_target(
            target_id="genuine", candidate_id="cand1",
            candidate_file="genuine.lean", provenance=provenance,
        )
        self.assertEqual(result.final_state, State.ACCEPTED.value)
        self.assertIsNotNone(result.accepted_entry)
        self.assertIn("genuine", pipeline.ratchet.accepted_targets)
        # Receipts were actually written to disk.
        kernel_path = self.tmp_path("receipts") / "genuine.cand1.kernel.json"
        audit_path = self.tmp_path("receipts") / "genuine.cand1.audit.json"
        self.assertTrue(kernel_path.exists())
        self.assertTrue(audit_path.exists())

    def test_kernel_rejected_target_returns_to_queued_not_ratcheted(self):
        pipeline = self._make_pipeline(fake_rejecting_checker)
        provenance = TargetProvenance(source="synthetic", statement_text="False")
        result = pipeline.run_target(
            target_id="bad", candidate_id="cand1",
            candidate_file="bad.lean", provenance=provenance,
        )
        self.assertEqual(result.final_state, State.QUEUED.value)
        self.assertIsNone(result.accepted_entry)
        self.assertNotIn("bad", pipeline.ratchet.accepted_targets)

    def test_vacuous_target_kernel_accepts_but_audit_rejects(self):
        pipeline = self._make_pipeline(fake_accepting_checker)
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (l : List Nat), False -> Sorted l",
            claim_keywords=("sorted",),
            preconditions=("False",),
            non_vacuity_witness=None,
        )
        result = pipeline.run_target(
            target_id="vacuous", candidate_id="cand1",
            candidate_file="vacuous.lean", provenance=provenance,
        )
        self.assertEqual(result.kernel_receipt.verdict, "accepted")
        self.assertEqual(result.audit_verdict.verdict, "fail")
        self.assertEqual(result.audit_verdict.failure_reason, "vacuous-precondition")
        self.assertEqual(result.final_state, State.QUEUED.value)
        self.assertNotIn("vacuous", pipeline.ratchet.accepted_targets)


class VacuousObligationDoesNotReachTheRatchetTests(TempDirCase):
    """A checker can accept a run overall while reporting one obligation
    as `vacuous` - that is exactly what the four-value status vocabulary
    exists to express (model_checker.py). The pipeline must not carry
    such a run through to the ratchet: the audit layer is handed the
    CURRENT receipt, and an obligation the checker itself says was never
    established cannot be part of an accepted result."""

    def _model_checker_pipeline(self, statuses: dict) -> Pipeline:
        def checker(_path: Path, _timeout=None) -> CheckerResult:
            # Accepted overall (nothing FAILED), with a per-obligation
            # status bucket - `model_checker.model_checker_command`
            # reports exactly this shape.
            return CheckerResult(
                accepted=True, exit_code=0, obligation_statuses=statuses,
            )

        gate = KernelGate(
            checker_command=checker,
            checker_name="fake-model-checker",
            checker_version="0.0.0",
            kind="model-checker",
            toolchain_id="fake-toolchain",
        )
        return Pipeline(
            queue=TargetQueue(self.tmp_path("queue.jsonl")),
            gate=gate,
            ratchet=Ratchet(self.tmp_path("ratchet.jsonl")),
            receipts_dir=self.tmp_path("receipts"),
        )

    def _run(self, pipeline: Pipeline, statuses: dict):
        provenance = TargetProvenance(
            source="synthetic",
            statement_text="forall (s : State), Ready s -> Safe s",
            claim_keywords=(),
            preconditions=(),
        )
        return pipeline.run_target(
            target_id="mc", candidate_id="cand1", candidate_file="mc.model",
            provenance=provenance, obligation_ids=tuple(statuses),
            harness="harness_x", bound=8, env_assumptions="synthetic",
        )

    def test_vacuous_obligation_is_refused_and_requeued(self):
        statuses = {"o1": "held", "o2": "vacuous"}
        pipeline = self._model_checker_pipeline(statuses)
        result = self._run(pipeline, statuses)

        self.assertEqual(result.kernel_receipt.verdict, "accepted")
        self.assertEqual(result.audit_verdict.verdict, "fail")
        self.assertEqual(result.audit_verdict.failure_reason, "vacuous-precondition")
        self.assertEqual(result.final_state, State.QUEUED.value)
        self.assertNotIn("mc", pipeline.ratchet.accepted_targets)

    def test_not_exercised_obligation_is_refused_and_requeued(self):
        statuses = {"o1": "not-exercised"}
        pipeline = self._model_checker_pipeline(statuses)
        result = self._run(pipeline, statuses)

        self.assertEqual(result.kernel_receipt.verdict, "accepted")
        self.assertEqual(result.audit_verdict.verdict, "fail")
        self.assertEqual(result.final_state, State.QUEUED.value)
        self.assertNotIn("mc", pipeline.ratchet.accepted_targets)

    def test_all_held_obligations_still_reach_the_ratchet(self):
        statuses = {"o1": "held", "o2": "held"}
        pipeline = self._model_checker_pipeline(statuses)
        result = self._run(pipeline, statuses)

        self.assertEqual(result.final_state, State.ACCEPTED.value)
        self.assertIn("mc", pipeline.ratchet.accepted_targets)


if __name__ == "__main__":
    unittest.main()
