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


if __name__ == "__main__":
    unittest.main()
