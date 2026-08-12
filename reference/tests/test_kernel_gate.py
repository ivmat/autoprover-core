"""Tests for kernel_gate.py using an injected fake checker command - no
Lean installation required. Also covers the type-level
kernel-vs-model-checker enforcement (ARCHITECTURE.md §4)."""

from __future__ import annotations

import unittest
from pathlib import Path

from autoprover_ref.kernel_gate import CheckerResult, KernelGate


def fake_accepting_checker(_path: Path) -> CheckerResult:
    return CheckerResult(accepted=True, exit_code=0, stdout="ok")


def fake_rejecting_checker(_path: Path) -> CheckerResult:
    return CheckerResult(accepted=False, exit_code=1, stderr="error: type mismatch")


class KernelGateBasicTests(unittest.TestCase):
    def test_accepted_kernel_receipt_has_certificate(self):
        gate = KernelGate(
            checker_command=fake_accepting_checker,
            checker_name="fake-lean",
            checker_version="0.0.0",
            kind="kernel",
            toolchain_id="fake-toolchain-1",
        )
        receipt = gate.check(target_id="t1", candidate_id="c1", candidate_file="t1.lean")
        self.assertEqual(receipt.verdict, "accepted")
        self.assertIsNotNone(receipt.certificate)
        self.assertEqual(receipt.certificate.toolchain_id, "fake-toolchain-1")
        self.assertIsNone(receipt.harness)
        self.assertIsNone(receipt.bound)
        self.assertIsNone(receipt.env_assumptions)
        self.assertEqual(receipt.checker.kind, "kernel")
        self.assertEqual([o.status for o in receipt.obligations], ["held"])

    def test_rejected_kernel_receipt_has_no_certificate(self):
        gate = KernelGate(
            checker_command=fake_rejecting_checker,
            checker_name="fake-lean",
            checker_version="0.0.0",
            kind="kernel",
            toolchain_id="fake-toolchain-1",
        )
        receipt = gate.check(target_id="t1", candidate_id="c1", candidate_file="t1.lean")
        self.assertEqual(receipt.verdict, "rejected")
        self.assertIsNone(receipt.certificate)
        self.assertEqual([o.status for o in receipt.obligations], ["failed"])

    def test_never_trusts_prover_claim_only_checker_exit_status(self):
        # Even if the "candidate file" name/content looks convincing,
        # only what the injected checker command reports matters.
        gate = KernelGate(
            checker_command=fake_rejecting_checker,
            checker_name="fake-lean",
            checker_version="0.0.0",
            kind="kernel",
            toolchain_id="fake-toolchain-1",
        )
        receipt = gate.check(
            target_id="definitely_true_theorem", candidate_id="obviously_correct_proof",
            candidate_file="definitely_true.lean",
        )
        self.assertEqual(receipt.verdict, "rejected")

    def test_kernel_gate_rejects_harness_arguments(self):
        gate = KernelGate(
            checker_command=fake_accepting_checker,
            checker_name="fake-lean",
            checker_version="0.0.0",
            kind="kernel",
            toolchain_id="fake-toolchain-1",
        )
        with self.assertRaises(ValueError):
            gate.check(
                target_id="t1", candidate_id="c1", candidate_file="t1.lean",
                harness="should not be allowed for a kernel gate",
            )

    def test_model_checker_gate_requires_harness_bound_env(self):
        gate = KernelGate(
            checker_command=fake_accepting_checker,
            checker_name="fake-kani",
            checker_version="0.0.0",
            kind="model-checker",
            toolchain_id="fake-toolchain-2",
        )
        with self.assertRaises(ValueError):
            gate.check(target_id="t1", candidate_id="c1", candidate_file="t1.rs")

    def test_model_checker_receipt_carries_harness_bound_env_no_certificate(self):
        gate = KernelGate(
            checker_command=fake_accepting_checker,
            checker_name="fake-kani",
            checker_version="0.0.0",
            kind="model-checker",
            toolchain_id="fake-toolchain-2",
        )
        receipt = gate.check(
            target_id="t1", candidate_id="c1", candidate_file="t1.rs",
            harness="harness_main", bound=16, env_assumptions="single-consumer queue",
        )
        self.assertIsNone(receipt.certificate)
        self.assertEqual(receipt.harness, "harness_main")
        self.assertEqual(receipt.bound, 16)
        self.assertEqual(receipt.env_assumptions, "single-consumer queue")

    def test_per_obligation_status_from_checker_result(self):
        def fake_reporting_checker(_path: Path) -> CheckerResult:
            return CheckerResult(
                accepted=True, exit_code=0,
                obligation_statuses={"ob1": "held", "ob2": "vacuous", "ob3": "not-exercised"},
            )

        gate = KernelGate(
            checker_command=fake_reporting_checker,
            checker_name="fake-model-checker",
            checker_version="0.0.0",
            kind="model-checker",
            toolchain_id="fake-toolchain-3",
        )
        receipt = gate.check(
            target_id="t1", candidate_id="c1", candidate_file="t1.rs",
            obligation_ids=["ob1", "ob2", "ob3"],
            harness="h", bound=4, env_assumptions="e",
        )
        statuses = {o.id: o.status for o in receipt.obligations}
        self.assertEqual(statuses, {"ob1": "held", "ob2": "vacuous", "ob3": "not-exercised"})

    def test_invalid_kind_rejected_at_construction(self):
        with self.assertRaises(ValueError):
            KernelGate(
                checker_command=fake_accepting_checker,
                checker_name="x", checker_version="0.0.0",
                kind="not-a-real-kind", toolchain_id="t",
            )


if __name__ == "__main__":
    unittest.main()
