"""Tests for kernel_gate.py using an injected fake checker command - no
Lean installation required. Also covers the type-level
kernel-vs-model-checker enforcement (ARCHITECTURE.md §4), the
tool-failure-is-not-property-failure mapping (a reported failure_kind
becomes verdict 'error', never 'rejected'), and which receipt schema
version a gate emits."""

from __future__ import annotations

import unittest
from pathlib import Path

from autoprover_ref.kernel_gate import CheckerResult, KernelGate, lean_checker_command
from autoprover_ref.receipts import (
    Control,
    Coverage,
    Dependency,
    Subject,
    Tool,
    Toolchain,
    validate_receipt_dict,
)


def make_toolchain() -> Toolchain:
    return Toolchain(
        tool=Tool(name="checker-x", commit_or_version="9f2c1ab3d4e5f60718293a4b5c6d7e8f90a1b2c3"),
        dependencies=(Dependency(name="solver-y", version="6.8.0"),),
        flags=("--unstable-semantics",),
        features=None,
    )


def make_subject() -> Subject:
    return Subject(
        repo="example/subject",
        commit="0123456789abcdef0123456789abcdef01234567",
        unit=None,
    )


def v2_gate(checker_command, **overrides) -> KernelGate:
    kwargs = dict(
        checker_command=checker_command,
        checker_name="fake-checker",
        checker_version="0.0.0",
        kind="model-checker",
        toolchain_id="fake-toolchain-1",
        subject=make_subject(),
        toolchain=make_toolchain(),
        claim_id="claim-1",
    )
    kwargs.update(overrides)
    return KernelGate(**kwargs)


def fake_accepting_checker(_path: Path, _timeout=None) -> CheckerResult:
    return CheckerResult(accepted=True, exit_code=0, stdout="ok")


def fake_rejecting_checker(_path: Path, _timeout=None) -> CheckerResult:
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
        def fake_reporting_checker(_path: Path, _timeout=None) -> CheckerResult:
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


class ReceiptVersionSelectionTests(unittest.TestCase):
    def test_gate_without_provenance_emits_1_0_0(self):
        gate = KernelGate(
            checker_command=fake_accepting_checker,
            checker_name="fake-lean", checker_version="0.0.0",
            kind="kernel", toolchain_id="fake-toolchain-1",
        )
        receipt = gate.check(target_id="t1", candidate_id="c1", candidate_file="t1.lean")
        self.assertEqual(receipt.schema_version, "1.0.0")
        self.assertIsNone(receipt.claim_id)
        validate_receipt_dict(receipt.to_dict())

    def test_gate_with_full_provenance_emits_2_0_0(self):
        gate = v2_gate(fake_accepting_checker)
        receipt = gate.check(
            target_id="t1", candidate_id="c1", candidate_file="t1.rs",
            harness="h", bound=8, env_assumptions="e",
        )
        self.assertEqual(receipt.schema_version, "2.0.0")
        self.assertEqual(receipt.claim_id, "claim-1")
        self.assertEqual(receipt.subject.repo, "example/subject")
        self.assertEqual(receipt.toolchain.tool.name, "checker-x")
        validate_receipt_dict(receipt.to_dict())

    def test_partial_provenance_is_a_construction_error_not_a_silent_downgrade(self):
        for dropped in ("subject", "toolchain", "claim_id"):
            with self.subTest(dropped=dropped):
                with self.assertRaises(ValueError) as ctx:
                    v2_gate(fake_accepting_checker, **{dropped: None})
                self.assertIn("all-or-nothing", str(ctx.exception))


class ToolFailureTests(unittest.TestCase):
    """A checker that failed to produce a verdict must never be reported
    as one that refuted the candidate."""

    @staticmethod
    def failing_checker(kind):
        def run(_path: Path, _timeout=None) -> CheckerResult:
            return CheckerResult(accepted=False, exit_code=-1, failure_kind=kind)
        return run

    def test_failure_kind_becomes_error_verdict_with_the_kind_recorded(self):
        for kind in ("timeout", "oom", "unsupported-construct", "tool-error"):
            with self.subTest(failure_kind=kind):
                gate = v2_gate(self.failing_checker(kind))
                receipt = gate.check(
                    target_id="t1", candidate_id="c1", candidate_file="t1.rs",
                    harness="h", bound=8, env_assumptions="e",
                )
                self.assertEqual(receipt.verdict, "error")
                self.assertEqual(receipt.failure_kind, kind)
                validate_receipt_dict(receipt.to_dict())

    def test_error_verdict_never_reports_obligations_as_failed(self):
        # No verdict was produced, so no obligation was decided; calling
        # them `failed` would be the same category error as calling the
        # run `rejected`.
        gate = v2_gate(self.failing_checker("timeout"))
        receipt = gate.check(
            target_id="t1", candidate_id="c1", candidate_file="t1.rs",
            obligation_ids=["ob1", "ob2"],
            harness="h", bound=8, env_assumptions="e",
        )
        self.assertEqual(
            [o.status for o in receipt.obligations], ["not-exercised", "not-exercised"]
        )

    def test_unsupported_construct_is_not_a_rejection(self):
        gate = v2_gate(self.failing_checker("unsupported-construct"))
        receipt = gate.check(
            target_id="t1", candidate_id="c1", candidate_file="t1.rs",
            harness="h", bound=8, env_assumptions="e",
        )
        self.assertNotEqual(receipt.verdict, "rejected")
        self.assertEqual(receipt.failure_kind, "unsupported-construct")

    def test_a_1_0_0_gate_refuses_to_drop_a_reported_failure_kind(self):
        # 1.0.0 has no field for it. Writing a bare 'error' would lose
        # the retry-bigger vs out-of-scope distinction, so the gate says
        # so loudly instead of quietly discarding it.
        gate = KernelGate(
            checker_command=self.failing_checker("oom"),
            checker_name="fake-lean", checker_version="0.0.0",
            kind="kernel", toolchain_id="fake-toolchain-1",
        )
        with self.assertRaises(ValueError) as ctx:
            gate.check(target_id="t1", candidate_id="c1", candidate_file="t1.lean")
        self.assertIn("oom", str(ctx.exception))

    def test_unknown_failure_kind_rejected_at_the_seam(self):
        with self.assertRaises(ValueError):
            CheckerResult(accepted=False, exit_code=1, failure_kind="probably-fine")


class TimeoutSeamTests(unittest.TestCase):
    def test_gate_passes_its_timeout_to_the_checker_command(self):
        seen = {}

        def recording_checker(_path: Path, timeout=None) -> CheckerResult:
            seen["timeout"] = timeout
            return CheckerResult(accepted=True, exit_code=0)

        gate = v2_gate(recording_checker, timeout=30.0)
        gate.check(
            target_id="t1", candidate_id="c1", candidate_file="t1.rs",
            harness="h", bound=8, env_assumptions="e",
        )
        self.assertEqual(seen["timeout"], 30.0)

    def test_no_timeout_is_passed_explicitly_as_none(self):
        seen = {}

        def recording_checker(_path: Path, timeout="unset") -> CheckerResult:
            seen["timeout"] = timeout
            return CheckerResult(accepted=True, exit_code=0)

        gate = v2_gate(recording_checker)
        gate.check(
            target_id="t1", candidate_id="c1", candidate_file="t1.rs",
            harness="h", bound=8, env_assumptions="e",
        )
        self.assertIsNone(seen["timeout"])


class CoverageAndControlTests(unittest.TestCase):
    def test_reported_coverage_reaches_the_receipt(self):
        def covering_checker(_path: Path, _timeout=None) -> CheckerResult:
            return CheckerResult(
                accepted=True, exit_code=0,
                obligation_statuses={"ob1": "held", "ob2": "held"},
                obligation_coverage={
                    "ob1": Coverage(states_satisfying=12, states_violating=7, exhaustive=True),
                },
            )

        gate = v2_gate(covering_checker)
        receipt = gate.check(
            target_id="t1", candidate_id="c1", candidate_file="t1.rs",
            obligation_ids=["ob1", "ob2"],
            harness="h", bound=8, env_assumptions="e",
        )
        by_id = {o.id: o for o in receipt.obligations}
        self.assertEqual(by_id["ob1"].coverage.states_violating, 7)
        # Explicitly null for the obligation nothing was measured about,
        # never a zeroed record that would read as "measured, found none".
        self.assertIsNone(by_id["ob2"].coverage)
        validate_receipt_dict(receipt.to_dict())

    def test_coverage_accepts_plain_dicts_and_rejects_anything_else(self):
        def dict_coverage_checker(_path: Path, _timeout=None) -> CheckerResult:
            return CheckerResult(
                accepted=True, exit_code=0,
                obligation_coverage={
                    "t1": {"states_satisfying": 1, "states_violating": 2, "exhaustive": False},
                },
            )

        receipt = v2_gate(dict_coverage_checker).check(
            target_id="t1", candidate_id="c1", candidate_file="t1.rs",
            harness="h", bound=8, env_assumptions="e",
        )
        self.assertEqual(receipt.obligations[0].coverage.states_violating, 2)

        def bad_coverage_checker(_path: Path, _timeout=None) -> CheckerResult:
            return CheckerResult(
                accepted=True, exit_code=0, obligation_coverage={"t1": "lots"},
            )

        with self.assertRaises(ValueError):
            v2_gate(bad_coverage_checker).check(
                target_id="t1", candidate_id="c1", candidate_file="t1.rs",
                harness="h", bound=8, env_assumptions="e",
            )

    def test_control_block_is_recorded_on_the_receipt(self):
        control = Control(
            kind="mutation", expectation="red", observed="red", of_claim="claim-1",
        )
        receipt = v2_gate(fake_rejecting_checker).check(
            target_id="t1", candidate_id="c1", candidate_file="t1.rs",
            harness="h", bound=8, env_assumptions="e", control=control,
        )
        self.assertEqual(receipt.verdict, "rejected")
        self.assertTrue(receipt.control.passed())
        validate_receipt_dict(receipt.to_dict())

    def test_control_requires_a_2_0_0_gate(self):
        gate = KernelGate(
            checker_command=fake_accepting_checker,
            checker_name="fake-lean", checker_version="0.0.0",
            kind="kernel", toolchain_id="fake-toolchain-1",
        )
        with self.assertRaises(ValueError):
            gate.check(
                target_id="t1", candidate_id="c1", candidate_file="t1.lean",
                control=Control(
                    kind="ablation", expectation="red", observed="red", of_claim="claim-1",
                ),
            )


class DefaultCheckerCommandFailureTests(unittest.TestCase):
    """The default (Lean) checker command turns a run that produced no
    verdict into a `tool-error` RESULT, never into a rejection and never
    into an exception with no receipt behind it. A checker killed by a
    signal did not refute anything, and an executable that could not be
    launched said nothing about the candidate at all."""

    def test_a_signalled_checker_is_a_tool_error_not_a_rejection(self):
        # /bin/sh kills itself: the process dies on SIGKILL, so its exit
        # is a negative return code, not a non-zero verdict.
        command = lean_checker_command("/bin/sh", ("-c", "kill -9 $$"))
        result = command(Path("ignored.lean"), None)
        self.assertEqual(result.failure_kind, "tool-error")
        self.assertFalse(result.accepted)
        self.assertLess(result.exit_code, 0)

    def test_a_checker_that_cannot_be_launched_is_a_tool_error(self):
        command = lean_checker_command("/nonexistent/definitely-not-a-checker")
        result = command(Path("ignored.lean"), None)
        self.assertEqual(result.failure_kind, "tool-error")
        self.assertFalse(result.accepted)

    def test_an_ordinary_non_zero_exit_is_still_a_rejection(self):
        # The distinction only earns its keep if a real refutation still
        # reads as one: exit 1 is the checker answering, not failing.
        command = lean_checker_command("/bin/sh", ("-c", "exit 1"))
        result = command(Path("ignored.lean"), None)
        self.assertIsNone(result.failure_kind)
        self.assertFalse(result.accepted)
        self.assertEqual(result.exit_code, 1)

    def test_a_zero_exit_is_still_an_acceptance(self):
        command = lean_checker_command("/bin/sh", ("-c", "exit 0"))
        result = command(Path("ignored.lean"), None)
        self.assertIsNone(result.failure_kind)
        self.assertTrue(result.accepted)


if __name__ == "__main__":
    unittest.main()
