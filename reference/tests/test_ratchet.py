"""Tests for ratchet.py: refuses to accept without both a checker-accept
receipt and an audit-pass verdict; logs removals explicitly; blocks
loudly on a failed recheck. Pure Python - no Lean needed."""

from __future__ import annotations

import unittest

from autoprover_ref.ratchet import Ratchet, RatchetError
from autoprover_ref.receipts import (
    AuditVerdict,
    Certificate,
    Checker,
    Obligation,
    Receipt,
    now_iso,
)

from _tmpdir import TempDirCase


def accepted_receipt(target_id="t1", candidate_id="c1"):
    return Receipt(
        target_id=target_id, candidate_id=candidate_id,
        checker=Checker(kind="kernel", name="lean", version="4.31.0"),
        verdict="accepted",
        certificate=Certificate(checked_file="x.lean", toolchain_id="tc1"),
        harness=None, bound=None, env_assumptions=None,
        obligations=(Obligation(id=target_id, status="held"),),
        produced_at=now_iso(),
        schema_version="1.0.0",
    )


def rejected_receipt(target_id="t1", candidate_id="c1"):
    return Receipt(
        target_id=target_id, candidate_id=candidate_id,
        checker=Checker(kind="kernel", name="lean", version="4.31.0"),
        verdict="rejected", certificate=None,
        harness=None, bound=None, env_assumptions=None,
        obligations=(Obligation(id=target_id, status="failed"),),
        produced_at=now_iso(),
        schema_version="1.0.0",
    )


def pass_audit(target_id="t1", candidate_id="c1"):
    return AuditVerdict(
        target_id=target_id, candidate_id=candidate_id, verdict="pass",
        failure_reason=None, details={}, produced_at=now_iso(),
    )


def fail_audit(target_id="t1", candidate_id="c1", reason="vacuous-precondition"):
    return AuditVerdict(
        target_id=target_id, candidate_id=candidate_id, verdict="fail",
        failure_reason=reason, details={}, produced_at=now_iso(),
    )


class AcceptRequiresBothTests(TempDirCase):
    def test_refuses_without_kernel_accept(self):
        ratchet = Ratchet(self.tmp_path("ratchet.jsonl"))
        with self.assertRaises(RatchetError):
            ratchet.accept(rejected_receipt(), pass_audit())
        self.assertNotIn("t1", ratchet.accepted_targets)

    def test_refuses_without_audit_pass(self):
        ratchet = Ratchet(self.tmp_path("ratchet.jsonl"))
        with self.assertRaises(RatchetError):
            ratchet.accept(accepted_receipt(), fail_audit())
        self.assertNotIn("t1", ratchet.accepted_targets)

    def test_refuses_mismatched_target_candidate(self):
        ratchet = Ratchet(self.tmp_path("ratchet.jsonl"))
        with self.assertRaises(RatchetError):
            ratchet.accept(accepted_receipt(target_id="t1"), pass_audit(target_id="t2"))

    def test_accepts_with_both(self):
        ratchet = Ratchet(self.tmp_path("ratchet.jsonl"))
        entry = ratchet.accept(accepted_receipt(), pass_audit())
        self.assertIn("t1", ratchet.accepted_targets)
        self.assertEqual(entry.target_id, "t1")


class RemovalTests(TempDirCase):
    def test_explicit_removal_logs_event_and_shrinks_set(self):
        ratchet = Ratchet(self.tmp_path("ratchet.jsonl"))
        ratchet.accept(accepted_receipt(), pass_audit())
        self.assertIn("t1", ratchet.accepted_targets)

        event = ratchet.remove("t1", reason="discovered unsoundness in a shared definition")
        self.assertNotIn("t1", ratchet.accepted_targets)
        self.assertEqual(event.target_id, "t1")
        self.assertEqual(event.reason, "discovered unsoundness in a shared definition")

    def test_removal_of_unaccepted_target_raises(self):
        ratchet = Ratchet(self.tmp_path("ratchet.jsonl"))
        with self.assertRaises(RatchetError):
            ratchet.remove("never-accepted", reason="n/a")

    def test_removal_is_visible_after_replay(self):
        log_path = self.tmp_path("ratchet.jsonl")
        r1 = Ratchet(log_path)
        r1.accept(accepted_receipt(), pass_audit())
        r1.remove("t1", reason="bad definition")

        r2 = Ratchet(log_path)
        self.assertNotIn("t1", r2.accepted_targets)


class RecheckTests(TempDirCase):
    def test_recheck_dependents_marks_only_accepted_targets(self):
        ratchet = Ratchet(self.tmp_path("ratchet.jsonl"))
        ratchet.accept(accepted_receipt(target_id="t1", candidate_id="c1"), pass_audit(target_id="t1", candidate_id="c1"))
        marked = ratchet.recheck_dependents("shared_def", ["t1", "t-not-accepted"])
        self.assertEqual(marked, ["t1"])
        self.assertIn("t1", ratchet.marked_for_recheck)

    def test_recheck_confirming_receipt_refreshes_entry(self):
        ratchet = Ratchet(self.tmp_path("ratchet.jsonl"))
        ratchet.accept(accepted_receipt(target_id="t1", candidate_id="c1"), pass_audit(target_id="t1", candidate_id="c1"))
        ratchet.recheck_dependents("shared_def", ["t1"])

        fresh_receipt = accepted_receipt(target_id="t1", candidate_id="c1")
        fresh_audit = pass_audit(target_id="t1", candidate_id="c1")
        event = ratchet.record_recheck_result("t1", "shared_def", fresh_receipt, fresh_audit)

        self.assertIsNone(event)
        self.assertIn("t1", ratchet.accepted_targets)
        self.assertEqual(ratchet.blocking_events, ())
        self.assertNotIn("t1", ratchet.marked_for_recheck)

    def test_recheck_new_failure_raises_blocking_event_and_removes(self):
        ratchet = Ratchet(self.tmp_path("ratchet.jsonl"))
        ratchet.accept(accepted_receipt(target_id="t1", candidate_id="c1"), pass_audit(target_id="t1", candidate_id="c1"))
        ratchet.recheck_dependents("shared_def", ["t1"])

        # Dependency change broke the proof: fresh kernel run now rejects.
        event = ratchet.record_recheck_result(
            "t1", "shared_def", rejected_receipt(target_id="t1", candidate_id="c1"), None
        )

        self.assertIsNotNone(event)
        self.assertEqual(event.target_id, "t1")
        self.assertEqual(event.triggering_dependency, "shared_def")
        self.assertNotIn("t1", ratchet.accepted_targets)
        self.assertEqual(len(ratchet.blocking_events), 1)

    def test_blocking_event_is_not_silently_swallowed_on_replay(self):
        log_path = self.tmp_path("ratchet.jsonl")
        r1 = Ratchet(log_path)
        r1.accept(accepted_receipt(target_id="t1", candidate_id="c1"), pass_audit(target_id="t1", candidate_id="c1"))
        r1.recheck_dependents("shared_def", ["t1"])
        r1.record_recheck_result("t1", "shared_def", None, None)

        r2 = Ratchet(log_path)
        self.assertNotIn("t1", r2.accepted_targets)
        self.assertEqual(len(r2.blocking_events), 1)
        self.assertEqual(r2.blocking_events[0].target_id, "t1")


if __name__ == "__main__":
    unittest.main()
