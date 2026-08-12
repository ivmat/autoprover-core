"""Tests for queue.py: the evidence-driven state machine. Covers the
"refuses an evidence-less / wrong-evidence-type / wrong-current-state
transition" discipline and "state is correctly rebuilt by folding the
log" round trip. Pure Python - no Lean, no kernel_gate needed."""

from __future__ import annotations

import unittest

from autoprover_ref.queue import (
    AbandonDecision,
    AttemptStarted,
    CandidateArtifact,
    InvalidTransition,
    NoCandidateProduced,
    RequeueDecision,
    State,
    TargetEntry,
    TargetQueue,
)
from autoprover_ref.receipts import (
    AuditVerdict,
    Certificate,
    Checker,
    Obligation,
    Receipt,
    now_iso,
)

from _tmpdir import TempDirCase


def kernel_receipt(target_id, candidate_id, verdict="accepted"):
    return Receipt(
        target_id=target_id,
        candidate_id=candidate_id,
        checker=Checker(kind="kernel", name="lean", version="4.31.0"),
        verdict=verdict,
        certificate=(
            Certificate(checked_file="x.lean", toolchain_id="leanprover/lean4:v4.31.0")
            if verdict == "accepted" else None
        ),
        harness=None, bound=None, env_assumptions=None,
        obligations=(Obligation(id=target_id, status="held" if verdict == "accepted" else "failed"),),
        produced_at=now_iso(),
    )


def audit_verdict(target_id, candidate_id, verdict="pass", failure_reason=None):
    return AuditVerdict(
        target_id=target_id, candidate_id=candidate_id, verdict=verdict,
        failure_reason=failure_reason, details={}, produced_at=now_iso(),
    )


class HappyPathTests(TempDirCase):
    def test_full_acceptance_path(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="1 = 1", provenance={"source": "test"}))
        self.assertEqual(q.state_of("t1"), State.QUEUED)

        q.start_attempt("t1", AttemptStarted(attempt_id="a1", prover_name="human"))
        self.assertEqual(q.state_of("t1"), State.ATTEMPTING)

        q.record_candidate("t1", CandidateArtifact(candidate_id="c1", artifact_path="c1.lean"))
        self.assertEqual(q.state_of("t1"), State.CANDIDATE_PRODUCED)

        state = q.record_kernel_receipt("t1", kernel_receipt("t1", "c1"))
        self.assertEqual(state, State.KERNEL_CHECKED)
        self.assertEqual(q.state_of("t1"), State.KERNEL_CHECKED)

        state = q.record_audit("t1", audit_verdict("t1", "c1", verdict="pass"))
        self.assertEqual(state, State.ACCEPTED)
        self.assertEqual(q.state_of("t1"), State.ACCEPTED)

    def test_kernel_rejected_then_requeue(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        q.start_attempt("t1", AttemptStarted(attempt_id="a1", prover_name="p"))
        q.record_candidate("t1", CandidateArtifact(candidate_id="c1", artifact_path="c1.lean"))
        state = q.record_kernel_receipt("t1", kernel_receipt("t1", "c1", verdict="rejected"))
        self.assertEqual(state, State.KERNEL_REJECTED)
        state = q.requeue_from_kernel_rejected("t1", RequeueDecision(reason="try again"))
        self.assertEqual(state, State.QUEUED)

    def test_kernel_rejected_then_abandon(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        q.start_attempt("t1", AttemptStarted(attempt_id="a1", prover_name="p"))
        q.record_candidate("t1", CandidateArtifact(candidate_id="c1", artifact_path="c1.lean"))
        q.record_kernel_receipt("t1", kernel_receipt("t1", "c1", verdict="rejected"))
        state = q.abandon_from_kernel_rejected("t1", AbandonDecision(reason="not worth retrying"))
        self.assertEqual(state, State.ABANDONED)

    def test_audit_rejected_then_requeue(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        q.start_attempt("t1", AttemptStarted(attempt_id="a1", prover_name="p"))
        q.record_candidate("t1", CandidateArtifact(candidate_id="c1", artifact_path="c1.lean"))
        q.record_kernel_receipt("t1", kernel_receipt("t1", "c1"))
        state = q.record_audit(
            "t1", audit_verdict("t1", "c1", verdict="fail", failure_reason="vacuous-precondition")
        )
        self.assertEqual(state, State.AUDIT_REJECTED)
        state = q.requeue_from_audit_rejected("t1", RequeueDecision(reason="fix the statement"))
        self.assertEqual(state, State.QUEUED)

    def test_no_candidate_produced_requeues(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        q.start_attempt("t1", AttemptStarted(attempt_id="a1", prover_name="p"))
        state = q.record_no_candidate("t1", NoCandidateProduced(attempt_id="a1", reason="no proof found"))
        self.assertEqual(state, State.QUEUED)


class RefusesEvidencelessTransitionTests(TempDirCase):
    def test_start_attempt_without_evidence_object_raises(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        with self.assertRaises(InvalidTransition):
            q.start_attempt("t1", "not an AttemptStarted instance")  # type: ignore[arg-type]
        # State must be unchanged after the refused transition.
        self.assertEqual(q.state_of("t1"), State.QUEUED)

    def test_record_candidate_with_wrong_evidence_type_raises(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        q.start_attempt("t1", AttemptStarted(attempt_id="a1", prover_name="p"))
        with self.assertRaises(InvalidTransition):
            q.record_candidate("t1", {"candidate_id": "c1"})  # dict, not CandidateArtifact
        self.assertEqual(q.state_of("t1"), State.ATTEMPTING)

    def test_enqueue_requires_target_entry(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        with self.assertRaises(InvalidTransition):
            q.enqueue("t1", None)  # type: ignore[arg-type]
        self.assertIsNone(q.state_of("t1"))

    def test_transition_from_wrong_state_raises(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        # Cannot record a candidate before an attempt has started.
        with self.assertRaises(InvalidTransition):
            q.record_candidate("t1", CandidateArtifact(candidate_id="c1", artifact_path="c1.lean"))
        self.assertEqual(q.state_of("t1"), State.QUEUED)

    def test_double_enqueue_raises(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        with self.assertRaises(InvalidTransition):
            q.enqueue("t1", TargetEntry(statement="s", provenance={}))

    def test_kernel_receipt_for_wrong_target_raises(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        q.start_attempt("t1", AttemptStarted(attempt_id="a1", prover_name="p"))
        q.record_candidate("t1", CandidateArtifact(candidate_id="c1", artifact_path="c1.lean"))
        with self.assertRaises(InvalidTransition):
            q.record_kernel_receipt("t1", kernel_receipt("t-other", "c1"))

    def test_cannot_accept_from_kernel_checked_without_audit(self):
        q = TargetQueue(self.tmp_path("q.jsonl"))
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        q.start_attempt("t1", AttemptStarted(attempt_id="a1", prover_name="p"))
        q.record_candidate("t1", CandidateArtifact(candidate_id="c1", artifact_path="c1.lean"))
        q.record_kernel_receipt("t1", kernel_receipt("t1", "c1"))
        # No transition method takes a plain string/bool as "evidence" -
        # attempting to reuse record_kernel_receipt again (already past
        # candidate-produced) must also raise.
        with self.assertRaises(InvalidTransition):
            q.record_kernel_receipt("t1", kernel_receipt("t1", "c1"))


class StateRebuildByFoldingLogTests(TempDirCase):
    def test_replay_from_log_file_reproduces_state(self):
        log_path = self.tmp_path("q.jsonl")
        q1 = TargetQueue(log_path)
        q1.enqueue("t1", TargetEntry(statement="s", provenance={}))
        q1.start_attempt("t1", AttemptStarted(attempt_id="a1", prover_name="p"))
        q1.record_candidate("t1", CandidateArtifact(candidate_id="c1", artifact_path="c1.lean"))
        q1.record_kernel_receipt("t1", kernel_receipt("t1", "c1"))
        q1.record_audit("t1", audit_verdict("t1", "c1", verdict="pass"))
        self.assertEqual(q1.state_of("t1"), State.ACCEPTED)

        # A brand-new TargetQueue instance pointed at the same log file
        # must derive the identical state purely by folding the log -
        # nothing else is passed in.
        q2 = TargetQueue.replay(log_path)
        self.assertEqual(q2.state_of("t1"), State.ACCEPTED)
        self.assertEqual(q2.all_states, q1.all_states)

    def test_replay_reproduces_multi_target_state(self):
        log_path = self.tmp_path("q.jsonl")
        q1 = TargetQueue(log_path)
        for tid in ("t1", "t2", "t3"):
            q1.enqueue(tid, TargetEntry(statement="s", provenance={}))
        q1.start_attempt("t2", AttemptStarted(attempt_id="a2", prover_name="p"))
        q1.start_attempt("t3", AttemptStarted(attempt_id="a3", prover_name="p"))
        q1.record_candidate("t3", CandidateArtifact(candidate_id="c3", artifact_path="c3.lean"))

        q2 = TargetQueue.replay(log_path)
        self.assertEqual(q2.state_of("t1"), State.QUEUED)
        self.assertEqual(q2.state_of("t2"), State.ATTEMPTING)
        self.assertEqual(q2.state_of("t3"), State.CANDIDATE_PRODUCED)

    def test_audit_hop_recorded_as_two_events(self):
        log_path = self.tmp_path("q.jsonl")
        q = TargetQueue(log_path)
        q.enqueue("t1", TargetEntry(statement="s", provenance={}))
        q.start_attempt("t1", AttemptStarted(attempt_id="a1", prover_name="p"))
        q.record_candidate("t1", CandidateArtifact(candidate_id="c1", artifact_path="c1.lean"))
        q.record_kernel_receipt("t1", kernel_receipt("t1", "c1"))
        q.record_audit("t1", audit_verdict("t1", "c1", verdict="pass"))
        events = q.events_for("t1")
        hops = [(e["from_state"], e["to_state"]) for e in events]
        self.assertIn(("kernel-checked", "audited"), hops)
        self.assertIn(("audited", "accepted"), hops)


if __name__ == "__main__":
    unittest.main()
