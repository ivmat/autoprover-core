"""The target queue: a closed state machine driven by evidence
(ARCHITECTURE.md §2).

State is not a status field a component writes prose into. Every
transition function below *consumes* a specific evidence artifact (a
target's provenance record, a prover's attempt/candidate output, a
kernel receipt, an audit verdict, or an explicit requeue/abandon
decision) and *produces* the next state; a transition attempted without
the right evidence — or from the wrong current state — raises rather
than silently doing nothing. No component may set a state it did not
produce evidence for.

The queue is persisted as an append-only JSONL event log. Current state
is never stored as mutable ground truth on its own — it is *derived* by
folding the log, and `TargetQueue.replay` does exactly that from a log
file with no other input. This is the same discipline the rest of the
package uses: state is derived from evidence, not asserted.

One documented divergence from the ARCHITECTURE.md §2 diagram: that
diagram shows a single arrow `kernel-checked → audited → accepted |
audit-rejected`. This module realizes that as two evidence-consuming
hops recorded as two log events from the *same* audit verdict artifact
(kernel-checked → audited, then audited → accepted|audit-rejected) —
both appended atomically within one call to `record_audit`, so folding
the log reproduces exactly the diagram's path. This is a fidelity
choice, not a reinterpretation: the diagram names an intermediate
"audited" state, so an evidence-per-hop implementation has to pass
through it explicitly rather than skip straight from kernel-checked to
a terminal state.
"""

from __future__ import annotations

import json
import os
from dataclasses import asdict, dataclass
from enum import Enum
from pathlib import Path
from typing import Optional, Union

from .receipts import AuditVerdict, Receipt, now_iso

__all__ = [
    "State",
    "QueueError",
    "InvalidTransition",
    "TargetEntry",
    "AttemptStarted",
    "CandidateArtifact",
    "NoCandidateProduced",
    "RequeueDecision",
    "AbandonDecision",
    "TargetQueue",
]


class State(str, Enum):
    QUEUED = "queued"
    ATTEMPTING = "attempting"
    CANDIDATE_PRODUCED = "candidate-produced"
    KERNEL_CHECKED = "kernel-checked"
    KERNEL_REJECTED = "kernel-rejected"
    # A checker that produced NO verdict (timeout, out of memory, an
    # unsupported construct, an internal failure). Deliberately its own
    # state rather than a flavour of `kernel-rejected`: the two call for
    # opposite responses. A rejection says "this candidate is wrong,
    # write another"; an error says "nothing is known about this
    # candidate yet, give the checker more resources or record the
    # clause as out of scope for this tool". Collapsing them sends a
    # prover chasing a ghost (kernel_gate.py's module docstring), and
    # receipt schema 2.0.0 says `error` is "never routed as if a
    # property had been refuted".
    CHECKER_ERROR = "checker-error"
    AUDITED = "audited"
    ACCEPTED = "accepted"
    AUDIT_REJECTED = "audit-rejected"
    ABANDONED = "abandoned"


class QueueError(Exception):
    """Base class for queue errors."""


class InvalidTransition(QueueError):
    """Raised when a transition is attempted from the wrong state, or
    without the evidence artifact that transition requires."""


# --------------------------------------------------------------------------
# Evidence artifacts. Each transition method below accepts exactly one of
# these types (isinstance-checked) — passing a bare string or a dict is a
# TypeError, not a state change. This is what "cannot set a state without
# the evidence that justifies it" means in code, not just in a docstring.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class TargetEntry:
    """Evidence a target satisfies ARCHITECTURE.md §1's entry contract:
    a well-formed statement plus a provenance record. This does not
    guarantee the target is true, or that its eventual name will match
    its statement — only that it is well-formed enough to queue."""

    statement: str
    provenance: dict


@dataclass(frozen=True)
class AttemptStarted:
    """Evidence that a prover attempt began (ARCHITECTURE.md §3)."""

    attempt_id: str
    prover_name: str


@dataclass(frozen=True)
class CandidateArtifact:
    """Evidence a prover produced a candidate (ARCHITECTURE.md §3)."""

    candidate_id: str
    artifact_path: str


@dataclass(frozen=True)
class NoCandidateProduced:
    """Evidence a prover attempt explicitly produced no candidate —
    the other guarantee §3 allows a prover to make, distinct from
    silence."""

    attempt_id: str
    reason: str


@dataclass(frozen=True)
class RequeueDecision:
    """An explicit, logged decision to retry a target after a kernel or
    audit rejection, rather than a silent fall-through."""

    reason: str


@dataclass(frozen=True)
class AbandonDecision:
    """An explicit, logged decision to stop working a target after a
    kernel or audit rejection."""

    reason: str


def _evidence_dict(evidence) -> dict:
    return asdict(evidence)


class TargetQueue:
    """An evidence-driven queue of targets, one state machine per
    ``target_id``, persisted as an append-only JSONL event log at
    ``log_path``.
    """

    def __init__(self, log_path: Union[str, Path]):
        self.log_path = Path(log_path)
        self._events: list[dict] = []
        if self.log_path.exists():
            self._events = self._read_log(self.log_path)
        self._state: dict[str, State] = self._fold(self._events)
        self._candidate: dict[str, str] = self._fold_candidates(self._events)

    # -- construction / persistence ---------------------------------

    @staticmethod
    def _read_log(path: Path) -> list[dict]:
        events = []
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line:
                    events.append(json.loads(line))
        return events

    @staticmethod
    def _fold(events: list[dict]) -> dict[str, State]:
        """Rebuild target_id -> current State purely by folding the log.
        This is the only way current state is ever computed — there is
        no separate mutable "state table" that could drift from the log.
        """
        state: dict[str, State] = {}
        for event in events:
            state[event["target_id"]] = State(event["to_state"])
        return state

    @staticmethod
    def _fold_candidates(events: list[dict]) -> dict[str, str]:
        """Rebuild target_id -> the candidate its evidence is currently
        bound to, by the same fold-the-log discipline `_fold` uses. A new
        `record_candidate` rebinds; nothing else changes the binding, so
        every artifact between one candidate event and the next has to be
        about that candidate."""
        candidates: dict[str, str] = {}
        for event in events:
            if event["evidence_kind"] == "candidate_artifact":
                candidates[event["target_id"]] = event["evidence"]["candidate_id"]
        return candidates

    @classmethod
    def replay(cls, log_path: Union[str, Path]) -> "TargetQueue":
        """Rebuild a queue's current state entirely by folding an
        existing log file. Equivalent to the constructor, exposed under
        an explicit name for callers/tests that want to state the
        "derive state from evidence" property directly."""
        return cls(log_path)

    def _append(self, target_id: str, from_state: Optional[State], to_state: State,
                evidence_kind: str, evidence: dict) -> None:
        event = {
            "target_id": target_id,
            "from_state": from_state.value if from_state is not None else None,
            "to_state": to_state.value,
            "evidence_kind": evidence_kind,
            "evidence": evidence,
            "recorded_at": now_iso(),
        }
        # Append to the on-disk log first (durability), then update the
        # in-memory projection — mirroring "state is derived from
        # evidence, not asserted": the event is the fact, the dict below
        # is just a cache of the fold.
        with open(self.log_path, "a", encoding="utf-8") as f:
            f.write(json.dumps(event, sort_keys=True) + "\n")
            f.flush()
            os.fsync(f.fileno())
        self._events.append(event)
        self._state[target_id] = to_state

    # -- queries -------------------------------------------------------

    def state_of(self, target_id: str) -> Optional[State]:
        return self._state.get(target_id)

    def active_candidate(self, target_id: str) -> Optional[str]:
        """The candidate id every downstream artifact for this target
        must be about, or None if no candidate has been recorded yet."""
        return self._candidate.get(target_id)

    def events_for(self, target_id: str) -> list[dict]:
        return [e for e in self._events if e["target_id"] == target_id]

    @property
    def all_states(self) -> dict[str, State]:
        return dict(self._state)

    # -- transitions -----------------------------------------------------

    def _require_state(self, target_id: str, *expected: State) -> State:
        current = self._state.get(target_id)
        if current not in expected:
            raise InvalidTransition(
                f"target {target_id!r} is in state {current!r}, expected one of "
                f"{[s.value for s in expected]}"
            )
        return current

    def _require_active_candidate(self, target_id: str, candidate_id: str, what: str) -> None:
        """Refuse an artifact about a candidate this target's evidence
        is not bound to. Without this, the public API reaches `accepted`
        with a candidate artifact for c1, a kernel receipt for c2 and an
        audit verdict for c3 — three artifacts, no two of them about the
        same thing, and a state nothing produced the evidence for."""
        active = self._candidate.get(target_id)
        if active is None:
            raise InvalidTransition(
                f"target {target_id!r} has no recorded candidate, so there is nothing for "
                f"this {what} to be evidence about"
            )
        if candidate_id != active:
            raise InvalidTransition(
                f"{what}.candidate_id {candidate_id!r} is not the candidate this target's "
                f"evidence is bound to ({active!r}); evidence about another candidate cannot "
                f"advance this one's state"
            )

    @staticmethod
    def _require_type(evidence, expected_type: type) -> None:
        if not isinstance(evidence, expected_type):
            raise InvalidTransition(
                f"transition requires evidence of type {expected_type.__name__}, "
                f"got {type(evidence).__name__}"
            )

    def enqueue(self, target_id: str, entry: TargetEntry) -> State:
        """Initial transition: None -> queued. Requires a TargetEntry
        (ARCHITECTURE.md §1's provenance contract)."""
        self._require_type(entry, TargetEntry)
        if target_id in self._state:
            raise InvalidTransition(f"target {target_id!r} is already enqueued")
        self._append(target_id, None, State.QUEUED, "target_entry", _evidence_dict(entry))
        return State.QUEUED

    def start_attempt(self, target_id: str, evidence: AttemptStarted) -> State:
        """queued -> attempting."""
        self._require_type(evidence, AttemptStarted)
        self._require_state(target_id, State.QUEUED)
        self._append(target_id, State.QUEUED, State.ATTEMPTING, "attempt_started",
                     _evidence_dict(evidence))
        return State.ATTEMPTING

    def record_candidate(self, target_id: str, evidence: CandidateArtifact) -> State:
        """attempting -> candidate-produced."""
        self._require_type(evidence, CandidateArtifact)
        self._require_state(target_id, State.ATTEMPTING)
        self._append(target_id, State.ATTEMPTING, State.CANDIDATE_PRODUCED,
                     "candidate_artifact", _evidence_dict(evidence))
        # Bind this target's evidence to this candidate: every artifact
        # from here to the next candidate has to be about it.
        self._candidate[target_id] = evidence.candidate_id
        return State.CANDIDATE_PRODUCED

    def record_no_candidate(self, target_id: str, evidence: NoCandidateProduced,
                             *, abandon: bool = False) -> State:
        """attempting -> queued (retry) | abandoned, on the prover's
        explicit "no candidate" result (ARCHITECTURE.md §3)."""
        self._require_type(evidence, NoCandidateProduced)
        self._require_state(target_id, State.ATTEMPTING)
        to_state = State.ABANDONED if abandon else State.QUEUED
        self._append(target_id, State.ATTEMPTING, to_state, "no_candidate_produced",
                     _evidence_dict(evidence))
        return to_state

    def record_kernel_receipt(self, target_id: str, receipt: Receipt) -> State:
        """candidate-produced -> kernel-checked | kernel-rejected |
        checker-error.

        Accepts a receipt from either checker kind — ARCHITECTURE.md §4
        treats a proof kernel and a bounded model checker as
        interchangeable *slots* in the pipeline (though not
        interchangeable in what their receipts may claim); this queue
        state name follows the diagram's literal wording, not a
        restriction to Lean specifically.

        Each of the receipt's three verdicts gets its own state. In
        particular `error` is NOT a rejection: the checker produced no
        verdict, so nothing is known about this candidate, and routing it
        as a refutation would requeue for a different candidate to a
        question that was never answered.
        """
        self._require_type(receipt, Receipt)
        self._require_state(target_id, State.CANDIDATE_PRODUCED)
        if receipt.target_id != target_id:
            raise InvalidTransition(
                f"receipt.target_id {receipt.target_id!r} does not match {target_id!r}"
            )
        self._require_active_candidate(target_id, receipt.candidate_id, "receipt")
        if receipt.verdict == "accepted":
            to_state = State.KERNEL_CHECKED
        elif receipt.verdict == "error":
            to_state = State.CHECKER_ERROR
        else:
            to_state = State.KERNEL_REJECTED
        self._append(target_id, State.CANDIDATE_PRODUCED, to_state, "kernel_receipt",
                     receipt.to_dict())
        return to_state

    def requeue_from_kernel_rejected(self, target_id: str, decision: RequeueDecision) -> State:
        self._require_type(decision, RequeueDecision)
        self._require_state(target_id, State.KERNEL_REJECTED)
        self._append(target_id, State.KERNEL_REJECTED, State.QUEUED, "requeue_decision",
                     _evidence_dict(decision))
        return State.QUEUED

    def abandon_from_kernel_rejected(self, target_id: str, decision: AbandonDecision) -> State:
        self._require_type(decision, AbandonDecision)
        self._require_state(target_id, State.KERNEL_REJECTED)
        self._append(target_id, State.KERNEL_REJECTED, State.ABANDONED, "abandon_decision",
                     _evidence_dict(decision))
        return State.ABANDONED

    def requeue_from_checker_error(self, target_id: str, decision: RequeueDecision) -> State:
        """checker-error -> queued. The retry a tool error calls for is
        "run the checker again, with more resources or a different
        configuration" — the candidate is unchanged and unjudged, which
        is exactly what distinguishes this from
        `requeue_from_kernel_rejected`."""
        self._require_type(decision, RequeueDecision)
        self._require_state(target_id, State.CHECKER_ERROR)
        self._append(target_id, State.CHECKER_ERROR, State.QUEUED, "requeue_decision",
                     _evidence_dict(decision))
        return State.QUEUED

    def abandon_from_checker_error(self, target_id: str, decision: AbandonDecision) -> State:
        """checker-error -> abandoned: the honest terminal state for
        "this clause is out of scope for this tool", which is a fact
        about the tool, never a refutation of the candidate."""
        self._require_type(decision, AbandonDecision)
        self._require_state(target_id, State.CHECKER_ERROR)
        self._append(target_id, State.CHECKER_ERROR, State.ABANDONED, "abandon_decision",
                     _evidence_dict(decision))
        return State.ABANDONED

    def record_audit(self, target_id: str, verdict: AuditVerdict) -> State:
        """kernel-checked -> audited -> accepted | audit-rejected.

        Recorded as two evidence-consuming hops from the same audit
        verdict artifact — see the module docstring for why.
        """
        self._require_type(verdict, AuditVerdict)
        self._require_state(target_id, State.KERNEL_CHECKED)
        if verdict.target_id != target_id:
            raise InvalidTransition(
                f"audit verdict.target_id {verdict.target_id!r} does not match {target_id!r}"
            )
        self._require_active_candidate(target_id, verdict.candidate_id, "audit verdict")
        doc = verdict.to_dict()
        self._append(target_id, State.KERNEL_CHECKED, State.AUDITED, "audit_verdict", doc)
        to_state = State.ACCEPTED if verdict.verdict == "pass" else State.AUDIT_REJECTED
        self._append(target_id, State.AUDITED, to_state, "audit_verdict", doc)
        return to_state

    def requeue_from_audit_rejected(self, target_id: str, decision: RequeueDecision) -> State:
        self._require_type(decision, RequeueDecision)
        self._require_state(target_id, State.AUDIT_REJECTED)
        self._append(target_id, State.AUDIT_REJECTED, State.QUEUED, "requeue_decision",
                     _evidence_dict(decision))
        return State.QUEUED

    def abandon_from_audit_rejected(self, target_id: str, decision: AbandonDecision) -> State:
        self._require_type(decision, AbandonDecision)
        self._require_state(target_id, State.AUDIT_REJECTED)
        self._append(target_id, State.AUDIT_REJECTED, State.ABANDONED, "abandon_decision",
                     _evidence_dict(decision))
        return State.ABANDONED
