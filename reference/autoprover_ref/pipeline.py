"""Pipeline glue: drives one target end-to-end through
queue -> kernel_gate -> audit -> ratchet (ARCHITECTURE.md §§2-7),
emitting a receipt or audit verdict at every boundary and advancing
queue state only on the evidence those artifacts constitute.

This module deliberately does not include an LLM prover. ARCHITECTURE.md
§3 describes the prover as "the generative, unreliable part of the
system by design" — an LLM call is out of scope for a standard-library-
only reference package, and nothing about soundness in this pipeline
depends on how the candidate was produced (that is the entire point of
§3's contract: a candidate is only ever an *input* to the kernel gate,
never a verdict). `Pipeline.run_target` takes an already-produced
candidate file, exactly as if a prover component upstream had just
finished; wiring in a real prover means calling `queue.record_candidate`
(or `queue.record_no_candidate`) yourself before invoking
`Pipeline.run_target`, or extending this module with a `ProverCommand`
seam analogous to `kernel_gate.CheckerCommand`.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Sequence, Union

from .audit import TargetProvenance, run_audit
from .kernel_gate import KernelGate
from .queue import (
    AttemptStarted,
    CandidateArtifact,
    RequeueDecision,
    State,
    TargetEntry,
    TargetQueue,
)
from .ratchet import AcceptedEntry, Ratchet
from .receipts import AuditVerdict, Receipt, write_audit, write_receipt

__all__ = ["PipelineResult", "Pipeline"]


@dataclass(frozen=True)
class PipelineResult:
    target_id: str
    candidate_id: str
    final_state: str
    kernel_receipt: Optional[Receipt]
    audit_verdict: Optional[AuditVerdict]
    accepted_entry: Optional[AcceptedEntry]


class Pipeline:
    """Glue object: owns a queue, a kernel gate, and a ratchet, and
    drives a single target through all of them, writing a receipt (and,
    if reached, an audit verdict) to `receipts_dir` at each boundary.
    """

    def __init__(
        self,
        *,
        queue: TargetQueue,
        gate: KernelGate,
        ratchet: Ratchet,
        receipts_dir: Union[str, Path],
    ):
        self.queue = queue
        self.gate = gate
        self.ratchet = ratchet
        self.receipts_dir = Path(receipts_dir)

    def run_target(
        self,
        *,
        target_id: str,
        candidate_id: str,
        candidate_file: Union[str, Path],
        provenance: TargetProvenance,
        attempt_id: Optional[str] = None,
        prover_name: str = "external",
        obligation_ids: Sequence[str] = (),
        harness: Optional[str] = None,
        bound=None,
        env_assumptions: Optional[str] = None,
    ) -> PipelineResult:
        """Drive `target_id` from wherever it currently is (or from
        not-yet-enqueued) through the kernel gate and audit layer, and
        into the ratchet on full acceptance. Every boundary crossed
        writes a schema-validated receipt/verdict to `receipts_dir`
        before the queue state that depends on it is advanced.
        """
        candidate_file = Path(candidate_file)

        if self.queue.state_of(target_id) is None:
            self.queue.enqueue(
                target_id,
                TargetEntry(statement=provenance.statement_text, provenance={
                    "source": provenance.source,
                    "claim_keywords": list(provenance.claim_keywords),
                    "preconditions": list(provenance.preconditions),
                    "non_vacuity_witness": provenance.non_vacuity_witness,
                    "claimed_scope": provenance.claimed_scope,
                }),
            )

        self.queue.start_attempt(
            target_id, AttemptStarted(attempt_id=attempt_id or candidate_id, prover_name=prover_name)
        )
        self.queue.record_candidate(
            target_id, CandidateArtifact(candidate_id=candidate_id, artifact_path=str(candidate_file))
        )

        receipt = self.gate.check(
            target_id=target_id,
            candidate_id=candidate_id,
            candidate_file=candidate_file,
            obligation_ids=obligation_ids,
            harness=harness,
            bound=bound,
            env_assumptions=env_assumptions,
        )
        write_receipt(self.receipts_dir / f"{target_id}.{candidate_id}.kernel.json", receipt)
        state = self.queue.record_kernel_receipt(target_id, receipt)

        if state == State.KERNEL_REJECTED:
            state = self.queue.requeue_from_kernel_rejected(
                target_id, RequeueDecision(reason="kernel rejected candidate; eligible for retry")
            )
            return PipelineResult(
                target_id=target_id,
                candidate_id=candidate_id,
                final_state=state.value,
                kernel_receipt=receipt,
                audit_verdict=None,
                accepted_entry=None,
            )

        audit_verdict = run_audit(target_id, candidate_id, provenance)
        write_audit(self.receipts_dir / f"{target_id}.{candidate_id}.audit.json", audit_verdict)
        state = self.queue.record_audit(target_id, audit_verdict)

        if state == State.AUDIT_REJECTED:
            state = self.queue.requeue_from_audit_rejected(
                target_id,
                RequeueDecision(reason=f"audit failed: {audit_verdict.failure_reason}"),
            )
            return PipelineResult(
                target_id=target_id,
                candidate_id=candidate_id,
                final_state=state.value,
                kernel_receipt=receipt,
                audit_verdict=audit_verdict,
                accepted_entry=None,
            )

        entry = self.ratchet.accept(receipt, audit_verdict)
        return PipelineResult(
            target_id=target_id,
            candidate_id=candidate_id,
            final_state=State.ACCEPTED.value,
            kernel_receipt=receipt,
            audit_verdict=audit_verdict,
            accepted_entry=entry,
        )
