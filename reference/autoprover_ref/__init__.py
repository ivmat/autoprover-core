"""autoprover_ref: a reference implementation of the pipeline pattern
described in ``docs/ARCHITECTURE.md`` and ``docs/INTERFACES.md``.

Standard-library only. See ``reference/README.md`` for the mapping from
each module here to the architecture document's sections, and for the
"reference implementation, not a product" scope note.

Public API re-exports the pieces most callers need; internal modules
remain individually importable for anything more specific.
"""

from .audit import TargetProvenance, check_name_content, check_scope, check_vacuity, run_audit
from .kernel_gate import CheckerCommand, CheckerResult, KernelGate, lean_checker_command
from .model_checker import (
    ExplorationResult,
    ModelObligation,
    ObligationCheckResult,
    TransitionSystem,
    check_obligations,
    explore,
    model_checker_command,
)
from .pipeline import Pipeline, PipelineResult
from .queue import (
    AbandonDecision,
    AttemptStarted,
    CandidateArtifact,
    InvalidTransition,
    NoCandidateProduced,
    QueueError,
    RequeueDecision,
    State,
    TargetEntry,
    TargetQueue,
)
from .ratchet import AcceptedEntry, BlockingEvent, Ratchet, RatchetError, RemovalEvent
from .receipts import (
    AUDIT_SCHEMA_VERSION,
    RECEIPT_SCHEMA_VERSION,
    AuditVerdict,
    Certificate,
    Checker,
    Obligation,
    Receipt,
    atomic_write_json,
    load_audit,
    load_receipt,
    now_iso,
    write_audit,
    write_receipt,
)

__all__ = [
    # audit
    "TargetProvenance",
    "check_name_content",
    "check_scope",
    "check_vacuity",
    "run_audit",
    # kernel_gate
    "CheckerCommand",
    "CheckerResult",
    "KernelGate",
    "lean_checker_command",
    # model_checker
    "ExplorationResult",
    "ModelObligation",
    "ObligationCheckResult",
    "TransitionSystem",
    "check_obligations",
    "explore",
    "model_checker_command",
    # pipeline
    "Pipeline",
    "PipelineResult",
    # queue
    "AbandonDecision",
    "AttemptStarted",
    "CandidateArtifact",
    "InvalidTransition",
    "NoCandidateProduced",
    "QueueError",
    "RequeueDecision",
    "State",
    "TargetEntry",
    "TargetQueue",
    # ratchet
    "AcceptedEntry",
    "BlockingEvent",
    "Ratchet",
    "RatchetError",
    "RemovalEvent",
    # receipts
    "AUDIT_SCHEMA_VERSION",
    "RECEIPT_SCHEMA_VERSION",
    "AuditVerdict",
    "Certificate",
    "Checker",
    "Obligation",
    "Receipt",
    "atomic_write_json",
    "load_audit",
    "load_receipt",
    "now_iso",
    "write_audit",
    "write_receipt",
]
