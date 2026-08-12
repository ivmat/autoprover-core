"""Receipt and audit-verdict data model (ARCHITECTURE.md §7, INTERFACES.md).

Every verification run — kernel or audit — must emit a structured,
machine-readable result artifact, never a log message meant for a human to
interpret. This module gives that artifact a concrete Python shape (a
frozen dataclass), a schema-checked JSON encoding, and an atomic-write
primitive so a consumer never observes a partially-written result
(INTERFACES.md property 4).

Reading a receipt or audit verdict that fails schema validation is a hard
error — this module never silently coerces a malformed document into
"looks close enough".
"""

from __future__ import annotations

import json
import os
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional, Union

from .jsonschema_min import SchemaValidationError, validate as _validate_schema

__all__ = [
    "RECEIPT_SCHEMA_VERSION",
    "AUDIT_SCHEMA_VERSION",
    "Checker",
    "Certificate",
    "Obligation",
    "Receipt",
    "AuditVerdict",
    "now_iso",
    "load_schema",
    "receipt_schema",
    "audit_schema",
    "validate_receipt_dict",
    "validate_audit_dict",
    "atomic_write_json",
    "write_receipt",
    "write_audit",
    "load_receipt",
    "load_audit",
]

RECEIPT_SCHEMA_VERSION = "1.0.0"
AUDIT_SCHEMA_VERSION = "1.0.0"

_SCHEMA_DIR = Path(__file__).resolve().parent.parent / "schema"

_KERNEL_KINDS = ("kernel", "model-checker")
_VERDICTS = ("accepted", "rejected", "error")
_OBLIGATION_STATUSES = ("held", "vacuous", "not-exercised", "failed")
_AUDIT_VERDICTS = ("pass", "fail")
_AUDIT_FAILURE_REASONS = (
    "vacuous-precondition",
    "name-content-mismatch",
    "scope-narrower-than-claimed",
)


def now_iso() -> str:
    """UTC timestamp in ISO-8601, used for every artifact's `produced_at`."""
    return datetime.now(timezone.utc).isoformat()


def load_schema(name: str) -> dict:
    """Load one of the versioned JSON Schemas shipped under
    ``reference/schema/``. Not cached deliberately — this is a reference
    implementation read a handful of times per run, not a hot path."""
    path = _SCHEMA_DIR / name
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def receipt_schema() -> dict:
    return load_schema("receipt.schema.json")


def audit_schema() -> dict:
    return load_schema("audit.schema.json")


def validate_receipt_dict(doc: dict) -> None:
    """Raise SchemaValidationError if ``doc`` is not a well-formed receipt."""
    _validate_schema(doc, receipt_schema())


def validate_audit_dict(doc: dict) -> None:
    """Raise SchemaValidationError if ``doc`` is not a well-formed audit verdict."""
    _validate_schema(doc, audit_schema())


# --------------------------------------------------------------------------
# Data model
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Checker:
    """Identifies the sound oracle that produced a receipt.

    ``kind`` distinguishes a proof kernel from a bounded model checker
    (ARCHITECTURE.md §4) — the two are not interchangeable oracles, and
    the receipt schema enforces different required/forbidden fields
    depending on which this is.
    """

    kind: str  # "kernel" | "model-checker"
    name: str
    version: str

    def __post_init__(self) -> None:
        if self.kind not in _KERNEL_KINDS:
            raise ValueError(f"checker.kind must be one of {_KERNEL_KINDS}, got {self.kind!r}")

    def to_dict(self) -> dict:
        return {"kind": self.kind, "name": self.name, "version": self.version}

    @classmethod
    def from_dict(cls, d: dict) -> "Checker":
        return cls(kind=d["kind"], name=d["name"], version=d["version"])


@dataclass(frozen=True)
class Certificate:
    """A re-runnable reference to a kernel's accepted proof — the checked
    file plus the toolchain identity needed to reproduce the check. Only
    ever attached to a kernel receipt with verdict == 'accepted'."""

    checked_file: str
    toolchain_id: str

    def to_dict(self) -> dict:
        return {"checked_file": self.checked_file, "toolchain_id": self.toolchain_id}

    @classmethod
    def from_dict(cls, d: dict) -> "Certificate":
        return cls(checked_file=d["checked_file"], toolchain_id=d["toolchain_id"])


@dataclass(frozen=True)
class Obligation:
    """One entry in a receipt's exhaustive obligation bucket
    (INTERFACES.md property 2). `status` must distinguish "held" from
    "vacuous" / "not-exercised" — an obligation that was never really
    tested must never look identical to one that held."""

    id: str
    status: str  # "held" | "vacuous" | "not-exercised" | "failed"

    def __post_init__(self) -> None:
        if self.status not in _OBLIGATION_STATUSES:
            raise ValueError(
                f"obligation.status must be one of {_OBLIGATION_STATUSES}, got {self.status!r}"
            )

    def to_dict(self) -> dict:
        return {"id": self.id, "status": self.status}

    @classmethod
    def from_dict(cls, d: dict) -> "Obligation":
        return cls(id=d["id"], status=d["status"])


@dataclass(frozen=True)
class Receipt:
    """A verification receipt (ARCHITECTURE.md §4, §7). Construct via the
    kernel gate (`kernel_gate.py`) rather than by hand where possible —
    the invariants below (certificate iff kernel+accepted, harness/bound/
    env_assumptions iff model-checker) are exactly what the schema
    enforces, and this constructor enforces them too so an in-memory
    Receipt can never itself be malformed before it is even serialized.
    """

    target_id: str
    candidate_id: str
    checker: Checker
    verdict: str  # "accepted" | "rejected" | "error"
    certificate: Optional[Certificate]
    harness: Optional[str]
    bound: Optional[Union[str, float, int]]
    env_assumptions: Optional[str]
    obligations: tuple[Obligation, ...]
    produced_at: str
    schema_version: str = RECEIPT_SCHEMA_VERSION

    def __post_init__(self) -> None:
        if self.verdict not in _VERDICTS:
            raise ValueError(f"verdict must be one of {_VERDICTS}, got {self.verdict!r}")

        if self.checker.kind == "kernel":
            if self.harness is not None or self.bound is not None or self.env_assumptions is not None:
                raise ValueError(
                    "a kernel receipt must not carry harness/bound/env_assumptions "
                    "(ARCHITECTURE.md §4: a proof kernel's verdict is not relative to a harness)"
                )
            if self.verdict == "accepted" and self.certificate is None:
                raise ValueError("a kernel receipt with verdict 'accepted' requires a certificate")
            if self.verdict != "accepted" and self.certificate is not None:
                raise ValueError("certificate must be null unless verdict == 'accepted'")
        else:  # model-checker
            if self.certificate is not None:
                raise ValueError(
                    "a model-checker receipt must not carry a certificate — its verdict is "
                    "only valid relative to its harness/bound/env_assumptions, never portable "
                    "the way a kernel's re-runnable proof object is (ARCHITECTURE.md §4)"
                )
            if not self.harness or self.bound is None or not self.env_assumptions:
                raise ValueError(
                    "a model-checker receipt requires non-null harness, bound, and env_assumptions"
                )

    def to_dict(self) -> dict:
        return {
            "schema_version": self.schema_version,
            "target_id": self.target_id,
            "candidate_id": self.candidate_id,
            "checker": self.checker.to_dict(),
            "verdict": self.verdict,
            "certificate": self.certificate.to_dict() if self.certificate else None,
            "harness": self.harness,
            "bound": self.bound,
            "env_assumptions": self.env_assumptions,
            "obligations": [o.to_dict() for o in self.obligations],
            "produced_at": self.produced_at,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Receipt":
        """Construct a Receipt from a plain dict. Callers that read
        receipts from disk should use `load_receipt`, which validates
        against the schema first; this constructor additionally enforces
        the dataclass-level invariants in __post_init__."""
        return cls(
            schema_version=d["schema_version"],
            target_id=d["target_id"],
            candidate_id=d["candidate_id"],
            checker=Checker.from_dict(d["checker"]),
            verdict=d["verdict"],
            certificate=Certificate.from_dict(d["certificate"]) if d.get("certificate") else None,
            harness=d.get("harness"),
            bound=d.get("bound"),
            env_assumptions=d.get("env_assumptions"),
            obligations=tuple(Obligation.from_dict(o) for o in d["obligations"]),
            produced_at=d["produced_at"],
        )


@dataclass(frozen=True)
class AuditVerdict:
    """A semantic audit verdict (ARCHITECTURE.md §5, §7). `failure_reason`
    is null exactly when `verdict == "pass"` — never inferred from an
    absent key (INTERFACES.md property 3)."""

    target_id: str
    candidate_id: str
    verdict: str  # "pass" | "fail"
    failure_reason: Optional[str]
    details: dict
    produced_at: str
    schema_version: str = AUDIT_SCHEMA_VERSION

    def __post_init__(self) -> None:
        if self.verdict not in _AUDIT_VERDICTS:
            raise ValueError(f"verdict must be one of {_AUDIT_VERDICTS}, got {self.verdict!r}")
        if self.verdict == "pass" and self.failure_reason is not None:
            raise ValueError("failure_reason must be null when verdict == 'pass'")
        if self.verdict == "fail" and self.failure_reason not in _AUDIT_FAILURE_REASONS:
            raise ValueError(
                f"failure_reason must be one of {_AUDIT_FAILURE_REASONS} when verdict == 'fail', "
                f"got {self.failure_reason!r}"
            )

    def to_dict(self) -> dict:
        return {
            "schema_version": self.schema_version,
            "target_id": self.target_id,
            "candidate_id": self.candidate_id,
            "verdict": self.verdict,
            "failure_reason": self.failure_reason,
            "details": self.details,
            "produced_at": self.produced_at,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "AuditVerdict":
        return cls(
            schema_version=d["schema_version"],
            target_id=d["target_id"],
            candidate_id=d["candidate_id"],
            verdict=d["verdict"],
            failure_reason=d.get("failure_reason"),
            details=d["details"],
            produced_at=d["produced_at"],
        )


# --------------------------------------------------------------------------
# Atomic, schema-checked I/O (INTERFACES.md properties 1, 4, 5)
# --------------------------------------------------------------------------


def atomic_write_json(path: Union[str, Path], obj: dict) -> None:
    """Write ``obj`` as JSON to ``path`` such that the file is never
    observable in a partially-written state: write to a temp file in the
    same directory, flush + fsync, then `os.replace` (atomic on POSIX and
    Windows) into the final name. If a file with the expected name
    exists, it is the finished result (INTERFACES.md property 4)."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=str(path.parent)
    )
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(obj, f, indent=2, sort_keys=True)
            f.write("\n")
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_name, path)
    except BaseException:
        # Never leave a stray temp file behind on failure, and never leave
        # a partial file at the final path (we never wrote to it directly).
        if os.path.exists(tmp_name):
            os.remove(tmp_name)
        raise


def write_receipt(path: Union[str, Path], receipt: Receipt) -> None:
    """Validate then atomically write a receipt. Validation happens
    before any bytes touch disk — a malformed receipt is never written
    at all, partially or otherwise."""
    doc = receipt.to_dict()
    validate_receipt_dict(doc)
    atomic_write_json(path, doc)


def write_audit(path: Union[str, Path], verdict: AuditVerdict) -> None:
    doc = verdict.to_dict()
    validate_audit_dict(doc)
    atomic_write_json(path, doc)


def load_receipt(path: Union[str, Path]) -> Receipt:
    """Read and validate a receipt from disk. Raises SchemaValidationError
    (schema-invalid) or KeyError/ValueError (structurally-invalid) rather
    than ever silently coercing a malformed document into a Receipt."""
    with open(path, "r", encoding="utf-8") as f:
        doc = json.load(f)
    validate_receipt_dict(doc)
    return Receipt.from_dict(doc)


def load_audit(path: Union[str, Path]) -> AuditVerdict:
    with open(path, "r", encoding="utf-8") as f:
        doc = json.load(f)
    validate_audit_dict(doc)
    return AuditVerdict.from_dict(doc)
