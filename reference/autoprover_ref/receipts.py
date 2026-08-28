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
    "RECEIPT_SCHEMA_VERSIONS",
    "AUDIT_SCHEMA_VERSION",
    "AUDIT_SCHEMA_VERSIONS",
    "Checker",
    "Certificate",
    "Tool",
    "Dependency",
    "Toolchain",
    "Subject",
    "Coverage",
    "Control",
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

# The CURRENT receipt format. 2.0.0 is a breaking change over 1.0.0 — it
# adds required objects (`toolchain`, `subject`, `claim_id`,
# `failure_kind`, `control`) and a per-obligation `coverage` block — so it
# ships as its own schema file rather than widening the old one, and a
# 1.0.0 document is validated against the 1.0.0 schema exactly as before
# (INTERFACES.md property 5). Writers emit the current version; readers
# accept every published version and dispatch on the document's own
# `schema_version`, so an old receipt on disk stays readable and can never
# be silently re-interpreted as a new one.
RECEIPT_SCHEMA_VERSION = "2.0.0"
RECEIPT_SCHEMA_VERSIONS = ("1.0.0", "2.0.0")

# 1.1.0 adds one failure reason (`unexercised-hypothesis`) to the audit
# verdict's closed enum; 1.2.0 adds one more (`missing-control`). Each
# changes nothing else. A new permitted value in a closed enum is a
# change a consumer must be able to notice — a reader built for 1.0.0
# would meet a code it cannot branch on — so it travels with a version
# bump rather than silently widening the contract (INTERFACES.md
# property 5). The schema still accepts every older version and forbids
# each document from carrying a code its own version never defined; the
# receipt schema is versioned separately and is unaffected.
AUDIT_SCHEMA_VERSION = "1.2.0"
AUDIT_SCHEMA_VERSIONS = ("1.0.0", "1.1.0", "1.2.0")

_SCHEMA_DIR = Path(__file__).resolve().parent.parent / "schema"

# 1.0.0 keeps its original, unversioned filename: it is the path already
# published to consumers, and renaming it would break them for no gain.
# Every version from 2.0.0 on ships as `receipt.schema-<version>.json`.
_RECEIPT_SCHEMA_FILES = {
    "1.0.0": "receipt.schema.json",
    "2.0.0": "receipt.schema-2.0.0.json",
}

_KERNEL_KINDS = ("kernel", "model-checker")
_VERDICTS = ("accepted", "rejected", "error")
_FAILURE_KINDS = ("timeout", "oom", "unsupported-construct", "tool-error")
_CONTROL_KINDS = ("ablation", "mutation", "planted-twin")
_CONTROL_EXPECTATIONS = ("red", "green", "sat")
_OBLIGATION_STATUSES = ("held", "vacuous", "not-exercised", "failed")
_AUDIT_VERDICTS = ("pass", "fail")
_AUDIT_FAILURE_REASONS = (
    "vacuous-precondition",
    "unexercised-hypothesis",
    "name-content-mismatch",
    "scope-narrower-than-claimed",
    "missing-control",
)

# Which reasons each published audit-schema version defines. A document
# may never carry a code its own version did not have — the schema says
# so in its allOf blocks, and the constructor says so here, because a
# verdict that cannot be written is better refused where it is built
# than where it is serialized.
_AUDIT_REASONS_BY_VERSION = {
    "1.0.0": (
        "vacuous-precondition",
        "name-content-mismatch",
        "scope-narrower-than-claimed",
    ),
    "1.1.0": (
        "vacuous-precondition",
        "unexercised-hypothesis",
        "name-content-mismatch",
        "scope-narrower-than-claimed",
    ),
    "1.2.0": _AUDIT_FAILURE_REASONS,
}


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


def receipt_schema(version: str = RECEIPT_SCHEMA_VERSION) -> dict:
    """Load the receipt schema for ``version`` (default: the current
    one). Asking for a version this package does not ship is an error,
    never a silent fallback to the newest schema — validating a document
    against a schema it did not declare is exactly the over-interpretation
    versioning exists to prevent."""
    try:
        filename = _RECEIPT_SCHEMA_FILES[version]
    except KeyError:
        raise ValueError(
            f"no receipt schema shipped for version {version!r}; "
            f"known versions: {RECEIPT_SCHEMA_VERSIONS}"
        ) from None
    return load_schema(filename)


def audit_schema() -> dict:
    return load_schema("audit.schema.json")


def validate_receipt_dict(doc: dict) -> None:
    """Raise SchemaValidationError if ``doc`` is not a well-formed
    receipt.

    The document's own ``schema_version`` selects the schema it is judged
    against, so a 1.0.0 receipt written years ago still validates as
    1.0.0 and is never held to 2.0.0's requirements — nor allowed to
    borrow 2.0.0's fields. A document with a missing or unknown version
    is rejected outright rather than being guessed at.
    """
    if not isinstance(doc, dict):
        raise SchemaValidationError([f"$: expected a receipt object, got {type(doc).__name__}"])
    version = doc.get("schema_version")
    if version not in _RECEIPT_SCHEMA_FILES:
        raise SchemaValidationError([
            f"$.schema_version: {version!r} is not a published receipt schema version "
            f"{RECEIPT_SCHEMA_VERSIONS}; refusing to guess which format this document is in"
        ])
    _validate_schema(doc, receipt_schema(version))


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
class Tool:
    """The exact build of the verification tool (receipt 2.0.0).

    ``commit_or_version`` is one field on purpose: "which build produced
    this verdict" has one answer, and offering two fields invites
    recording the release while omitting the build that was actually run.
    A commit hash where one exists, a release version otherwise.
    """

    name: str
    commit_or_version: str

    def __post_init__(self) -> None:
        if not self.name or not self.commit_or_version:
            raise ValueError("toolchain.tool requires a non-empty name and commit_or_version")

    def to_dict(self) -> dict:
        return {"name": self.name, "commit_or_version": self.commit_or_version}

    @classmethod
    def from_dict(cls, d: dict) -> "Tool":
        return cls(name=d["name"], commit_or_version=d["commit_or_version"])


@dataclass(frozen=True)
class Dependency:
    """One version-bearing component whose identity can change the
    verdict (a solver, a backend, a standard library)."""

    name: str
    version: str

    def __post_init__(self) -> None:
        if not self.name or not self.version:
            raise ValueError("toolchain.dependencies entries require a non-empty name and version")

    def to_dict(self) -> dict:
        return {"name": self.name, "version": self.version}

    @classmethod
    def from_dict(cls, d: dict) -> "Dependency":
        return cls(name=d["name"], version=d["version"])


@dataclass(frozen=True)
class Toolchain:
    """Build identity at commit granularity, plus the semantics in force
    (receipt 2.0.0).

    A verdict is relative to the exact build that produced it AND to the
    flags/features that were enabled: a flag that switches an unstable
    semantics on or off changes what was proved, not merely how fast.
    1.0.0 recorded a single `checker.version` string, which cannot
    distinguish two builds of one release and cannot record semantics at
    all — a verdict that cannot be attributed to a build is not evidence.

    `features` is nullable, and the two values are NOT the same claim: an
    (even empty) list means the tool has a feature-selection concept and
    exactly these were on; None means the tool has no such concept.
    Neither ever means "we didn't write it down" (INTERFACES.md
    property 3).
    """

    tool: Tool
    dependencies: tuple[Dependency, ...] = ()
    flags: tuple[str, ...] = ()
    features: Optional[tuple[str, ...]] = None

    def to_dict(self) -> dict:
        return {
            "tool": self.tool.to_dict(),
            "dependencies": [d.to_dict() for d in self.dependencies],
            "flags": list(self.flags),
            "features": None if self.features is None else list(self.features),
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Toolchain":
        features = d["features"]
        return cls(
            tool=Tool.from_dict(d["tool"]),
            dependencies=tuple(Dependency.from_dict(x) for x in d["dependencies"]),
            flags=tuple(d["flags"]),
            features=None if features is None else tuple(features),
        )


@dataclass(frozen=True)
class Subject:
    """What the verdict is ABOUT: repository, commit, and optionally the
    sub-unit within it (receipt 2.0.0).

    Without this a receipt store cannot hold two subjects at once, and a
    verdict cannot be re-attached to the source state it was measured on.
    `unit` is nullable and explicitly means "the whole subject at that
    commit, not a sub-unit" — never "unknown".
    """

    repo: str
    commit: str
    unit: Optional[str] = None

    def __post_init__(self) -> None:
        if not self.repo or not self.commit:
            raise ValueError("subject requires a non-empty repo and commit")
        if self.unit is not None and not self.unit:
            raise ValueError("subject.unit must be a non-empty string or null, never ''")

    def to_dict(self) -> dict:
        return {"repo": self.repo, "commit": self.commit, "unit": self.unit}

    @classmethod
    def from_dict(cls, d: dict) -> "Subject":
        return cls(repo=d["repo"], commit=d["commit"], unit=d["unit"])


@dataclass(frozen=True)
class Coverage:
    """What an enumerating checker measured about ONE obligation's
    precondition (receipt 2.0.0).

    This is the same record `audit.ObligationHypothesisEvidence` carries,
    put where it belongs: on the receipt. Before 2.0.0 a checker could
    measure hypothesis coverage and had nowhere to put it, so the
    unexercised-hypothesis audit check had nothing to read and abstained
    on every target driven through the pipeline — coverage silently
    bypassed the gate it was supposed to feed.

    `exhaustive` changes what the counts MEAN (a whole reachable set
    versus a bound-truncated slice of it), so it travels with them.
    """

    states_satisfying: int
    states_violating: int
    exhaustive: bool

    def __post_init__(self) -> None:
        for field_name in ("states_satisfying", "states_violating"):
            value = getattr(self, field_name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"coverage.{field_name} must be a non-negative integer, got {value!r}")
        if not isinstance(self.exhaustive, bool):
            raise ValueError(f"coverage.exhaustive must be a bool, got {self.exhaustive!r}")

    def to_dict(self) -> dict:
        return {
            "states_satisfying": self.states_satisfying,
            "states_violating": self.states_violating,
            "exhaustive": self.exhaustive,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Coverage":
        return cls(
            states_satisfying=d["states_satisfying"],
            states_violating=d["states_violating"],
            exhaustive=d["exhaustive"],
        )


@dataclass(frozen=True)
class Control:
    """A receipt's control block (receipt 2.0.0): this run exists to
    attest that ANOTHER claim's oracle or precondition is load-bearing,
    not to establish that claim.

    A check nobody has watched fail is untested. An ablation removes a
    precondition and expects the property to break; a mutation perturbs
    the implementation and expects the oracle to catch it; a planted twin
    is a deliberately-wrong sibling artifact the pipeline is expected to
    reject. Recording the prediction (`expectation`) separately from the
    measurement (`observed`) is what stops a control from being
    reinterpreted after the fact to match whatever happened.

    `observed` is deliberately NOT restricted to the expectation
    vocabulary: a control can land outside it (the run errored, no cover
    existed). `passed()` is equality, so an unrecognized observation is a
    failed control rather than an unnoticed one.
    """

    kind: str            # "ablation" | "mutation" | "planted-twin"
    expectation: str     # "red" | "green" | "sat"
    observed: str
    of_claim: str

    def __post_init__(self) -> None:
        if self.kind not in _CONTROL_KINDS:
            raise ValueError(f"control.kind must be one of {_CONTROL_KINDS}, got {self.kind!r}")
        if self.expectation not in _CONTROL_EXPECTATIONS:
            raise ValueError(
                f"control.expectation must be one of {_CONTROL_EXPECTATIONS}, "
                f"got {self.expectation!r}"
            )
        if not self.observed:
            raise ValueError(
                "control.observed must record what the run actually showed; an empty "
                "observation is not the same as a control that was never run"
            )
        if not self.of_claim:
            raise ValueError("control.of_claim must name the claim_id this control attests")

    def passed(self) -> bool:
        """True iff the control behaved as predicted. Equality on
        purpose: 'close enough to the prediction' is not a control."""
        return self.observed == self.expectation

    def to_dict(self) -> dict:
        return {
            "kind": self.kind,
            "expectation": self.expectation,
            "observed": self.observed,
            "of_claim": self.of_claim,
        }

    @classmethod
    def from_dict(cls, d: dict) -> "Control":
        return cls(
            kind=d["kind"],
            expectation=d["expectation"],
            observed=d["observed"],
            of_claim=d["of_claim"],
        )


@dataclass(frozen=True)
class Obligation:
    """One entry in a receipt's exhaustive obligation bucket
    (INTERFACES.md property 2). `status` must distinguish "held" from
    "vacuous" / "not-exercised" — an obligation that was never really
    tested must never look identical to one that held.

    `coverage` is a 2.0.0 addition and is null on a 1.0.0 receipt (the
    format had no place for it); null there means "this checker reported
    no coverage for this obligation", never "coverage was fine".
    """

    id: str
    status: str  # "held" | "vacuous" | "not-exercised" | "failed"
    coverage: Optional[Coverage] = None

    def __post_init__(self) -> None:
        if self.status not in _OBLIGATION_STATUSES:
            raise ValueError(
                f"obligation.status must be one of {_OBLIGATION_STATUSES}, got {self.status!r}"
            )

    def to_dict(self, *, include_coverage: bool = False) -> dict:
        """Serialize. `include_coverage` is driven by the enclosing
        receipt's schema version, because whether the key exists at all
        is a format question, not a data question: on 2.0.0 it is always
        present (null when unmeasured), on 1.0.0 it must never appear."""
        doc = {"id": self.id, "status": self.status}
        if include_coverage:
            doc["coverage"] = self.coverage.to_dict() if self.coverage else None
        return doc

    @classmethod
    def from_dict(cls, d: dict) -> "Obligation":
        coverage = d.get("coverage")
        return cls(
            id=d["id"],
            status=d["status"],
            coverage=Coverage.from_dict(coverage) if coverage else None,
        )


@dataclass(frozen=True)
class Receipt:
    """A verification receipt (ARCHITECTURE.md §4, §7). Construct via the
    kernel gate (`kernel_gate.py`) rather than by hand where possible —
    the invariants below (certificate iff kernel+accepted, harness/bound/
    env_assumptions iff model-checker) are exactly what the schema
    enforces, and this constructor enforces them too so an in-memory
    Receipt can never itself be malformed before it is even serialized.

    One class serves both published formats, and `schema_version` decides
    which invariants apply. A 2.0.0 receipt REQUIRES `toolchain`,
    `subject` and `claim_id` (a verdict that cannot be attributed to a
    build, a subject and a claim is not evidence) and requires
    `failure_kind` exactly when the verdict is 'error'. A 1.0.0 receipt
    must carry NONE of the 2.0.0 fields — not because they would be
    unwelcome, but because a document that declares the old format and
    carries new fields is unreadable by both formats' consumers
    (INTERFACES.md property 5). Both directions are enforced here and in
    the schemas.
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
    # --- 2.0.0 additions; all must be None on a 1.0.0 receipt ---
    claim_id: Optional[str] = None
    subject: Optional[Subject] = None
    toolchain: Optional[Toolchain] = None
    failure_kind: Optional[str] = None
    control: Optional[Control] = None

    def __post_init__(self) -> None:
        if self.schema_version not in RECEIPT_SCHEMA_VERSIONS:
            raise ValueError(
                f"schema_version must be one of {RECEIPT_SCHEMA_VERSIONS}, "
                f"got {self.schema_version!r}"
            )
        if self.verdict not in _VERDICTS:
            raise ValueError(f"verdict must be one of {_VERDICTS}, got {self.verdict!r}")

        if self.schema_version == "1.0.0":
            for name in ("claim_id", "subject", "toolchain", "failure_kind", "control"):
                if getattr(self, name) is not None:
                    raise ValueError(
                        f"{name} was introduced in receipt schema 2.0.0 and must be null on a "
                        f"1.0.0 receipt — a document may not carry a field its own format "
                        f"never defined"
                    )
            if any(o.coverage is not None for o in self.obligations):
                raise ValueError(
                    "per-obligation coverage was introduced in receipt schema 2.0.0 and must "
                    "be null on a 1.0.0 receipt"
                )
        else:
            if self.toolchain is None or self.subject is None:
                raise ValueError(
                    "a 2.0.0 receipt requires a toolchain and a subject: a verdict that cannot "
                    "be attributed to an exact build and an exact source state is not evidence"
                )
            if not self.claim_id:
                raise ValueError(
                    "a 2.0.0 receipt requires a non-empty claim_id — the key under which this "
                    "receipt is evidence for one claim among many"
                )
            if self.verdict == "error":
                if self.failure_kind not in _FAILURE_KINDS:
                    raise ValueError(
                        f"verdict 'error' requires failure_kind in {_FAILURE_KINDS}, got "
                        f"{self.failure_kind!r}: an error that does not say what kind of error "
                        f"is the ambiguity this field exists to remove"
                    )
            elif self.failure_kind is not None:
                raise ValueError(
                    f"failure_kind must be null unless verdict == 'error', got "
                    f"{self.failure_kind!r} with verdict {self.verdict!r}"
                )

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
        is_2_0_0 = self.schema_version == "2.0.0"
        doc = {
            "schema_version": self.schema_version,
            "target_id": self.target_id,
            "candidate_id": self.candidate_id,
            "checker": self.checker.to_dict(),
            "verdict": self.verdict,
            "certificate": self.certificate.to_dict() if self.certificate else None,
            "harness": self.harness,
            "bound": self.bound,
            "env_assumptions": self.env_assumptions,
            "obligations": [o.to_dict(include_coverage=is_2_0_0) for o in self.obligations],
            "produced_at": self.produced_at,
        }
        if is_2_0_0:
            doc["claim_id"] = self.claim_id
            doc["subject"] = self.subject.to_dict()
            doc["toolchain"] = self.toolchain.to_dict()
            doc["failure_kind"] = self.failure_kind
            doc["control"] = self.control.to_dict() if self.control else None
        return doc

    @classmethod
    def from_dict(cls, d: dict) -> "Receipt":
        """Construct a Receipt from a plain dict, in whichever published
        format the document declares. Callers that read receipts from
        disk should use `load_receipt`, which validates against that
        version's schema first; this constructor additionally enforces
        the dataclass-level invariants in __post_init__."""
        subject = d.get("subject")
        toolchain = d.get("toolchain")
        control = d.get("control")
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
            claim_id=d.get("claim_id"),
            subject=Subject.from_dict(subject) if subject else None,
            toolchain=Toolchain.from_dict(toolchain) if toolchain else None,
            failure_kind=d.get("failure_kind"),
            control=Control.from_dict(control) if control else None,
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
        if self.schema_version not in _AUDIT_REASONS_BY_VERSION:
            raise ValueError(
                f"schema_version must be one of {AUDIT_SCHEMA_VERSIONS}, "
                f"got {self.schema_version!r}"
            )
        if self.verdict not in _AUDIT_VERDICTS:
            raise ValueError(f"verdict must be one of {_AUDIT_VERDICTS}, got {self.verdict!r}")
        if self.verdict == "pass" and self.failure_reason is not None:
            raise ValueError("failure_reason must be null when verdict == 'pass'")
        if self.verdict == "fail":
            permitted = _AUDIT_REASONS_BY_VERSION[self.schema_version]
            if self.failure_reason not in permitted:
                introduced_later = self.failure_reason in _AUDIT_FAILURE_REASONS
                raise ValueError(
                    f"failure_reason {self.failure_reason!r} is not available in audit schema "
                    f"{self.schema_version}"
                    + (
                        " — it was introduced in a later version, and a document may not carry "
                        "a code its own format never defined (INTERFACES.md property 5)"
                        if introduced_later
                        else f"; permitted there: {permitted}"
                    )
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
