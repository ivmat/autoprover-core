"""Tests for receipts.py: schema round-trip, malformed-document rejection,
and atomic_write leaving no partial file. Pure Python — no Lean needed.

Both published receipt formats are exercised here, in both directions:
a 1.0.0 document must still validate as 1.0.0 and must not be allowed to
carry 2.0.0's fields, and a 2.0.0 document must not be allowed to omit
them (INTERFACES.md property 5).
"""

from __future__ import annotations

import json
import os
import unittest
from pathlib import Path

from autoprover_ref.jsonschema_min import SchemaValidationError
from autoprover_ref.receipts import (
    AUDIT_SCHEMA_VERSION,
    RECEIPT_SCHEMA_VERSION,
    Certificate,
    Checker,
    Control,
    Coverage,
    Dependency,
    Obligation,
    Receipt,
    Subject,
    Tool,
    Toolchain,
    AuditVerdict,
    atomic_write_json,
    load_audit,
    load_receipt,
    now_iso,
    receipt_schema,
    validate_audit_dict,
    validate_receipt_dict,
    write_audit,
    write_receipt,
)

from _tmpdir import TempDirCase


def make_kernel_receipt(**overrides) -> Receipt:
    """A 1.0.0 kernel receipt (the original format, explicitly pinned)."""
    fields = dict(
        target_id="t1",
        candidate_id="c1",
        checker=Checker(kind="kernel", name="lean", version="4.31.0"),
        verdict="accepted",
        certificate=Certificate(checked_file="/tmp/x.lean", toolchain_id="leanprover/lean4:v4.31.0"),
        harness=None,
        bound=None,
        env_assumptions=None,
        obligations=(Obligation(id="t1", status="held"),),
        produced_at=now_iso(),
        schema_version="1.0.0",
    )
    fields.update(overrides)
    return Receipt(**fields)


def make_model_checker_receipt(**overrides) -> Receipt:
    """A 1.0.0 model-checker receipt."""
    fields = dict(
        target_id="t2",
        candidate_id="c2",
        checker=Checker(kind="model-checker", name="kani", version="0.55.0"),
        verdict="accepted",
        certificate=None,
        harness="harness_foo",
        bound=8,
        env_assumptions="single-threaded, bounded queue depth 8",
        obligations=(Obligation(id="t2", status="held"),),
        produced_at=now_iso(),
        schema_version="1.0.0",
    )
    fields.update(overrides)
    return Receipt(**fields)


def make_toolchain(**overrides) -> Toolchain:
    fields = dict(
        tool=Tool(name="checker-x", commit_or_version="9f2c1ab3d4e5f60718293a4b5c6d7e8f90a1b2c3"),
        dependencies=(Dependency(name="solver-y", version="6.8.0"),),
        flags=("--unstable-semantics", "--bound=8"),
        features=("contracts",),
    )
    fields.update(overrides)
    return Toolchain(**fields)


def make_subject(**overrides) -> Subject:
    fields = dict(repo="example/subject", commit="0123456789abcdef0123456789abcdef01234567", unit="mod_a")
    fields.update(overrides)
    return Subject(**fields)


def make_kernel_receipt_v2(**overrides) -> Receipt:
    """A 2.0.0 kernel receipt: fully attributed (toolchain + subject +
    claim_id), with the fields 1.0.0 could not carry."""
    fields = dict(
        target_id="t1",
        candidate_id="c1",
        checker=Checker(kind="kernel", name="lean", version="4.31.0"),
        verdict="accepted",
        certificate=Certificate(checked_file="/tmp/x.lean", toolchain_id="leanprover/lean4:v4.31.0"),
        harness=None,
        bound=None,
        env_assumptions=None,
        obligations=(Obligation(id="t1", status="held"),),
        produced_at=now_iso(),
        schema_version="2.0.0",
        claim_id="claim-1",
        subject=make_subject(),
        toolchain=make_toolchain(),
        failure_kind=None,
        control=None,
    )
    fields.update(overrides)
    return Receipt(**fields)


def make_model_checker_receipt_v2(**overrides) -> Receipt:
    fields = dict(
        target_id="t2",
        candidate_id="c2",
        checker=Checker(kind="model-checker", name="checker-x", version="0.55.0"),
        verdict="accepted",
        certificate=None,
        harness="harness_foo",
        bound=8,
        env_assumptions="single-threaded, bounded queue depth 8",
        obligations=(Obligation(id="t2", status="held"),),
        produced_at=now_iso(),
        schema_version="2.0.0",
        claim_id="claim-1",
        subject=make_subject(),
        toolchain=make_toolchain(),
        failure_kind=None,
        control=None,
    )
    fields.update(overrides)
    return Receipt(**fields)


class ReceiptRoundTripTests(TempDirCase):
    def test_kernel_receipt_round_trip(self):
        receipt = make_kernel_receipt()
        path = self.tmp_path("receipt.json")
        write_receipt(path, receipt)
        loaded = load_receipt(path)
        self.assertEqual(loaded, receipt)

    def test_model_checker_receipt_round_trip(self):
        receipt = make_model_checker_receipt()
        path = self.tmp_path("receipt.json")
        write_receipt(path, receipt)
        loaded = load_receipt(path)
        self.assertEqual(loaded, receipt)

    def test_audit_verdict_round_trip_pass(self):
        verdict = AuditVerdict(
            target_id="t1", candidate_id="c1", verdict="pass",
            failure_reason=None, details={"checks_run": ["vacuity"]}, produced_at=now_iso(),
        )
        path = self.tmp_path("audit.json")
        write_audit(path, verdict)
        loaded = load_audit(path)
        self.assertEqual(loaded, verdict)

    def test_audit_verdict_round_trip_fail(self):
        verdict = AuditVerdict(
            target_id="t1", candidate_id="c1", verdict="fail",
            failure_reason="vacuous-precondition", details={"missing_witness_for": ["p"]},
            produced_at=now_iso(),
        )
        path = self.tmp_path("audit.json")
        write_audit(path, verdict)
        loaded = load_audit(path)
        self.assertEqual(loaded, verdict)

    def test_audit_verdict_round_trip_unexercised_hypothesis(self):
        verdict = AuditVerdict(
            target_id="t1", candidate_id="c1", verdict="fail",
            failure_reason="unexercised-hypothesis",
            details={"unexercised": [{"obligation_id": "o1"}]},
            produced_at=now_iso(),
        )
        path = self.tmp_path("audit.json")
        write_audit(path, verdict)
        loaded = load_audit(path)
        self.assertEqual(loaded, verdict)
        self.assertEqual(loaded.schema_version, "1.2.0")


class MalformedDocumentTests(unittest.TestCase):
    def test_kernel_receipt_construction_rejects_harness(self):
        with self.assertRaises(ValueError):
            make_kernel_receipt(harness="should not be allowed")

    def test_kernel_receipt_construction_requires_certificate_on_accept(self):
        with self.assertRaises(ValueError):
            make_kernel_receipt(certificate=None)

    def test_kernel_receipt_construction_rejects_certificate_on_reject(self):
        with self.assertRaises(ValueError):
            make_kernel_receipt(
                verdict="rejected",
                obligations=(Obligation(id="t1", status="failed"),),
            )  # certificate default (from make_kernel_receipt) is non-None -> invalid combo

    def test_model_checker_receipt_requires_harness_bound_env(self):
        with self.assertRaises(ValueError):
            make_model_checker_receipt(harness=None)
        with self.assertRaises(ValueError):
            make_model_checker_receipt(bound=None)
        with self.assertRaises(ValueError):
            make_model_checker_receipt(env_assumptions=None)

    def test_model_checker_receipt_rejects_certificate(self):
        with self.assertRaises(ValueError):
            make_model_checker_receipt(
                certificate=Certificate(checked_file="x", toolchain_id="y")
            )

    def test_schema_rejects_missing_field(self):
        doc = make_kernel_receipt().to_dict()
        del doc["produced_at"]
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_schema_rejects_bad_enum(self):
        doc = make_kernel_receipt().to_dict()
        doc["verdict"] = "maybe"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_schema_rejects_additional_property(self):
        doc = make_kernel_receipt().to_dict()
        doc["unexpected_field"] = "surprise"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_schema_rejects_kernel_receipt_with_harness_set(self):
        doc = make_kernel_receipt().to_dict()
        doc["harness"] = "should be null for a kernel receipt"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_schema_rejects_model_checker_receipt_missing_harness(self):
        doc = make_model_checker_receipt().to_dict()
        doc["harness"] = None
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_schema_rejects_certificate_without_kernel_accept(self):
        doc = make_model_checker_receipt().to_dict()
        doc["certificate"] = {"checked_file": "x", "toolchain_id": "y"}
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_audit_schema_rejects_null_failure_reason_on_fail(self):
        doc = {
            "schema_version": AUDIT_SCHEMA_VERSION, "target_id": "t", "candidate_id": "c",
            "verdict": "fail", "failure_reason": None, "details": {}, "produced_at": now_iso(),
        }
        with self.assertRaises(SchemaValidationError):
            validate_audit_dict(doc)

    def test_audit_schema_rejects_non_null_failure_reason_on_pass(self):
        doc = {
            "schema_version": AUDIT_SCHEMA_VERSION, "target_id": "t", "candidate_id": "c",
            "verdict": "pass", "failure_reason": "vacuous-precondition", "details": {},
            "produced_at": now_iso(),
        }
        with self.assertRaises(SchemaValidationError):
            validate_audit_dict(doc)

    def test_audit_schema_accepts_the_1_1_0_failure_reason(self):
        doc = {
            "schema_version": "1.1.0", "target_id": "t", "candidate_id": "c",
            "verdict": "fail", "failure_reason": "unexercised-hypothesis",
            "details": {"check": "unexercised_hypothesis"}, "produced_at": now_iso(),
        }
        validate_audit_dict(doc)  # must not raise

    def test_audit_schema_forbids_the_1_1_0_reason_in_a_1_0_0_document(self):
        # Adding a value to a closed enum travels with a version bump
        # (INTERFACES.md property 5): a document that declares the older
        # format may not carry a code that format never defined.
        doc = {
            "schema_version": "1.0.0", "target_id": "t", "candidate_id": "c",
            "verdict": "fail", "failure_reason": "unexercised-hypothesis",
            "details": {}, "produced_at": now_iso(),
        }
        with self.assertRaises(SchemaValidationError):
            validate_audit_dict(doc)

    def test_audit_schema_still_accepts_a_1_0_0_document(self):
        doc = {
            "schema_version": "1.0.0", "target_id": "t", "candidate_id": "c",
            "verdict": "fail", "failure_reason": "vacuous-precondition",
            "details": {}, "produced_at": now_iso(),
        }
        validate_audit_dict(doc)  # must not raise

    def test_audit_schema_accepts_the_1_2_0_failure_reason(self):
        doc = {
            "schema_version": "1.2.0", "target_id": "t", "candidate_id": "c",
            "verdict": "fail", "failure_reason": "missing-control",
            "details": {"check": "controls"}, "produced_at": now_iso(),
        }
        validate_audit_dict(doc)  # must not raise

    def test_audit_schema_forbids_the_1_2_0_reason_in_older_documents(self):
        # Each version may carry only the codes it defined; a reader
        # built for 1.1.0 must be able to tell "old-format verdict" from
        # "a code I cannot branch on" (INTERFACES.md property 5).
        for version in ("1.0.0", "1.1.0"):
            with self.subTest(schema_version=version):
                doc = {
                    "schema_version": version, "target_id": "t", "candidate_id": "c",
                    "verdict": "fail", "failure_reason": "missing-control",
                    "details": {}, "produced_at": now_iso(),
                }
                with self.assertRaises(SchemaValidationError):
                    validate_audit_dict(doc)

    def test_audit_schema_still_accepts_a_1_1_0_document(self):
        doc = {
            "schema_version": "1.1.0", "target_id": "t", "candidate_id": "c",
            "verdict": "fail", "failure_reason": "unexercised-hypothesis",
            "details": {}, "produced_at": now_iso(),
        }
        validate_audit_dict(doc)  # must not raise

    def test_audit_schema_rejects_an_unpublished_version(self):
        doc = {
            "schema_version": "1.3.0", "target_id": "t", "candidate_id": "c",
            "verdict": "pass", "failure_reason": None,
            "details": {}, "produced_at": now_iso(),
        }
        with self.assertRaises(SchemaValidationError):
            validate_audit_dict(doc)

    def test_load_receipt_raises_on_disk_corruption_not_silent_coerce(self):
        with TempDirCase.temp_dir() as d:
            path = Path(d) / "receipt.json"
            write_receipt(path, make_kernel_receipt())
            # Corrupt it after writing: flip verdict to something invalid.
            doc = json.loads(path.read_text())
            doc["verdict"] = "sort-of-accepted"
            path.write_text(json.dumps(doc))
            with self.assertRaises(SchemaValidationError):
                load_receipt(path)


class Receipt2RoundTripTests(TempDirCase):
    def test_current_version_is_2_0_0(self):
        # A receipt constructed without an explicit version is written to
        # the CURRENT format, not the oldest one.
        self.assertEqual(RECEIPT_SCHEMA_VERSION, "2.0.0")
        self.assertEqual(make_kernel_receipt_v2().schema_version, "2.0.0")

    def test_kernel_receipt_v2_round_trip(self):
        receipt = make_kernel_receipt_v2()
        path = self.tmp_path("receipt.json")
        write_receipt(path, receipt)
        loaded = load_receipt(path)
        self.assertEqual(loaded, receipt)
        self.assertEqual(loaded.toolchain.tool.commit_or_version, receipt.toolchain.tool.commit_or_version)
        self.assertEqual(loaded.subject.unit, "mod_a")
        self.assertEqual(loaded.claim_id, "claim-1")

    def test_model_checker_receipt_v2_round_trip(self):
        receipt = make_model_checker_receipt_v2()
        path = self.tmp_path("receipt.json")
        write_receipt(path, receipt)
        self.assertEqual(load_receipt(path), receipt)

    def test_error_verdict_round_trip_with_failure_kind(self):
        for kind in ("timeout", "oom", "unsupported-construct", "tool-error"):
            with self.subTest(failure_kind=kind):
                receipt = make_model_checker_receipt_v2(
                    verdict="error",
                    failure_kind=kind,
                    obligations=(Obligation(id="t2", status="not-exercised"),),
                )
                path = self.tmp_path(f"receipt-{kind}.json")
                write_receipt(path, receipt)
                loaded = load_receipt(path)
                self.assertEqual(loaded.verdict, "error")
                self.assertEqual(loaded.failure_kind, kind)

    def test_coverage_round_trip_and_explicit_null(self):
        receipt = make_model_checker_receipt_v2(
            obligations=(
                Obligation(
                    id="measured", status="held",
                    coverage=Coverage(states_satisfying=12, states_violating=7, exhaustive=True),
                ),
                Obligation(id="unmeasured", status="held"),
            ),
        )
        path = self.tmp_path("receipt.json")
        write_receipt(path, receipt)
        doc = json.loads(path.read_text())
        # Null is written explicitly, never left as a missing key
        # (INTERFACES.md property 3).
        self.assertIsNone(doc["obligations"][1]["coverage"])
        self.assertEqual(doc["obligations"][0]["coverage"]["states_violating"], 7)
        self.assertEqual(load_receipt(path), receipt)

    def test_control_receipt_round_trip(self):
        receipt = make_model_checker_receipt_v2(
            verdict="rejected",
            obligations=(Obligation(id="t2", status="failed"),),
            control=Control(
                kind="mutation", expectation="red", observed="red", of_claim="claim-1",
            ),
        )
        path = self.tmp_path("receipt.json")
        write_receipt(path, receipt)
        loaded = load_receipt(path)
        self.assertEqual(loaded, receipt)
        self.assertTrue(loaded.control.passed())

    def test_control_that_did_not_behave_as_predicted_is_a_failed_control(self):
        control = Control(kind="ablation", expectation="red", observed="green", of_claim="claim-1")
        self.assertFalse(control.passed())

    def test_control_observed_outside_the_expectation_vocabulary_is_not_a_pass(self):
        # `observed` is measured, not declared, so it may land outside the
        # closed expectation enum. Equality is the test, so an
        # unrecognized observation fails rather than slipping through.
        control = Control(kind="ablation", expectation="red", observed="error", of_claim="claim-1")
        self.assertFalse(control.passed())

    def test_features_null_and_empty_are_distinct_documents(self):
        no_concept = make_kernel_receipt_v2(toolchain=make_toolchain(features=None))
        none_enabled = make_kernel_receipt_v2(toolchain=make_toolchain(features=()))
        self.assertIsNone(no_concept.to_dict()["toolchain"]["features"])
        self.assertEqual(none_enabled.to_dict()["toolchain"]["features"], [])
        self.assertNotEqual(no_concept, none_enabled)


class Receipt2ConstructionRejectionTests(unittest.TestCase):
    """Construction-level rejection matrix for every 2.0.0 invariant —
    an in-memory Receipt can never be malformed before serialization."""

    def test_2_0_0_requires_toolchain(self):
        with self.assertRaises(ValueError):
            make_kernel_receipt_v2(toolchain=None)

    def test_2_0_0_requires_subject(self):
        with self.assertRaises(ValueError):
            make_kernel_receipt_v2(subject=None)

    def test_2_0_0_requires_non_empty_claim_id(self):
        with self.assertRaises(ValueError):
            make_kernel_receipt_v2(claim_id=None)
        with self.assertRaises(ValueError):
            make_kernel_receipt_v2(claim_id="")

    def test_error_verdict_requires_a_failure_kind(self):
        with self.assertRaises(ValueError):
            make_model_checker_receipt_v2(
                verdict="error", failure_kind=None,
                obligations=(Obligation(id="t2", status="not-exercised"),),
            )

    def test_error_verdict_rejects_an_unknown_failure_kind(self):
        with self.assertRaises(ValueError):
            make_model_checker_receipt_v2(
                verdict="error", failure_kind="probably-fine",
                obligations=(Obligation(id="t2", status="not-exercised"),),
            )

    def test_non_error_verdict_rejects_a_failure_kind(self):
        with self.assertRaises(ValueError):
            make_model_checker_receipt_v2(failure_kind="timeout")

    def test_unknown_schema_version_rejected(self):
        with self.assertRaises(ValueError):
            make_kernel_receipt_v2(schema_version="3.0.0")

    def test_subject_requires_repo_and_commit(self):
        with self.assertRaises(ValueError):
            Subject(repo="", commit="abc", unit=None)
        with self.assertRaises(ValueError):
            Subject(repo="r", commit="", unit=None)

    def test_subject_unit_is_null_or_non_empty_never_blank(self):
        with self.assertRaises(ValueError):
            Subject(repo="r", commit="c", unit="")
        self.assertIsNone(Subject(repo="r", commit="c", unit=None).unit)

    def test_tool_requires_a_build_identity(self):
        with self.assertRaises(ValueError):
            Tool(name="checker-x", commit_or_version="")

    def test_dependency_requires_name_and_version(self):
        with self.assertRaises(ValueError):
            Dependency(name="solver-y", version="")

    def test_coverage_rejects_negative_and_non_integer_counts(self):
        with self.assertRaises(ValueError):
            Coverage(states_satisfying=-1, states_violating=0, exhaustive=True)
        with self.assertRaises(ValueError):
            Coverage(states_satisfying=1.5, states_violating=0, exhaustive=True)
        with self.assertRaises(ValueError):
            Coverage(states_satisfying=1, states_violating=0, exhaustive="yes")

    def test_control_rejects_unknown_kind_and_expectation(self):
        with self.assertRaises(ValueError):
            Control(kind="vibes", expectation="red", observed="red", of_claim="c")
        with self.assertRaises(ValueError):
            Control(kind="mutation", expectation="pink", observed="red", of_claim="c")

    def test_control_requires_observed_and_of_claim(self):
        with self.assertRaises(ValueError):
            Control(kind="mutation", expectation="red", observed="", of_claim="c")
        with self.assertRaises(ValueError):
            Control(kind="mutation", expectation="red", observed="red", of_claim="")


class ReceiptVersionDisciplineTests(unittest.TestCase):
    """Both directions of INTERFACES.md property 5: an old document may
    not borrow the new format's fields, and a new document may not omit
    them."""

    def test_1_0_0_receipt_may_not_carry_2_0_0_fields_at_construction(self):
        for field, value in (
            ("claim_id", "claim-1"),
            ("subject", make_subject()),
            ("toolchain", make_toolchain()),
            ("control", Control(kind="mutation", expectation="red", observed="red", of_claim="c")),
        ):
            with self.subTest(field=field):
                with self.assertRaises(ValueError):
                    make_kernel_receipt(**{field: value})

    def test_1_0_0_receipt_may_not_carry_obligation_coverage(self):
        with self.assertRaises(ValueError):
            make_kernel_receipt(
                obligations=(Obligation(
                    id="t1", status="held",
                    coverage=Coverage(states_satisfying=1, states_violating=1, exhaustive=False),
                ),),
            )

    def test_1_0_0_receipt_may_not_carry_a_failure_kind(self):
        with self.assertRaises(ValueError):
            make_kernel_receipt(
                verdict="error", certificate=None, failure_kind="timeout",
                obligations=(Obligation(id="t1", status="not-exercised"),),
            )

    def test_schema_rejects_a_1_0_0_document_carrying_2_0_0_fields(self):
        doc = make_kernel_receipt().to_dict()
        doc["claim_id"] = "claim-1"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_schema_rejects_a_1_0_0_document_whose_obligation_carries_coverage(self):
        doc = make_kernel_receipt().to_dict()
        doc["obligations"][0]["coverage"] = None
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_schema_rejects_a_2_0_0_document_missing_the_new_required_objects(self):
        for field in ("claim_id", "subject", "toolchain", "failure_kind", "control"):
            with self.subTest(field=field):
                doc = make_kernel_receipt_v2().to_dict()
                del doc[field]
                with self.assertRaises(SchemaValidationError):
                    validate_receipt_dict(doc)

    def test_schema_rejects_a_2_0_0_document_whose_obligation_omits_coverage(self):
        doc = make_kernel_receipt_v2().to_dict()
        del doc["obligations"][0]["coverage"]
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_schema_still_accepts_an_unchanged_1_0_0_document(self):
        doc = make_kernel_receipt().to_dict()
        validate_receipt_dict(doc)  # must not raise
        self.assertNotIn("toolchain", doc)

    def test_a_1_0_0_document_is_judged_by_the_1_0_0_schema_not_the_current_one(self):
        doc = make_kernel_receipt().to_dict()
        with self.assertRaises(SchemaValidationError):
            # ... which is what would happen if the loader used the
            # current schema for every document.
            validate_receipt_dict({**doc, "schema_version": "2.0.0"})
        validate_receipt_dict(doc)

    def test_unknown_schema_version_is_refused_not_guessed(self):
        doc = make_kernel_receipt_v2().to_dict()
        doc["schema_version"] = "1.5.0"
        with self.assertRaises(SchemaValidationError) as ctx:
            validate_receipt_dict(doc)
        self.assertIn("refusing to guess", str(ctx.exception))

    def test_missing_schema_version_is_refused_not_guessed(self):
        doc = make_kernel_receipt_v2().to_dict()
        del doc["schema_version"]
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_receipt_schema_loader_refuses_an_unpublished_version(self):
        with self.assertRaises(ValueError):
            receipt_schema("1.5.0")
        self.assertEqual(receipt_schema("1.0.0")["schemaVersion"], "1.0.0")
        self.assertEqual(receipt_schema()["schemaVersion"], "2.0.0")


class Receipt2SchemaRejectionTests(unittest.TestCase):
    """Schema-level rejection matrix for the 2.0.0 invariants — the same
    rules the constructor enforces, checked against documents that never
    went through it (as receipts read from disk have not)."""

    def test_rejects_error_verdict_without_failure_kind(self):
        doc = make_model_checker_receipt_v2().to_dict()
        doc["verdict"] = "error"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_rejects_failure_kind_on_a_non_error_verdict(self):
        doc = make_model_checker_receipt_v2().to_dict()
        doc["failure_kind"] = "timeout"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_rejects_unknown_failure_kind(self):
        doc = make_model_checker_receipt_v2().to_dict()
        doc["verdict"] = "error"
        doc["failure_kind"] = "probably-fine"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_rejects_empty_claim_id(self):
        doc = make_kernel_receipt_v2().to_dict()
        doc["claim_id"] = ""
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_rejects_subject_missing_commit(self):
        doc = make_kernel_receipt_v2().to_dict()
        del doc["subject"]["commit"]
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_rejects_subject_with_additional_property(self):
        doc = make_kernel_receipt_v2().to_dict()
        doc["subject"]["branch"] = "somewhere"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_rejects_toolchain_missing_any_required_key(self):
        for key in ("tool", "dependencies", "flags", "features"):
            with self.subTest(key=key):
                doc = make_kernel_receipt_v2().to_dict()
                del doc["toolchain"][key]
                with self.assertRaises(SchemaValidationError):
                    validate_receipt_dict(doc)

    def test_rejects_tool_without_build_identity(self):
        doc = make_kernel_receipt_v2().to_dict()
        del doc["toolchain"]["tool"]["commit_or_version"]
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_rejects_dependency_without_version(self):
        doc = make_kernel_receipt_v2().to_dict()
        doc["toolchain"]["dependencies"][0].pop("version")
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_accepts_null_features_and_empty_features(self):
        for features in (None, []):
            with self.subTest(features=features):
                doc = make_kernel_receipt_v2().to_dict()
                doc["toolchain"]["features"] = features
                validate_receipt_dict(doc)  # must not raise

    def test_rejects_coverage_missing_a_count(self):
        doc = make_model_checker_receipt_v2(
            obligations=(Obligation(
                id="t2", status="held",
                coverage=Coverage(states_satisfying=3, states_violating=1, exhaustive=False),
            ),),
        ).to_dict()
        del doc["obligations"][0]["coverage"]["states_violating"]
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_rejects_non_integer_coverage_count(self):
        doc = make_model_checker_receipt_v2(
            obligations=(Obligation(
                id="t2", status="held",
                coverage=Coverage(states_satisfying=3, states_violating=1, exhaustive=False),
            ),),
        ).to_dict()
        doc["obligations"][0]["coverage"]["states_satisfying"] = "lots"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_rejects_unknown_control_kind_and_expectation(self):
        base = make_model_checker_receipt_v2(
            control=Control(kind="mutation", expectation="red", observed="red", of_claim="claim-1"),
        ).to_dict()
        for key, bad in (("kind", "vibes"), ("expectation", "pink")):
            with self.subTest(key=key):
                doc = json.loads(json.dumps(base))
                doc["control"][key] = bad
                with self.assertRaises(SchemaValidationError):
                    validate_receipt_dict(doc)

    def test_rejects_control_missing_of_claim(self):
        doc = make_model_checker_receipt_v2(
            control=Control(kind="ablation", expectation="green", observed="green", of_claim="claim-1"),
        ).to_dict()
        del doc["control"]["of_claim"]
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_rejects_additional_top_level_property(self):
        doc = make_kernel_receipt_v2().to_dict()
        doc["confidence"] = "high"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

    def test_still_rejects_the_1_0_0_kernel_vs_model_checker_rules(self):
        doc = make_kernel_receipt_v2().to_dict()
        doc["harness"] = "should be null for a kernel receipt"
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)

        doc = make_model_checker_receipt_v2().to_dict()
        doc["certificate"] = {"checked_file": "x", "toolchain_id": "y"}
        with self.assertRaises(SchemaValidationError):
            validate_receipt_dict(doc)


class AtomicWriteTests(TempDirCase):
    def test_atomic_write_leaves_no_partial_file(self):
        path = self.tmp_path("out.json")
        atomic_write_json(path, {"a": 1})
        self.assertTrue(path.exists())
        # No leftover temp files in the directory.
        leftovers = [p for p in path.parent.iterdir() if p != path]
        self.assertEqual(leftovers, [], f"unexpected leftover files: {leftovers}")

    def test_atomic_write_final_file_is_never_partial_on_success(self):
        path = self.tmp_path("out.json")
        atomic_write_json(path, {"a": 1, "b": [1, 2, 3]})
        with open(path) as f:
            data = json.load(f)  # would raise if truncated/partial
        self.assertEqual(data, {"a": 1, "b": [1, 2, 3]})

    def test_atomic_write_does_not_clobber_via_partial_state_on_failure(self):
        path = self.tmp_path("out.json")
        atomic_write_json(path, {"a": 1})
        original_bytes = path.read_bytes()

        class Unserializable:
            pass

        with self.assertRaises(TypeError):
            atomic_write_json(path, {"a": Unserializable()})

        # Original file must be untouched (replace never happened), and no
        # temp file left behind.
        self.assertEqual(path.read_bytes(), original_bytes)
        leftovers = [p for p in path.parent.iterdir() if p != path]
        self.assertEqual(leftovers, [], f"unexpected leftover files: {leftovers}")


if __name__ == "__main__":
    unittest.main()
