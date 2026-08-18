"""Tests for receipts.py: schema round-trip, malformed-document rejection,
and atomic_write leaving no partial file. Pure Python — no Lean needed.
"""

from __future__ import annotations

import json
import os
import unittest
from pathlib import Path

from autoprover_ref.jsonschema_min import SchemaValidationError
from autoprover_ref.receipts import (
    AUDIT_SCHEMA_VERSION,
    Certificate,
    Checker,
    Obligation,
    Receipt,
    AuditVerdict,
    atomic_write_json,
    load_audit,
    load_receipt,
    now_iso,
    validate_audit_dict,
    validate_receipt_dict,
    write_audit,
    write_receipt,
)

from _tmpdir import TempDirCase


def make_kernel_receipt(**overrides) -> Receipt:
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
    )
    fields.update(overrides)
    return Receipt(**fields)


def make_model_checker_receipt(**overrides) -> Receipt:
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
        self.assertEqual(loaded.schema_version, "1.1.0")


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
