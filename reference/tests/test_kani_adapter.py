"""Tests for adapters/kani.py against SYNTHETIC log fixtures.

Every log below was written by hand to exercise one shape of the tool's
output: a clean pass, a genuine failure, a run whose only failure is the
tool declining to reason, an unsatisfiable cover property, an inverted-
expectation (should-panic) harness, the terse/parallel output format, and
a log whose own trailer disagrees with its body. No real project's output
is checked in here; the fixtures are the specification of what the parser
promises to understand.
"""

from __future__ import annotations

import unittest

from autoprover_ref.adapters.kani import (
    KaniAdapterError,
    parse_kani_log,
    parse_kani_log_detailed,
)
from autoprover_ref.receipts import validate_receipt_dict


INVOCATION = {
    "claim_id": "claim-widget-copy",
    "candidate_id": "run-2001-01-01",
    "subject": {"repo": "example/widget", "commit": "a" * 40, "unit": "widget_core"},
    "toolchain": {
        "tool": {"name": "bmc-tool", "commit_or_version": "b" * 40},
        "dependencies": [
            {"name": "backend", "version": "6.8.0"},
            {"name": "sat-solver", "version": "2.0.0"},
        ],
        "flags": ["-Z function-contracts", "--object-bits", "12"],
        "features": ["contracts"],
    },
    "checker": {"name": "bmc-tool", "version": "0.67.0"},
    "bound": "object-bits=12, unwind=4",
    "env_assumptions": "single-threaded harness, pointers from one generator",
}


PREAMBLE = """\
Kani Rust Verifier 0.67.0 (standalone)
    Updating crates.io index
   Compiling widget_core v0.0.0 (/work/widget/src)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 12.34s
warning: the following packages contain code that will be rejected by a future version
note: to see what the problems were, use the option `--future-incompat-report`
"""

SOLVER_CHATTER = """\
CBMC 6.8.0 (cbmc-6.8.0)
Reading GOTO program from file /work/widget/target/widget_core.out
Generating GOTO Program
Adding CPROVER library (x86_64)
Removal of function pointers and virtual functions
Generic Property Instrumentation
Running with 12 object bits, 52 offset bits (user-specified)
Starting Bounded Model Checking
aborting path on assume(false) at file /work/widget/src/lib.rs line 12 column 5 function widget thread 0
size of program expression: 4242 steps
slicing removed 17 assignments
Generated 9 VCC(s), 4 remaining after simplification
Passing problem to propositional reduction
converting SSA
Running propositional reduction
Solving with CaDiCaL 2.0.0
1234 variables, 5678 clauses
SAT checker: instance is SATISFIABLE
Runtime Solver: 0.11s
Runtime decision procedure: 0.12s
"""

CLEAN_PASS_LOG = PREAMBLE + """\
Checking harness widget::verify::check_copy_contract...
""" + SOLVER_CHATTER + """\
SAT checker: instance is UNSATISFIABLE
Runtime Solver: 0.33s

RESULTS:
Check 1: widget::copy.assertion.1
\t - Status: SUCCESS
\t - Description: "copied region is initialized"
\t - Location: src/lib.rs:20:9 in function widget::copy

Check 2: widget::copy.pointer_dereference.1
\t - Status: SUCCESS
\t - Description: "dereference failure: pointer NULL"
\t - Location: src/lib.rs:21:9 in function widget::copy

Check 3: widget::copy.unreachable.1
\t - Status: UNREACHABLE
\t - Description: "unreachable code"
\t - Location: src/lib.rs:22:9 in function widget::copy

Check 4: widget::verify::check_copy_contract::{closure#0}.cover.1
\t - Status: SATISFIED
\t - Description: "overlapping source and destination is reachable"
\t - Location: src/lib.rs:30:13 in function widget::verify::check_copy_contract::{closure#0}


SUMMARY:
 ** 0 of 4 failed (1 unreachable)

 ** 1 of 1 cover properties satisfied


VERIFICATION:- SUCCESSFUL
Verification Time: 3.58s

Manual Harness Summary:
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
"""

FAILURE_LOG = PREAMBLE + """\
Checking harness widget::verify::check_copy_contract...
""" + SOLVER_CHATTER + """\

RESULTS:
Check 1: widget::copy.assertion.1
\t - Status: FAILURE
\t - Description: "copied region is initialized"
\t - Location: src/lib.rs:20:9 in function widget::copy

Check 2: widget::copy.pointer_dereference.1
\t - Status: SUCCESS
\t - Description: "dereference failure: pointer NULL"
\t - Location: src/lib.rs:21:9 in function widget::copy


SUMMARY:
 ** 1 of 2 failed

Failed Checks: copied region is initialized
 File: "src/lib.rs", line 20, in widget::copy

VERIFICATION:- FAILED
Verification Time: 4.20s

Manual Harness Summary:
Verification failed for - widget::verify::check_copy_contract
Complete - 0 successfully verified harnesses, 1 failures, 1 total.
"""

UNSUPPORTED_LOG = PREAMBLE + """\
Checking harness widget::verify::check_exotic...
""" + SOLVER_CHATTER + """\

RESULTS:
Check 1: widget::exotic.unsupported_construct.1
\t - Status: FAILURE
\t - Description: "caller_location is not currently supported by Kani. Please post your example"
\t - Location: src/lib.rs:40:1 in function widget::exotic

Check 2: widget::exotic.assertion.1
\t - Status: SUCCESS
\t - Description: "result is in range"
\t - Location: src/lib.rs:41:1 in function widget::exotic


SUMMARY:
 ** 1 of 2 failed

Failed Checks: caller_location is not currently supported by Kani. Please post your example
 File: "src/lib.rs", line 40, in widget::exotic

VERIFICATION:- FAILED
Verification Time: 1.00s

Manual Harness Summary:
Verification failed for - widget::verify::check_exotic
Complete - 0 successfully verified harnesses, 1 failures, 1 total.
"""

UNSUPPORTED_PLUS_GENUINE_LOG = UNSUPPORTED_LOG.replace(
    """Check 2: widget::exotic.assertion.1
\t - Status: SUCCESS""",
    """Check 2: widget::exotic.assertion.1
\t - Status: FAILURE""",
).replace(
    " ** 1 of 2 failed",
    " ** 2 of 2 failed",
).replace(
    """Failed Checks: caller_location is not currently supported by Kani. Please post your example
 File: "src/lib.rs", line 40, in widget::exotic""",
    """Failed Checks: caller_location is not currently supported by Kani. Please post your example
 File: "src/lib.rs", line 40, in widget::exotic

Failed Checks: result is in range
 File: "src/lib.rs", line 41, in widget::exotic""",
)

UNSATISFIABLE_COVER_LOG = PREAMBLE + """\
Checking harness widget::verify::check_overlap_cover...
""" + SOLVER_CHATTER + """\
SAT checker: instance is UNSATISFIABLE

RESULTS:
Check 1: widget::copy.assertion.1
\t - Status: SUCCESS
\t - Description: "copied region is initialized"
\t - Location: src/lib.rs:20:9 in function widget::copy

Check 2: widget::verify::check_overlap_cover::{closure#0}.cover.1
\t - Status: UNSATISFIABLE
\t - Description: "overlapping source and destination is reachable"
\t - Location: src/lib.rs:30:13 in function widget::verify::check_overlap_cover::{closure#0}


SUMMARY:
 ** 0 of 2 failed

 ** 0 of 1 cover properties satisfied


VERIFICATION:- SUCCESSFUL
Verification Time: 2.00s

Manual Harness Summary:
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
"""

# The parallel driver's terse format: no per-check results at all, and
# harness output interleaved across worker threads.
TERSE_PARALLEL_LOG = PREAMBLE + """\
Thread 0: Checking harness widget::verify::check_a...
Thread 1: Checking harness widget::verify::check_b...
Thread 2: Checking harness widget::verify::should_fail_c...
Thread 1:
VERIFICATION RESULT:
 ** 0 of 53 failed

VERIFICATION:- SUCCESSFUL
Verification Time: 0.61s

Thread 0:
VERIFICATION RESULT:
 ** 0 of 66 failed (2 unreachable)

 ** 1 of 1 cover properties satisfied


VERIFICATION:- SUCCESSFUL
Verification Time: 0.57s

Thread 2:
VERIFICATION RESULT:
 ** 1 of 23 failed (1 unreachable)
Failed Checks: input can be dereferenced
 File: "src/lib.rs", line 60, in widget::transmute_wrapper

VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)
Verification Time: 0.10s

Manual Harness Summary:
Complete - 3 successfully verified harnesses, 0 failures, 3 total.
"""

COUNT_MISMATCH_LOG = CLEAN_PASS_LOG.replace(
    "Complete - 1 successfully verified harnesses, 0 failures, 1 total.",
    "Complete - 2 successfully verified harnesses, 0 failures, 2 total.",
)

NO_TRAILER_LOG = CLEAN_PASS_LOG.replace(
    "Manual Harness Summary:\nComplete - 1 successfully verified harnesses, 0 failures, 1 total.\n",
    "",
)


class CleanPassTests(unittest.TestCase):
    def test_one_receipt_per_harness_fully_attributed(self):
        [receipt] = parse_kani_log(CLEAN_PASS_LOG, INVOCATION)
        self.assertEqual(receipt.verdict, "accepted")
        self.assertEqual(receipt.harness, "widget::verify::check_copy_contract")
        self.assertEqual(receipt.target_id, "widget::verify::check_copy_contract")
        self.assertEqual(receipt.candidate_id, "run-2001-01-01")
        self.assertEqual(receipt.claim_id, "claim-widget-copy")
        self.assertEqual(receipt.subject.commit, "a" * 40)
        self.assertEqual(receipt.toolchain.tool.commit_or_version, "b" * 40)
        self.assertEqual(receipt.toolchain.dependencies[0].name, "backend")
        self.assertEqual(receipt.checker.kind, "model-checker")
        self.assertIsNone(receipt.certificate)
        self.assertIsNone(receipt.failure_kind)
        self.assertIsNone(receipt.control)
        validate_receipt_dict(receipt.to_dict())

    def test_every_check_becomes_an_obligation_in_the_four_status_vocabulary(self):
        [receipt] = parse_kani_log(CLEAN_PASS_LOG, INVOCATION)
        statuses = {o.id: o.status for o in receipt.obligations}
        self.assertEqual(statuses["widget::copy.assertion.1"], "held")
        self.assertEqual(statuses["widget::copy.pointer_dereference.1"], "held")
        self.assertEqual(statuses["widget::copy.unreachable.1"], "not-exercised")
        self.assertEqual(
            statuses["widget::verify::check_copy_contract::{closure#0}.cover.1"], "held"
        )
        self.assertEqual(len(receipt.obligations), 4)

    def test_coverage_is_null_because_the_tool_reports_none(self):
        # This tool says whether a property held, not how the explored
        # states split across its precondition. Null is the true answer.
        [receipt] = parse_kani_log(CLEAN_PASS_LOG, INVOCATION)
        self.assertTrue(all(o.coverage is None for o in receipt.obligations))

    def test_target_id_prefix_is_applied_when_supplied(self):
        invocation = dict(INVOCATION, target_id_prefix="widget-core/")
        [receipt] = parse_kani_log(CLEAN_PASS_LOG, invocation)
        self.assertEqual(receipt.target_id, "widget-core/widget::verify::check_copy_contract")
        self.assertEqual(receipt.harness, "widget::verify::check_copy_contract")

    def test_no_unclassified_lines_on_a_well_understood_log(self):
        parsed = parse_kani_log_detailed(CLEAN_PASS_LOG, INVOCATION)
        self.assertEqual(parsed.unclassified_lines, ())
        self.assertEqual(parsed.diagnostics, ())
        self.assertEqual(parsed.verdict_counts, {"accepted": 1, "rejected": 0, "error": 0})


class FailureTests(unittest.TestCase):
    def test_failed_harness_is_rejected_not_errored(self):
        [receipt] = parse_kani_log(FAILURE_LOG, INVOCATION)
        self.assertEqual(receipt.verdict, "rejected")
        self.assertIsNone(receipt.failure_kind)
        statuses = {o.id: o.status for o in receipt.obligations}
        self.assertEqual(statuses["widget::copy.assertion.1"], "failed")
        self.assertEqual(statuses["widget::copy.pointer_dereference.1"], "held")
        validate_receipt_dict(receipt.to_dict())

    def test_failing_property_count_is_cross_checked_against_the_checks(self):
        # The body says one check failed but reports two in the summary:
        # the parser and the tool disagree, so nothing is returned.
        log = FAILURE_LOG.replace(" ** 1 of 2 failed", " ** 2 of 2 failed")
        with self.assertRaises(KaniAdapterError) as ctx:
            parse_kani_log(log, INVOCATION)
        self.assertIn("disagree", str(ctx.exception))


class UnsupportedConstructTests(unittest.TestCase):
    def test_only_unsupported_failures_make_it_an_error_not_a_rejection(self):
        [receipt] = parse_kani_log(UNSUPPORTED_LOG, INVOCATION)
        self.assertEqual(receipt.verdict, "error")
        self.assertEqual(receipt.failure_kind, "unsupported-construct")
        validate_receipt_dict(receipt.to_dict())

    def test_the_unsupported_check_is_still_reported_as_a_failed_obligation(self):
        [receipt] = parse_kani_log(UNSUPPORTED_LOG, INVOCATION)
        statuses = {o.id: o.status for o in receipt.obligations}
        self.assertEqual(statuses["widget::exotic.unsupported_construct.1"], "failed")

    def test_a_genuine_failure_alongside_it_is_still_a_rejection(self):
        # An unsupported construct must not be allowed to mask a real
        # red by upgrading the whole run to "the tool had a problem".
        parsed = parse_kani_log_detailed(UNSUPPORTED_PLUS_GENUINE_LOG, INVOCATION)
        [receipt] = parsed.receipts
        self.assertEqual(receipt.verdict, "rejected")
        self.assertIsNone(receipt.failure_kind)
        # ... and it is reported rather than dropped.
        kinds = [d["kind"] for d in parsed.diagnostics]
        self.assertIn("unsupported-construct", kinds)

    def test_an_unsupported_check_that_passed_is_not_an_error(self):
        # Proved unreachable: the tool never had to reason about it.
        log = UNSUPPORTED_LOG.replace(
            """Check 1: widget::exotic.unsupported_construct.1
\t - Status: FAILURE""",
            """Check 1: widget::exotic.unsupported_construct.1
\t - Status: SUCCESS""",
        ).replace(
            " ** 1 of 2 failed", " ** 0 of 2 failed",
        ).replace(
            """Failed Checks: caller_location is not currently supported by Kani. Please post your example
 File: "src/lib.rs", line 40, in widget::exotic

""", "",
        ).replace(
            "VERIFICATION:- FAILED", "VERIFICATION:- SUCCESSFUL",
        ).replace(
            "Verification failed for - widget::verify::check_exotic\n", "",
        ).replace(
            "Complete - 0 successfully verified harnesses, 1 failures, 1 total.",
            "Complete - 1 successfully verified harnesses, 0 failures, 1 total.",
        )
        [receipt] = parse_kani_log(log, INVOCATION)
        self.assertEqual(receipt.verdict, "accepted")


class CoverPropertyTests(unittest.TestCase):
    def test_unsatisfiable_cover_is_vacuous(self):
        [receipt] = parse_kani_log(UNSATISFIABLE_COVER_LOG, INVOCATION)
        statuses = {o.id: o.status for o in receipt.obligations}
        self.assertEqual(
            statuses["widget::verify::check_overlap_cover::{closure#0}.cover.1"], "vacuous"
        )
        # The harness still "passes" at the tool's level - which is
        # exactly why the vacuity has to be visible in the obligations.
        self.assertEqual(receipt.verdict, "accepted")

    def test_the_solvers_unsatisfiable_prose_is_never_read_as_a_cover_status(self):
        # Both logs contain "SAT checker: instance is UNSATISFIABLE",
        # which is the solver reporting on one propositional query. Only
        # the log with an actual UNSATISFIABLE cover property yields a
        # vacuous obligation.
        self.assertIn("SAT checker: instance is UNSATISFIABLE", CLEAN_PASS_LOG)
        [clean] = parse_kani_log(CLEAN_PASS_LOG, INVOCATION)
        self.assertNotIn("vacuous", [o.status for o in clean.obligations])

    def test_unsatisfiable_on_a_non_cover_check_is_refused_not_guessed(self):
        log = UNSATISFIABLE_COVER_LOG.replace(
            "Check 2: widget::verify::check_overlap_cover::{closure#0}.cover.1",
            "Check 2: widget::verify::check_overlap_cover::{closure#0}.assertion.7",
        )
        with self.assertRaises(KaniAdapterError) as ctx:
            parse_kani_log(log, INVOCATION)
        self.assertIn("cover property", str(ctx.exception))

    def test_unknown_check_status_is_refused(self):
        log = CLEAN_PASS_LOG.replace("\t - Status: SUCCESS", "\t - Status: PROBABLY_FINE", 1)
        with self.assertRaises(KaniAdapterError):
            parse_kani_log(log, INVOCATION)


class TerseParallelTests(unittest.TestCase):
    def test_one_receipt_per_harness_across_interleaved_threads(self):
        receipts = parse_kani_log(TERSE_PARALLEL_LOG, INVOCATION)
        self.assertEqual(
            sorted(r.harness for r in receipts),
            [
                "widget::verify::check_a",
                "widget::verify::check_b",
                "widget::verify::should_fail_c",
            ],
        )
        self.assertTrue(all(r.verdict == "accepted" for r in receipts))
        for receipt in receipts:
            validate_receipt_dict(receipt.to_dict())

    def test_aggregate_obligation_when_no_per_check_results_exist(self):
        receipts = {r.harness: r for r in parse_kani_log(TERSE_PARALLEL_LOG, INVOCATION)}
        check_b = receipts["widget::verify::check_b"]
        self.assertEqual(
            [(o.id, o.status) for o in check_b.obligations],
            [("widget::verify::check_b::all-properties", "held")],
        )

    def test_cover_aggregate_is_recorded_when_the_terse_format_reports_one(self):
        receipts = {r.harness: r for r in parse_kani_log(TERSE_PARALLEL_LOG, INVOCATION)}
        statuses = {o.id: o.status for o in receipts["widget::verify::check_a"].obligations}
        self.assertEqual(statuses["widget::verify::check_a::cover-properties"], "held")

    def test_partially_satisfied_cover_aggregate_is_vacuous(self):
        log = TERSE_PARALLEL_LOG.replace(
            " ** 1 of 1 cover properties satisfied", " ** 1 of 2 cover properties satisfied"
        )
        receipts = {r.harness: r for r in parse_kani_log(log, INVOCATION)}
        statuses = {o.id: o.status for o in receipts["widget::verify::check_a"].obligations}
        self.assertEqual(statuses["widget::verify::check_a::cover-properties"], "vacuous")

    def test_inverted_expectation_harness_keeps_both_facts_visible(self):
        # It passed BY failing. The failing check stays `failed` because
        # it did fail, and an explicit expected-panic obligation records
        # why the verdict is nonetheless `accepted`.
        receipts = {r.harness: r for r in parse_kani_log(TERSE_PARALLEL_LOG, INVOCATION)}
        should_fail = receipts["widget::verify::should_fail_c"]
        self.assertEqual(should_fail.verdict, "accepted")
        statuses = {o.id: o.status for o in should_fail.obligations}
        self.assertEqual(statuses["widget::verify::should_fail_c::all-properties"], "failed")
        self.assertEqual(statuses["widget::verify::should_fail_c::expected-panic"], "held")
        self.assertEqual(
            statuses["widget::verify::should_fail_c::input can be dereferenced"], "failed"
        )

    def test_output_attributed_to_an_unannounced_thread_is_refused(self):
        log = TERSE_PARALLEL_LOG.replace("Thread 1:\n", "Thread 9:\n", 1)
        with self.assertRaises(KaniAdapterError) as ctx:
            parse_kani_log(log, INVOCATION)
        self.assertIn("thread 9", str(ctx.exception))


class CountCrossCheckTests(unittest.TestCase):
    def test_trailer_mismatch_is_an_error_not_a_silent_drop(self):
        with self.assertRaises(KaniAdapterError) as ctx:
            parse_kani_log(COUNT_MISMATCH_LOG, INVOCATION)
        message = str(ctx.exception)
        self.assertIn("2 harness(es) in total", message)
        self.assertIn("the parser found 1", message)

    def test_success_failure_split_is_cross_checked_too(self):
        log = FAILURE_LOG.replace(
            "Complete - 0 successfully verified harnesses, 1 failures, 1 total.",
            "Complete - 1 successfully verified harnesses, 0 failures, 1 total.",
        )
        with self.assertRaises(KaniAdapterError):
            parse_kani_log(log, INVOCATION)

    def test_named_failed_harnesses_are_cross_checked(self):
        log = FAILURE_LOG.replace(
            "Verification failed for - widget::verify::check_copy_contract",
            "Verification failed for - widget::verify::some_other_harness",
        )
        with self.assertRaises(KaniAdapterError) as ctx:
            parse_kani_log(log, INVOCATION)
        self.assertIn("names", str(ctx.exception))

    def test_missing_trailer_is_refused_by_default(self):
        with self.assertRaises(KaniAdapterError) as ctx:
            parse_kani_log(NO_TRAILER_LOG, INVOCATION)
        self.assertIn("trailer", str(ctx.exception))

    def test_missing_trailer_can_be_accepted_deliberately(self):
        parsed = parse_kani_log_detailed(
            NO_TRAILER_LOG, INVOCATION, require_trailer=False
        )
        self.assertEqual(len(parsed.receipts), 1)
        self.assertIsNone(parsed.trailer)

    def test_a_harness_with_no_verdict_line_becomes_a_tool_error(self):
        log = NO_TRAILER_LOG.replace("VERIFICATION:- SUCCESSFUL\n", "")
        parsed = parse_kani_log_detailed(log, INVOCATION, require_trailer=False)
        [receipt] = parsed.receipts
        self.assertEqual(receipt.verdict, "error")
        self.assertEqual(receipt.failure_kind, "tool-error")
        validate_receipt_dict(receipt.to_dict())


class UnclassifiedLineTests(unittest.TestCase):
    def test_an_unrecognized_line_is_reported_with_its_number(self):
        lines = CLEAN_PASS_LOG.splitlines()
        lines.insert(3, "Quantum flux detected in property lattice")
        parsed = parse_kani_log_detailed("\n".join(lines) + "\n", INVOCATION)
        self.assertEqual(len(parsed.unclassified_lines), 1)
        self.assertEqual(parsed.unclassified_lines[0]["line"], 4)
        self.assertIn("Quantum flux", parsed.unclassified_lines[0]["text"])
        # Reported, not fatal: the receipts are still produced, and the
        # caller decides what an unreadable line means for them.
        self.assertEqual(len(parsed.receipts), 1)

    def test_tool_error_diagnostics_are_captured_separately(self):
        lines = CLEAN_PASS_LOG.splitlines()
        lines.insert(3, "error: could not compile `widget_core`")
        parsed = parse_kani_log_detailed("\n".join(lines) + "\n", INVOCATION)
        self.assertEqual(parsed.unclassified_lines, ())
        self.assertEqual(parsed.diagnostics[0]["kind"], "tool-error-diagnostic")


class ControlReceiptTests(unittest.TestCase):
    def test_observed_is_measured_from_the_run_not_declared(self):
        invocation = dict(
            INVOCATION,
            control={"kind": "mutation", "expectation": "red", "of_claim": "claim-widget-copy"},
        )
        [receipt] = parse_kani_log(FAILURE_LOG, invocation)
        self.assertEqual(receipt.control.kind, "mutation")
        self.assertEqual(receipt.control.expectation, "red")
        self.assertEqual(receipt.control.observed, "red")
        self.assertTrue(receipt.control.passed())
        validate_receipt_dict(receipt.to_dict())

    def test_a_control_that_did_not_behave_as_predicted_records_what_happened(self):
        invocation = dict(
            INVOCATION,
            control={"kind": "ablation", "expectation": "red", "of_claim": "claim-widget-copy"},
        )
        [receipt] = parse_kani_log(CLEAN_PASS_LOG, invocation)
        self.assertEqual(receipt.control.observed, "green")
        self.assertFalse(receipt.control.passed())

    def test_an_errored_control_run_observes_error_not_a_colour(self):
        invocation = dict(
            INVOCATION,
            control={"kind": "ablation", "expectation": "red", "of_claim": "claim-widget-copy"},
        )
        [receipt] = parse_kani_log(UNSUPPORTED_LOG, invocation)
        self.assertEqual(receipt.control.observed, "error")
        self.assertFalse(receipt.control.passed())

    def test_a_sat_expectation_is_measured_from_the_cover_obligations(self):
        invocation = dict(
            INVOCATION,
            control={"kind": "planted-twin", "expectation": "sat", "of_claim": "claim-widget-copy"},
        )
        [satisfied] = parse_kani_log(CLEAN_PASS_LOG, invocation)
        self.assertEqual(satisfied.control.observed, "sat")
        [unsatisfied] = parse_kani_log(UNSATISFIABLE_COVER_LOG, invocation)
        self.assertEqual(unsatisfied.control.observed, "unsat")

    def test_declaring_observed_in_the_invocation_is_refused(self):
        invocation = dict(
            INVOCATION,
            control={
                "kind": "mutation", "expectation": "red", "observed": "red",
                "of_claim": "claim-widget-copy",
            },
        )
        with self.assertRaises(KaniAdapterError) as ctx:
            parse_kani_log(FAILURE_LOG, invocation)
        self.assertIn("measured", str(ctx.exception))

    def test_of_claim_defaults_to_the_receipts_own_claim(self):
        invocation = dict(INVOCATION, control={"kind": "mutation", "expectation": "red"})
        [receipt] = parse_kani_log(FAILURE_LOG, invocation)
        self.assertEqual(receipt.control.of_claim, "claim-widget-copy")


class InvocationRecordTests(unittest.TestCase):
    def test_every_required_key_is_required(self):
        for key in (
            "claim_id", "candidate_id", "subject", "toolchain", "checker",
            "bound", "env_assumptions",
        ):
            with self.subTest(missing=key):
                invocation = {k: v for k, v in INVOCATION.items() if k != key}
                with self.assertRaises(KaniAdapterError) as ctx:
                    parse_kani_log(CLEAN_PASS_LOG, invocation)
                self.assertIn(key, str(ctx.exception))

    def test_an_unknown_key_is_refused_rather_than_ignored(self):
        invocation = dict(INVOCATION, tolchain={"typo": True})
        with self.assertRaises(KaniAdapterError) as ctx:
            parse_kani_log(CLEAN_PASS_LOG, invocation)
        self.assertIn("tolchain", str(ctx.exception))

    def test_toolchain_features_must_be_stated_explicitly(self):
        toolchain = {k: v for k, v in INVOCATION["toolchain"].items() if k != "features"}
        invocation = dict(INVOCATION, toolchain=toolchain)
        with self.assertRaises(KaniAdapterError) as ctx:
            parse_kani_log(CLEAN_PASS_LOG, invocation)
        self.assertIn("features", str(ctx.exception))

    def test_nested_required_keys_are_required(self):
        invocation = dict(INVOCATION, subject={"repo": "example/widget"})
        with self.assertRaises(KaniAdapterError) as ctx:
            parse_kani_log(CLEAN_PASS_LOG, invocation)
        self.assertIn("commit", str(ctx.exception))


if __name__ == "__main__":
    unittest.main()
