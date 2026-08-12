"""Tests for model_checker.py: bounded exploration, the four obligation
statuses (held/vacuous/not-exercised/failed), the CheckerCommand adapter,
and the kernel-vs-model-checker receipt distinction at the queue/ratchet
boundary. Pure Python - no Lean, no installed packages needed.

Two toy transition systems are shared across the test classes below:

  - a 3-state traffic light cycle (red -> green -> yellow -> red), used
    to exhibit `held` and `vacuous` (it never enters a "maintenance"
    state, and exhaustive BFS proves that, not just fails to find it);
    a buggy variant adds an extra red->stuck-adjacent transition, used to
    exhibit `failed`.
  - a long linear counter (0 -> 1 -> 2 -> ...), explored with a bound far
    smaller than its reachable set, used to exhibit `not-exercised` (an
    obligation about large counts is never reached, and the truncated
    exploration honestly can't tell you whether it would hold).
"""

from __future__ import annotations

import unittest
from pathlib import Path

from autoprover_ref.audit import TargetProvenance
from autoprover_ref.kernel_gate import KernelGate
from autoprover_ref.model_checker import (
    ModelObligation,
    TransitionSystem,
    check_obligations,
    explore,
    model_checker_command,
)
from autoprover_ref.pipeline import Pipeline
from autoprover_ref.queue import State, TargetQueue
from autoprover_ref.ratchet import Ratchet

from _tmpdir import TempDirCase


def traffic_light_system(buggy: bool = False) -> TransitionSystem:
    def successors(state: str):
        if state == "red":
            return ["green"]
        if state == "green":
            return ["yellow"]
        if state == "yellow":
            return ["red", "stuck"] if buggy else ["red"]
        if state == "stuck":
            return []
        raise ValueError(f"unknown state {state!r}")

    return TransitionSystem(
        name="buggy_traffic_light" if buggy else "traffic_light",
        initial_states=("red",),
        successors=successors,
    )


TRAFFIC_LIGHT_OBLIGATIONS = [
    ModelObligation(
        id="light_never_stuck",
        property=lambda s: s != "stuck",
        description="the light must never end up in the stuck state",
    ),
    ModelObligation(
        id="maintenance_mode_is_safe",
        precondition=lambda s: s == "maintenance",
        property=lambda s: True,
        description="if the light ever enters maintenance mode, it is safe there",
    ),
]


def counter_system(cap: int = 1000) -> TransitionSystem:
    def successors(n: int):
        return [n + 1] if n < cap else []

    return TransitionSystem(name="counter", initial_states=(0,), successors=successors)


COUNTER_OBLIGATIONS = [
    ModelObligation(
        id="large_count_stays_valid",
        precondition=lambda n: n >= 500,
        property=lambda n: n < 10_000,
        description="counts above 500 (never reached under a tiny bound) stay in range",
    ),
]


class ExplorationTests(unittest.TestCase):
    def test_small_closed_system_is_exhaustive(self):
        result = explore(traffic_light_system(), bound=10)
        self.assertTrue(result.exhaustive)
        self.assertEqual(result.visited, frozenset({"red", "green", "yellow"}))

    def test_large_system_with_small_bound_is_not_exhaustive(self):
        result = explore(counter_system(), bound=5)
        self.assertFalse(result.exhaustive)
        self.assertEqual(len(result.visited), 5)
        self.assertEqual(result.visited, frozenset({0, 1, 2, 3, 4}))

    def test_buggy_system_reaches_stuck_state_and_is_exhaustive(self):
        result = explore(traffic_light_system(buggy=True), bound=10)
        self.assertTrue(result.exhaustive)
        self.assertIn("stuck", result.visited)

    def test_bound_below_one_raises(self):
        with self.assertRaises(ValueError):
            explore(traffic_light_system(), bound=0)

    def test_exploration_does_not_revisit_or_loop_forever(self):
        # The traffic light cycles back to "red"; explore() must not
        # re-expand an already-visited state (this would just be slow in
        # a bounded checker, but in an unbounded one it would hang).
        result = explore(traffic_light_system(), bound=1000)
        self.assertEqual(len(result.visited_order), len(set(result.visited_order)))


class CheckObligationsFourStatusesTests(unittest.TestCase):
    def test_held_status(self):
        exploration = explore(traffic_light_system(), bound=10)
        results = {r.id: r for r in check_obligations(exploration, TRAFFIC_LIGHT_OBLIGATIONS)}
        self.assertEqual(results["light_never_stuck"].status, "held")
        self.assertEqual(results["light_never_stuck"].applicable_states_checked, 3)
        self.assertIsNone(results["light_never_stuck"].counterexample)

    def test_vacuous_status(self):
        # Exhaustive exploration, precondition never satisfiable within
        # the reachable set -> genuinely vacuous, not just unexplored.
        exploration = explore(traffic_light_system(), bound=10)
        self.assertTrue(exploration.exhaustive)
        results = {r.id: r for r in check_obligations(exploration, TRAFFIC_LIGHT_OBLIGATIONS)}
        self.assertEqual(results["maintenance_mode_is_safe"].status, "vacuous")
        self.assertEqual(results["maintenance_mode_is_safe"].applicable_states_checked, 0)

    def test_not_exercised_status(self):
        # Bound-truncated exploration (not exhaustive); the same
        # precondition never fires in what *was* explored, but that's the
        # bound's fault, not the system's -> not-exercised, not vacuous.
        exploration = explore(counter_system(), bound=5)
        self.assertFalse(exploration.exhaustive)
        results = {r.id: r for r in check_obligations(exploration, COUNTER_OBLIGATIONS)}
        self.assertEqual(results["large_count_stays_valid"].status, "not-exercised")
        self.assertEqual(results["large_count_stays_valid"].applicable_states_checked, 0)

    def test_failed_status_with_counterexample(self):
        exploration = explore(traffic_light_system(buggy=True), bound=10)
        results = {r.id: r for r in check_obligations(exploration, TRAFFIC_LIGHT_OBLIGATIONS)}
        self.assertEqual(results["light_never_stuck"].status, "failed")
        self.assertEqual(results["light_never_stuck"].counterexample, "stuck")

    def test_same_precondition_is_vacuous_or_not_exercised_depending_only_on_exhaustiveness(self):
        # Same obligation, same "never actually satisfied in what we
        # saw" outcome - the label differs purely on whether the
        # exploration itself was exhaustive, which is exactly the
        # distinction this module exists to make visible.
        never_satisfiable_elsewhere = ModelObligation(
            id="never_seen", precondition=lambda s: s == "nope", property=lambda s: True,
        )
        exhaustive = explore(traffic_light_system(), bound=100)
        truncated = explore(traffic_light_system(), bound=1)
        self.assertTrue(exhaustive.exhaustive)
        self.assertFalse(truncated.exhaustive)
        exhaustive_status = check_obligations(exhaustive, [never_satisfiable_elsewhere])[0].status
        truncated_status = check_obligations(truncated, [never_satisfiable_elsewhere])[0].status
        self.assertEqual(exhaustive_status, "vacuous")
        self.assertEqual(truncated_status, "not-exercised")


class ModelCheckerCommandAdapterTests(unittest.TestCase):
    def test_accepted_when_no_obligation_fails(self):
        command = model_checker_command(traffic_light_system(), TRAFFIC_LIGHT_OBLIGATIONS, bound=10)
        result = command(Path("nonexistent-file-never-read.model"))
        self.assertTrue(result.accepted)
        self.assertEqual(result.exit_code, 0)
        self.assertEqual(result.obligation_statuses["light_never_stuck"], "held")
        self.assertEqual(result.obligation_statuses["maintenance_mode_is_safe"], "vacuous")

    def test_rejected_when_an_obligation_fails(self):
        command = model_checker_command(
            traffic_light_system(buggy=True), TRAFFIC_LIGHT_OBLIGATIONS, bound=10
        )
        result = command(Path("nonexistent-file-never-read.model"))
        self.assertFalse(result.accepted)
        self.assertEqual(result.exit_code, 1)
        self.assertEqual(result.obligation_statuses["light_never_stuck"], "failed")

    def test_not_exercised_does_not_itself_fail_the_run(self):
        command = model_checker_command(counter_system(), COUNTER_OBLIGATIONS, bound=5)
        result = command(Path("ignored.model"))
        self.assertTrue(result.accepted)
        self.assertEqual(result.obligation_statuses["large_count_stays_valid"], "not-exercised")


class KernelGateIntegrationTests(unittest.TestCase):
    """Runs the model checker through KernelGate itself (not just the
    CheckerCommand adapter in isolation) to confirm the receipt it
    produces obeys ARCHITECTURE.md §4's kernel-vs-model-checker
    distinction: harness/bound/env_assumptions present, no certificate,
    obligation statuses exhaustively reported including vacuous/
    not-exercised."""

    def _gate(self, system, obligations, bound) -> KernelGate:
        return KernelGate(
            checker_command=model_checker_command(system, obligations, bound),
            checker_name="toy-bounded-checker",
            checker_version="0.1.0",
            kind="model-checker",
            toolchain_id="toy-bounded-checker-toolchain",
        )

    def test_receipt_carries_harness_bound_env_and_no_certificate(self):
        gate = self._gate(traffic_light_system(), TRAFFIC_LIGHT_OBLIGATIONS, bound=10)
        receipt = gate.check(
            target_id="light_never_stuck", candidate_id="cand1",
            candidate_file="ignored.model",
            obligation_ids=[o.id for o in TRAFFIC_LIGHT_OBLIGATIONS],
            harness="bounded_bfs(traffic_light)", bound=10,
            env_assumptions="single traffic light, no external resets",
        )
        self.assertEqual(receipt.checker.kind, "model-checker")
        self.assertIsNone(receipt.certificate)
        self.assertEqual(receipt.harness, "bounded_bfs(traffic_light)")
        self.assertEqual(receipt.bound, 10)
        self.assertEqual(receipt.env_assumptions, "single traffic light, no external resets")
        self.assertEqual(receipt.verdict, "accepted")
        statuses = {o.id: o.status for o in receipt.obligations}
        self.assertEqual(statuses, {"light_never_stuck": "held", "maintenance_mode_is_safe": "vacuous"})

    def test_all_four_obligation_statuses_reachable_through_the_gate(self):
        # A single gate call whose obligation set spans failed, held, and
        # vacuous; not-exercised is exhibited separately (it needs a
        # non-exhaustive exploration, i.e. a different bound) in
        # test_not_exercised_reachable_through_the_gate below - together
        # this shows all four statuses flow through KernelGate correctly.
        gate = self._gate(traffic_light_system(buggy=True), TRAFFIC_LIGHT_OBLIGATIONS, bound=10)
        receipt = gate.check(
            target_id="t", candidate_id="c", candidate_file="ignored.model",
            obligation_ids=[o.id for o in TRAFFIC_LIGHT_OBLIGATIONS],
            harness="bounded_bfs(buggy_traffic_light)", bound=10,
            env_assumptions="single traffic light with an unsafe transition",
        )
        self.assertEqual(receipt.verdict, "rejected")
        statuses = {o.id: o.status for o in receipt.obligations}
        self.assertEqual(statuses["light_never_stuck"], "failed")
        self.assertEqual(statuses["maintenance_mode_is_safe"], "vacuous")

    def test_not_exercised_reachable_through_the_gate(self):
        gate = self._gate(counter_system(), COUNTER_OBLIGATIONS, bound=5)
        receipt = gate.check(
            target_id="t", candidate_id="c", candidate_file="ignored.model",
            obligation_ids=[o.id for o in COUNTER_OBLIGATIONS],
            harness="bounded_bfs(counter)", bound=5,
            env_assumptions="single linear counter, no wraparound",
        )
        self.assertEqual(receipt.verdict, "accepted")
        statuses = {o.id: o.status for o in receipt.obligations}
        self.assertEqual(statuses["large_count_stays_valid"], "not-exercised")

    def test_kernel_gate_still_requires_harness_bound_env_for_model_checker(self):
        gate = self._gate(traffic_light_system(), TRAFFIC_LIGHT_OBLIGATIONS, bound=10)
        with self.assertRaises(ValueError):
            gate.check(target_id="t", candidate_id="c", candidate_file="ignored.model")


class PipelineRatchetBoundaryTests(TempDirCase):
    """The kernel-vs-model-checker distinction at the ratchet boundary: a
    model-checker receipt with no failures can still be ratcheted (the
    ratchet only requires verdict == 'accepted' + an audit pass — it does
    not care which checker kind produced the receipt), but the accepted
    entry it stores must still honestly reflect that this was a
    model-checker verdict, never a kernel one: no certificate, harness/
    bound/env_assumptions present. A receipt with a failed obligation
    must never reach the ratchet at all."""

    def _pipeline(self, system, obligations, bound) -> Pipeline:
        gate = KernelGate(
            checker_command=model_checker_command(system, obligations, bound),
            checker_name="toy-bounded-checker",
            checker_version="0.1.0",
            kind="model-checker",
            toolchain_id="toy-bounded-checker-toolchain",
        )
        return Pipeline(
            queue=TargetQueue(self.tmp_path("queue.jsonl")),
            gate=gate,
            ratchet=Ratchet(self.tmp_path("ratchet.jsonl")),
            receipts_dir=self.tmp_path("receipts"),
        )

    def test_accepted_model_checker_receipt_flows_into_ratchet(self):
        pipeline = self._pipeline(traffic_light_system(), TRAFFIC_LIGHT_OBLIGATIONS, bound=10)
        provenance = TargetProvenance(
            source="synthetic", statement_text="the traffic light never gets stuck",
        )
        result = pipeline.run_target(
            target_id="light_never_stuck", candidate_id="cand1",
            candidate_file="ignored.model", provenance=provenance,
            obligation_ids=[o.id for o in TRAFFIC_LIGHT_OBLIGATIONS],
            harness="bounded_bfs(traffic_light)", bound=10,
            env_assumptions="single traffic light, no external resets",
        )
        self.assertEqual(result.final_state, State.ACCEPTED.value)
        self.assertIsNotNone(result.accepted_entry)
        self.assertIn("light_never_stuck", pipeline.ratchet.accepted_targets)

        # The accepted entry's own receipt must still honestly carry the
        # model-checker shape - never a certificate, always the
        # harness/bound/env triple its verdict is relative to.
        stored_receipt = pipeline.ratchet.entry_for("light_never_stuck").receipt
        self.assertEqual(stored_receipt.checker.kind, "model-checker")
        self.assertIsNone(stored_receipt.certificate)
        self.assertEqual(stored_receipt.harness, "bounded_bfs(traffic_light)")
        self.assertEqual(stored_receipt.bound, 10)
        self.assertIsNotNone(stored_receipt.env_assumptions)

    def test_failed_obligation_model_checker_receipt_never_reaches_ratchet(self):
        pipeline = self._pipeline(traffic_light_system(buggy=True), TRAFFIC_LIGHT_OBLIGATIONS, bound=10)
        provenance = TargetProvenance(
            source="synthetic", statement_text="the traffic light never gets stuck",
        )
        result = pipeline.run_target(
            target_id="light_never_stuck", candidate_id="cand1",
            candidate_file="ignored.model", provenance=provenance,
            obligation_ids=[o.id for o in TRAFFIC_LIGHT_OBLIGATIONS],
            harness="bounded_bfs(buggy_traffic_light)", bound=10,
            env_assumptions="single traffic light with an unsafe transition",
        )
        self.assertEqual(result.kernel_receipt.verdict, "rejected")
        self.assertEqual(result.final_state, State.QUEUED.value)
        self.assertIsNone(result.accepted_entry)
        self.assertNotIn("light_never_stuck", pipeline.ratchet.accepted_targets)


if __name__ == "__main__":
    unittest.main()
