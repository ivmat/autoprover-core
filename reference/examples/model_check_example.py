#!/usr/bin/env python3
"""Worked example: `autoprover_ref.model_checker` driving a tiny bounded
model checker through four toy scenarios. The first three demonstrate all
four obligation statuses `receipt.schema.json` makes first-class
(INTERFACES.md property 2): `held`, `vacuous`, `not-exercised`, `failed`.
The fourth demonstrates the finding those statuses cannot express — a
precondition no explored state violated.

  - Scenario 1: a 3-state traffic light (`red -> green -> yellow -> red`).
    Bounded exploration reaches a fixed point (the whole reachable set is
    seen) well within the bound, so it is *exhaustive*. Two obligations
    are checked against it:
      - "the light never gets stuck"       -> `held` (true everywhere).
      - "maintenance mode, if entered, is safe" -> `vacuous` (the light
        never enters maintenance in this system at all, and because the
        exploration was exhaustive, that absence is a genuine fact about
        the system, not an artifact of not looking hard enough).
    This scenario is driven all the way through `KernelGate` ->
    `Pipeline` twice, because "no obligation FAILED" and "every
    obligation was established" are different statements:
      - with both obligations, the run is accepted by the checker (a
        `vacuous` status is not a failure) and REFUSED by the audit
        layer, which reads the receipt's own obligation bucket and will
        not let a never-established obligation into the accepted set;
      - with only the obligation that held, the same wiring ratchets the
        result like any other acceptance - while never carrying a
        kernel-grade certificate.

  - Scenario 2: a long linear counter (`0 -> 1 -> 2 -> ...`), explored
    with a bound far smaller than its reachable set. The exploration is
    *not* exhaustive (states past the bound were never visited). One
    obligation is checked - "counts above 500 stay in a valid range" -
    but no explored state satisfies "above 500", so the obligation is
    `not-exercised`: the bound, not the system's semantics, is why
    nothing was seen. This is the same "no counterexample found" ambiguity
    ARCHITECTURE.md §5 describes for real bounded model checkers, made
    structurally visible instead of collapsed into a false `vacuous` (or
    worse, a false `held`).

  - Scenario 3: the same traffic light with one extra, buggy transition
    (`yellow -> stuck`, alongside the normal `yellow -> red`). Exhaustive
    exploration finds the stuck state directly reachable, so "the light
    never gets stuck" comes back `failed`, with the stuck state recorded
    as a counterexample. Driven through the same `KernelGate` ->
    `Pipeline` wiring as scenario 1, this shows the failing receipt is
    correctly kept out of the ratchet.

  - Scenario 4: the same two traffic lights, checked against an
    obligation whose guard is "the light is not stuck". Against the
    correct light, every explored state satisfies that guard — it prunes
    nothing, the implication is never exercised as an implication, and
    `audit.check_unexercised_hypothesis` flags it
    (`failure_reason="unexercised-hypothesis"`). Against the buggy light,
    which can reach `stuck`, the same guard prunes a state and the audit
    passes. Note what this is not: the obligation `held` in both runs.
    A `held` status cannot distinguish "checked on both sides of the
    guard" from "the guard did no work", which is exactly why this is a
    separate audit-layer finding rather than a fifth status.

See `autoprover_ref/model_checker.py` for the module this drives and
`reference/README.md` for how this fits the rest of the pipeline.
"""

from __future__ import annotations

import sys
from pathlib import Path

EXAMPLES_DIR = Path(__file__).resolve().parent
REFERENCE_DIR = EXAMPLES_DIR.parent
sys.path.insert(0, str(REFERENCE_DIR))

from autoprover_ref.audit import TargetProvenance, run_audit  # noqa: E402
from autoprover_ref.kernel_gate import KernelGate  # noqa: E402
from autoprover_ref.model_checker import (  # noqa: E402
    ModelObligation,
    TransitionSystem,
    check_obligations,
    explore,
    hypothesis_coverage,
    model_checker_command,
)
from autoprover_ref.pipeline import Pipeline  # noqa: E402
from autoprover_ref.queue import TargetQueue  # noqa: E402
from autoprover_ref.ratchet import Ratchet  # noqa: E402


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
        description="the light must never end up in a stuck state",
    ),
    ModelObligation(
        id="maintenance_mode_is_safe",
        precondition=lambda s: s == "maintenance",
        property=lambda s: True,
        description="if the light ever enters maintenance mode, it stays safe there",
    ),
]


# An obligation whose guard the correct light never prunes, and the buggy
# one does — the contrast scenario 4 turns into two different audit
# verdicts on an obligation that `held` either way.
NOT_STUCK_OBLIGATION = ModelObligation(
    id="not_stuck_implies_cycling",
    precondition=lambda s: s != "stuck",
    property=lambda s: s in ("red", "green", "yellow"),
    description="a light that is not stuck is in one of the three cycle states",
)


def counter_system(cap: int = 1000) -> TransitionSystem:
    def successors(n: int):
        return [n + 1] if n < cap else []

    return TransitionSystem(name="counter", initial_states=(0,), successors=successors)


COUNTER_OBLIGATIONS = [
    ModelObligation(
        id="large_count_stays_valid",
        precondition=lambda n: n >= 500,
        property=lambda n: n < 10_000,
        description="counts above 500 stay within a valid range",
    ),
]


def print_obligation_results(exploration, obligations) -> dict:
    results = check_obligations(exploration, obligations)
    print(
        f"  exploration: {len(exploration.visited)} state(s) visited, "
        f"exhaustive={exploration.exhaustive}"
    )
    statuses = {}
    for r in results:
        statuses[r.id] = r.status
        extra = f" counterexample={r.counterexample!r}" if r.counterexample is not None else ""
        print(f"  obligation {r.id!r}: {r.status}{extra}")
    return statuses


def scenario_1_traffic_light() -> dict:
    print("=== scenario 1: traffic light (exhaustive) — held + vacuous ===")
    exploration = explore(traffic_light_system(), bound=10)
    statuses = print_obligation_results(exploration, TRAFFIC_LIGHT_OBLIGATIONS)

    run_dir = EXAMPLES_DIR / "_run"
    run_dir.mkdir(exist_ok=True)
    provenance = TargetProvenance(
        source="reference/examples/model_check_example.py:scenario_1",
        statement_text="the traffic light never enters a stuck state",
    )

    def drive(obligations, target_id, candidate_id):
        gate = KernelGate(
            checker_command=model_checker_command(
                traffic_light_system(), obligations, bound=10
            ),
            checker_name="toy-bounded-checker",
            checker_version="0.1.0",
            kind="model-checker",
            toolchain_id="toy-bounded-checker-toolchain",
        )
        pipeline = Pipeline(
            queue=TargetQueue(run_dir / "model_check_queue.jsonl"),
            gate=gate,
            ratchet=Ratchet(run_dir / "model_check_ratchet.jsonl"),
            receipts_dir=run_dir / "model_check_receipts",
        )
        result = pipeline.run_target(
            target_id=target_id,
            candidate_id=candidate_id,
            candidate_file="traffic_light.model",
            provenance=provenance,
            obligation_ids=[o.id for o in obligations],
            harness="bounded_bfs(traffic_light)",
            bound=10,
            env_assumptions="single traffic light, no external resets",
        )
        return pipeline, result

    print("  driving BOTH obligations through KernelGate -> Pipeline...")
    pipeline, result = drive(
        TRAFFIC_LIGHT_OBLIGATIONS, "light_never_stuck_and_maintenance", "scenario1-v1",
    )
    print(f"  receipt.verdict={result.kernel_receipt.verdict!r} "
          f"statuses={[o.status for o in result.kernel_receipt.obligations]}")
    print(f"  audit verdict={result.audit_verdict.verdict!r} "
          f"failure_reason={result.audit_verdict.failure_reason!r}")
    print(f"  pipeline final_state={result.final_state!r}")
    # The checker accepted the run: nothing FAILED. The audit layer still
    # refuses it, because one obligation was never established at all.
    assert result.kernel_receipt.verdict == "accepted"
    assert result.audit_verdict.failure_reason == "vacuous-precondition"
    assert result.final_state == "queued"
    assert "light_never_stuck_and_maintenance" not in pipeline.ratchet.accepted_targets

    print("  driving only the obligation that held -> ratchet...")
    pipeline, result = drive(
        [TRAFFIC_LIGHT_OBLIGATIONS[0]], "light_never_stuck", "scenario1-held-v1",
    )
    receipt = result.kernel_receipt
    print(f"  receipt.checker.kind={receipt.checker.kind!r} certificate={receipt.certificate!r}")
    print(f"  receipt.harness={receipt.harness!r} bound={receipt.bound!r}")
    print(f"  pipeline final_state={result.final_state!r}")
    print(f"  ratchet accepted_targets={sorted(pipeline.ratchet.accepted_targets)}")
    assert receipt.checker.kind == "model-checker"
    assert receipt.certificate is None, "a model-checker receipt must never carry a certificate"
    assert receipt.harness and receipt.bound is not None and receipt.env_assumptions
    assert result.final_state == "accepted"
    assert "light_never_stuck" in pipeline.ratchet.accepted_targets
    return statuses


def scenario_2_counter() -> dict:
    print("\n=== scenario 2: counter (bound-truncated) — not-exercised ===")
    exploration = explore(counter_system(), bound=5)
    statuses = print_obligation_results(exploration, COUNTER_OBLIGATIONS)
    assert not exploration.exhaustive, "scenario 2 must be a truncated exploration"
    return statuses


def scenario_3_buggy_traffic_light() -> dict:
    print("\n=== scenario 3: buggy traffic light (exhaustive) — failed ===")
    exploration = explore(traffic_light_system(buggy=True), bound=10)
    statuses = print_obligation_results(exploration, TRAFFIC_LIGHT_OBLIGATIONS)

    print("  driving through KernelGate -> Pipeline (must NOT reach the ratchet)...")
    run_dir = EXAMPLES_DIR / "_run"
    run_dir.mkdir(exist_ok=True)
    gate = KernelGate(
        checker_command=model_checker_command(
            traffic_light_system(buggy=True), TRAFFIC_LIGHT_OBLIGATIONS, bound=10
        ),
        checker_name="toy-bounded-checker",
        checker_version="0.1.0",
        kind="model-checker",
        toolchain_id="toy-bounded-checker-toolchain",
    )
    pipeline = Pipeline(
        queue=TargetQueue(run_dir / "model_check_buggy_queue.jsonl"),
        gate=gate,
        ratchet=Ratchet(run_dir / "model_check_buggy_ratchet.jsonl"),
        receipts_dir=run_dir / "model_check_buggy_receipts",
    )
    provenance = TargetProvenance(
        source="reference/examples/model_check_example.py:scenario_3",
        statement_text="the traffic light never enters a stuck state",
    )
    result = pipeline.run_target(
        target_id="light_never_stuck",
        candidate_id="scenario3-v1",
        candidate_file="buggy_traffic_light.model",
        provenance=provenance,
        obligation_ids=[o.id for o in TRAFFIC_LIGHT_OBLIGATIONS],
        harness="bounded_bfs(buggy_traffic_light)",
        bound=10,
        env_assumptions="single traffic light with an unsafe transition",
    )
    receipt = result.kernel_receipt
    print(f"  receipt.verdict={receipt.verdict!r}")
    print(f"  pipeline final_state={result.final_state!r}")
    print(f"  ratchet accepted_targets={sorted(pipeline.ratchet.accepted_targets)}")
    assert receipt.verdict == "rejected"
    assert result.final_state == "queued"
    assert result.accepted_entry is None
    assert "light_never_stuck" not in pipeline.ratchet.accepted_targets
    return statuses


def scenario_4_unexercised_hypothesis() -> dict:
    print("\n=== scenario 4: a precondition nothing violated — unexercised-hypothesis ===")
    verdicts = {}
    for label, system in (("correct", traffic_light_system()),
                          ("buggy", traffic_light_system(buggy=True))):
        exploration = explore(system, bound=10)
        [status] = check_obligations(exploration, [NOT_STUCK_OBLIGATION])
        [coverage] = hypothesis_coverage(exploration, [NOT_STUCK_OBLIGATION])
        provenance = TargetProvenance(
            source="reference/examples/model_check_example.py:scenario_4",
            statement_text="a light that is not stuck is in one of the three cycle states",
            preconditions=("the light is not stuck",),
            non_vacuity_witness=(
                f"bounded exploration: {coverage.states_satisfying} state(s) satisfy it"
            ),
            obligation_evidence=(coverage,),
        )
        verdict = run_audit("not_stuck_implies_cycling", f"scenario4-{label}", provenance)
        verdicts[label] = verdict.failure_reason
        print(
            f"  {label} light: obligation status={status.status!r}, "
            f"precondition satisfied by {coverage.states_satisfying} state(s), "
            f"violated by {coverage.states_violating}"
        )
        print(f"    audit verdict={verdict.verdict!r} failure_reason={verdict.failure_reason!r}")
    assert verdicts["correct"] == "unexercised-hypothesis", verdicts
    assert verdicts["buggy"] is None, verdicts
    return verdicts


def main() -> int:
    all_statuses = {}
    all_statuses.update(scenario_1_traffic_light())
    all_statuses.update({f"counter.{k}": v for k, v in scenario_2_counter().items()})
    all_statuses.update({f"buggy.{k}": v for k, v in scenario_3_buggy_traffic_light().items()})
    audit_verdicts = scenario_4_unexercised_hypothesis()

    observed = set(all_statuses.values())
    expected = {"held", "vacuous", "not-exercised", "failed"}
    print(f"\nObligation statuses observed across all scenarios: {sorted(observed)}")
    ok = expected.issubset(observed)
    print(f"All four obligation statuses demonstrated: {ok}")
    flagged = audit_verdicts.get("correct") == "unexercised-hypothesis"
    print(f"Unexercised hypothesis flagged by the audit layer: {flagged}")
    return 0 if (ok and flagged) else 1


if __name__ == "__main__":
    raise SystemExit(main())
