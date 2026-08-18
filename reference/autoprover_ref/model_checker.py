"""A small, self-contained bounded model checker (ARCHITECTURE.md §4, §5;
INTERFACES.md property 2).

This module realizes the "exhaustive obligation-level bucket" the rest of
this package's docs argue for but a plain kernel invocation cannot produce
on its own: a bounded exploration of a tiny finite transition system,
reporting each named obligation's status as exactly one of `held` /
`vacuous` / `not-exercised` / `failed` — never collapsing "never got a
chance to check this" into "checked and it passed".

Besides the four-status reduction, this module also reports, per
obligation, how the explored states split across its PRECONDITION
(`hypothesis_coverage`) — how many satisfied it and how many violated it.
That is what lets the audit layer ask a question the status alone cannot
answer: was the implication ever exercised as an implication, or did the
guard prune nothing (see `audit.check_unexercised_hypothesis`)?

It is deliberately tiny and dependency-free: states are any hashable
Python value, transitions are a plain function ``state -> Iterable[state]``,
and obligations are a precondition predicate plus a property predicate,
both plain callables over a state. Nothing here is a general-purpose model
checker (no LTL, no symbolic state, no partial-order reduction) — it is
exactly enough breadth-first bounded exploration to make the
vacuous/not-exercised distinction concrete in runnable code, matching the
scope of the rest of ``reference/``.

The distinction the exploration is built around:

  - The explored set is *exhaustive* if bounded BFS from the initial
    states reaches a fixed point (no new states left to expand) before
    hitting the bound. In that case, an obligation whose precondition
    never held anywhere in the explored set is genuinely **vacuous** —
    the whole reachable state space was seen, and the precondition simply
    never fires.
  - If the bound is hit before BFS reaches a fixed point, the explored
    set is *not* exhaustive: states beyond the bound were never visited.
    An obligation whose precondition never held in what *was* explored is
    then **not-exercised**, not vacuous — the bound, not the semantics of
    the system, is why nothing was seen. This is exactly the ambiguity
    ARCHITECTURE.md §5 describes for real bounded model checkers ("no
    counterexample found" is indistinguishable from genuine coverage
    unless the tool also reports whether any input was actually
    explored), made structurally visible here instead of collapsed.
  - An obligation whose precondition *does* hold somewhere in the
    explored set is checked directly: **held** if the property holds on
    every state where the precondition held, **failed** (with a recorded
    counterexample) on the first state where it does not.

This module produces a `kernel_gate.CheckerCommand`-compatible callable
(`model_checker_command`), so a bounded-model-checker run flows through
exactly the same `KernelGate` / `Pipeline` / queue / ratchet wiring a
Lean-backed kernel run does — see `examples/model_check_example.py`. That
reuse is what enforces the kernel-vs-model-checker distinction from
ARCHITECTURE.md §4 in code, not just in this module: `KernelGate(kind=
"model-checker")` requires harness/bound/env_assumptions on every receipt
it produces and refuses to ever attach a certificate (see
`kernel_gate.py`, `receipts.Receipt.__post_init__`), so a model-checker
receipt produced through this module can never be mistaken for carrying a
re-runnable kernel-grade proof object.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Hashable, Iterable, Optional, Sequence

from .audit import ObligationHypothesisEvidence
from .kernel_gate import CheckerCommand, CheckerResult

__all__ = [
    "TransitionSystem",
    "ModelObligation",
    "ExplorationResult",
    "explore",
    "ObligationCheckResult",
    "check_obligations",
    "hypothesis_coverage",
    "model_checker_command",
]

State = Hashable


@dataclass(frozen=True)
class TransitionSystem:
    """A tiny finite transition system: a set of initial states plus a
    successor function. `name` is a human-readable identifier recorded in
    exploration results and receipts/details, not interpreted by this
    module."""

    name: str
    initial_states: tuple[State, ...]
    successors: Callable[[State], Iterable[State]]


@dataclass(frozen=True)
class ModelObligation:
    """One named obligation to check against an explored state space.

    `precondition` gates which explored states this obligation is even
    about (None means "every explored state is in scope"). `property` is
    the thing that must hold on every in-scope state. Both are plain
    predicates over a state — this module does not care what a state
    actually *is*, only what these two callables say about it."""

    id: str
    property: Callable[[State], bool]
    precondition: Optional[Callable[[State], bool]] = None
    description: str = ""


@dataclass(frozen=True)
class ExplorationResult:
    """The result of bounded breadth-first exploration: every state
    actually visited, in BFS discovery order, and whether that set is the
    system's full reachable closure (`exhaustive`) or was cut off by
    `bound` before reaching one (not exhaustive)."""

    system_name: str
    bound: int
    exhaustive: bool
    visited_order: tuple[State, ...]

    @property
    def visited(self) -> frozenset:
        return frozenset(self.visited_order)


def explore(system: TransitionSystem, bound: int) -> ExplorationResult:
    """Breadth-first explore `system` from its initial states, visiting at
    most `bound` distinct states. `bound` must be a positive integer —
    this is a *bounded* model checker; unbounded exploration of a
    possibly-infinite-state system is out of scope by design.

    Returns an `ExplorationResult` whose `exhaustive` flag is True iff BFS
    ran to a fixed point (emptied its frontier) strictly before the bound
    was reached — i.e. the returned `visited_order` really is the
    system's complete reachable set from its initial states, not merely a
    bound-sized prefix of it.
    """
    if bound < 1:
        raise ValueError(f"bound must be >= 1, got {bound}")

    visited: set = set()
    order: list = []
    # De-duplicate initial states while preserving first-seen order.
    frontier: list = list(dict.fromkeys(system.initial_states))

    while frontier:
        if len(visited) >= bound:
            # Bound reached with states still pending in the frontier:
            # exploration is truncated, not exhaustive.
            return ExplorationResult(
                system_name=system.name, bound=bound,
                exhaustive=False, visited_order=tuple(order),
            )
        state = frontier.pop(0)
        if state in visited:
            continue
        visited.add(state)
        order.append(state)
        for nxt in system.successors(state):
            if nxt not in visited:
                frontier.append(nxt)

    # Frontier emptied before the bound was hit: `order` is the system's
    # full reachable closure from its initial states.
    return ExplorationResult(
        system_name=system.name, bound=bound,
        exhaustive=True, visited_order=tuple(order),
    )


@dataclass(frozen=True)
class ObligationCheckResult:
    """One obligation's outcome plus the evidence behind it — richer than
    the schema-constrained `receipts.Obligation` (id + status only, see
    `schema/receipt.schema.json`), kept around for callers/examples that
    want to report on *why* a status was reached. `status` is exactly the
    value that ends up in a receipt's `obligations[].status` once reduced
    through `model_checker_command`."""

    id: str
    status: str  # "held" | "vacuous" | "not-exercised" | "failed"
    applicable_states_checked: int
    counterexample: Optional[State] = None


def check_obligations(
    exploration: ExplorationResult, obligations: Sequence[ModelObligation]
) -> list[ObligationCheckResult]:
    """Reduce one exploration to a per-obligation held/vacuous/
    not-exercised/failed status, using exactly the rule the module
    docstring states:

      - no state in the explored set satisfies the obligation's
        precondition -> `vacuous` if the exploration was exhaustive,
        `not-exercised` if it was bound-truncated;
      - at least one state satisfies the precondition and the property
        holds on every one of them -> `held`;
      - at least one state satisfies the precondition and the property
        fails on at least one of them -> `failed`, with the first such
        state recorded as a counterexample.
    """
    results: list[ObligationCheckResult] = []
    for obligation in obligations:
        precondition = obligation.precondition or (lambda _s: True)
        applicable = [s for s in exploration.visited_order if precondition(s)]

        if not applicable:
            status = "vacuous" if exploration.exhaustive else "not-exercised"
            results.append(ObligationCheckResult(
                id=obligation.id, status=status, applicable_states_checked=0,
            ))
            continue

        counterexample = None
        for state in applicable:
            if not obligation.property(state):
                counterexample = state
                break

        status = "failed" if counterexample is not None else "held"
        results.append(ObligationCheckResult(
            id=obligation.id, status=status,
            applicable_states_checked=len(applicable),
            counterexample=counterexample,
        ))
    return results


def hypothesis_coverage(
    exploration: ExplorationResult, obligations: Sequence[ModelObligation]
) -> list[ObligationHypothesisEvidence]:
    """Report, per obligation, how the explored states split across its
    precondition: how many satisfied it and how many VIOLATED it. This is
    the input `audit.check_unexercised_hypothesis` judges — an obligation
    no explored state violated the precondition of is one whose guard
    pruned nothing, so its implication was never exercised as an
    implication.

    This function only counts; it makes no judgment, exactly as
    `check_obligations` above only assigns statuses and makes no judgment
    about whether a status is acceptable. The `exhaustive` flag is copied
    onto every record because it is what tells a reader whether "nothing
    violated it" is a fact about the system's whole reachable set or only
    about this bounded run.

    Note the deliberate asymmetry with `check_obligations`: an obligation
    with no precondition is reported here with `has_precondition=False`
    and both counts zero rather than being treated as "precondition
    trivially true everywhere". An unconditional obligation is not a
    conditional one with a tautological guard — it never claimed to be
    restricted — and flattening the two would manufacture a finding out
    of an honest unconditional claim.
    """
    records: list[ObligationHypothesisEvidence] = []
    for obligation in obligations:
        if obligation.precondition is None:
            records.append(ObligationHypothesisEvidence(
                obligation_id=obligation.id,
                has_precondition=False,
                states_satisfying=0,
                states_violating=0,
                exhaustive=exploration.exhaustive,
            ))
            continue
        satisfying = 0
        violating = 0
        for state in exploration.visited_order:
            if obligation.precondition(state):
                satisfying += 1
            else:
                violating += 1
        records.append(ObligationHypothesisEvidence(
            obligation_id=obligation.id,
            has_precondition=True,
            states_satisfying=satisfying,
            states_violating=violating,
            exhaustive=exploration.exhaustive,
        ))
    return records


def model_checker_command(
    system: TransitionSystem,
    obligations: Sequence[ModelObligation],
    bound: int,
) -> CheckerCommand:
    """Build a `kernel_gate.CheckerCommand` that runs this module's
    bounded exploration and reports per-obligation status through
    `CheckerResult.obligation_statuses` — the seam `KernelGate` already
    has for a "richer checker" (see `kernel_gate.py`'s module docstring
    and `CheckerResult.obligation_statuses`). The candidate-file path
    `KernelGate.check` passes in is accepted for interface compatibility
    and otherwise ignored: this checker's actual input is the in-memory
    `TransitionSystem` and `obligations` closed over here, not a file on
    disk — there is nothing to read.

    Overall `CheckerResult.accepted` is False iff at least one obligation
    came back `failed`. A `vacuous` or `not-exercised` obligation does
    *not* itself fail the run — collapsing those into an overall failure
    would defeat the point of surfacing them as distinct, visible
    statuses; instead they are visible per-obligation in
    `obligation_statuses` (and, downstream, in the receipt's
    `obligations` array) for a caller to act on directly.
    """

    def run(_candidate_file: Path) -> CheckerResult:
        exploration = explore(system, bound)
        checked = check_obligations(exploration, obligations)
        statuses = {r.id: r.status for r in checked}
        any_failed = any(r.status == "failed" for r in checked)
        return CheckerResult(
            accepted=not any_failed,
            exit_code=1 if any_failed else 0,
            stdout=(
                f"explored {len(exploration.visited)} state(s) of system "
                f"{system.name!r} (exhaustive={exploration.exhaustive})"
            ),
            obligation_statuses=statuses,
        )

    return run
