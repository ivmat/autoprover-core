# ADR-003: The proven set is monotone; it only shrinks through a logged removal event

**Status:** Accepted

## Context

`docs/ARCHITECTURE.md` §6 states the rule for the proven set once a target
is kernel-checked and audit-passed: "The proven set is monotone by
construction: a result, once accepted, can only leave the set through an
explicit, logged removal event (a discovered unsoundness in a dependency,
a definition change that invalidates the statement) — never through a
silent re-run that happens to fail this time and gets treated as 'the old
result must have been wrong, moving on.'"

## Decision

Every accepted result is re-checked on every change to anything it
depends on (a shared definition, a library the kernel trusts, the kernel
version itself). A re-check failure is a loud, blocking, logged event —
it blocks further progress on anything downstream of that result until
resolved — rather than a quiet queue-state change.

`reference/autoprover_ref/ratchet.py` implements the parts of that rule a
library can implement, and only those. It holds the monotone accepted set
and its explicit logged removal path. `recheck_dependents` marks accepted
targets as owing a re-check because a named dependency changed, and
`record_recheck_result` records the outcome: the entry is refreshed when a
fresh receipt and audit still justify acceptance, and otherwise removed
with a loud `BlockingEvent` raised. That cycle is a re-verification path
and never a second way into the accepted set — it refuses a target with no
outstanding mark, a `changed_dep` the target was not marked for, and a
receipt/audit pair that is not about one artifact of this target, which is
the same validation `accept()` performs.

Two halves of the rule are deliberately left to the caller, and the
reference implementation does not pretend otherwise:

- **Which targets depend on what.** The ratchet holds no dependency graph.
  The set of dependents is supplied by the caller on each
  `recheck_dependents(changed_dep, dependents)` call, so "every accepted
  result is re-checked on every change to anything it depends on" is a
  guarantee about the dependencies the caller actually declares, not one
  the library can make on its own.
- **Blocking downstream progress.** `BlockingEvent` makes the failure
  impossible to miss; it does not stop anything. A real scheduler would
  refuse to schedule work depending on a target with an open blocking
  event. This module surfaces the event and leaves that enforcement to
  whatever schedules the work.

## Consequences

"Currently proven" means what it says relative to the dependencies the
ratchet has recorded and rechecked: a reader does not have to ask
whether a passing corpus silently drifted, because a *recorded*
dependency change that breaks a downstream result is a blocking event,
not a silent drift. That is a monotonicity guarantee with explicit,
logged removal — not an unconditional freshness claim; it holds only
for dependencies the ratchet actually tracks, and it inherits the
standing assumptions `ASSUMPTIONS.md` states for the rest of the
apparatus (kernel soundness, honest receipts, and the rest).
`docs/ARCHITECTURE.md` draws the explicit analogy to a regression-gated
build: "the corpus is a ratchet, not a snapshot." The cost is that a
shared-dependency change can legitimately
halt progress on everything downstream of a newly-failing result until
the failure is resolved or the result is removed through the logged
removal path — there is no quieter option.
