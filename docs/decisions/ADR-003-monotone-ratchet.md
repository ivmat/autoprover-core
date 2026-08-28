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
resolved — rather than a quiet queue-state change. `reference/autoprover_ref/ratchet.py`
implements the monotone accepted set and its explicit removal path, with
dependency re-checking, matching this rule.

## Consequences

"Currently proven" always means what it says: a reader never has to ask
whether a passing corpus is stale relative to a dependency change,
because a dependency change that breaks a downstream result is a blocking
event, not a silent drift. `docs/ARCHITECTURE.md` draws the explicit
analogy to a regression-gated build: "the corpus is a ratchet, not a
snapshot." The cost is that a shared-dependency change can legitimately
halt progress on everything downstream of a newly-failing result until
the failure is resolved or the result is removed through the logged
removal path — there is no quieter option.
