# ADR-004: A result that was never exercised is not the same as one that failed — and a heuristic that cannot tell, abstains

**Status:** Accepted

## Context

`docs/INTERFACES.md` property 2 states the rule: "Every property or
obligation the tool was asked to check gets an entry in the result,
including the ones that were *not* meaningfully checked. A result that
only lists what passed and is silent about what wasn't exercised looks
identical to a result with genuine full coverage... The fix is
structural: give 'this obligation was vacuous / never reached' its own
explicit, first-class bucket in the output, so it is visibly distinct
from 'this obligation was checked and held.'"

`reference/schema/receipt.schema.json`'s obligation status is a
four-value closed enum for exactly this reason: `held` / `vacuous` /
`not-exercised` / `failed`. `reference/README.md` explains the split
between the latter two: if a bounded exploration reaches a fixed point
before hitting its bound, the explored set is the system's whole
reachable closure, and an obligation whose precondition never fired is
genuinely `vacuous`; if the bound is hit first, the same "precondition
never fired" outcome is instead `not-exercised`, because the bound,
rather than the system's semantics, is why nothing was seen.

The same discipline shows up one layer up, in the audit heuristics
themselves. `docs/LIMITATIONS.md` §7 states it directly: the audit checks
"can miss and, where they cannot tell, they abstain rather than guess."

## Decision

Two related but distinct rules are both enforced structurally, not left
to prose:

1. An obligation's status is never collapsed to a two-value
   held/failed split. `vacuous` and `not-exercised` are first-class,
   distinct values, so "never really tested" can never look identical to
   "held."
2. An audit check that cannot determine an answer abstains — passes
   without judging — rather than guessing at a verdict. `audit.check_scope`
   abstains on any target that doesn't declare a claimed scope;
   `audit.check_unexercised_hypothesis` abstains on any target that
   records no enumerated-obligation evidence; `audit.check_controls`
   abstains for probe-grade or ungraded claims.

## Consequences

A caller can always distinguish "this held," "this couldn't fire,"
"this wasn't reached because of a bound," and "this failed" from the
receipt alone, without inferring intent from an absence. An audit check
that abstains passes without judging, and says so in a field a caller can
branch on. Every check writes its own block into the audit verdict's
`details`, and every block carries `judged`: an abstention sets
`judged: false` together with a `reason` naming what was missing — "no
claimed_scope declared", "no enumerated-obligation evidence recorded",
"claim_grade is 'probe', not 'contract'", "no kernel receipt supplied to
judge obligation statuses". The `verdict` field alone still does not
separate "abstained" from "passed", deliberately: both are `pass`, because
an abstention is not a finding. A caller that wants the difference reads
`details.<check>.judged`, and it is on the artifact rather than only in the
heuristic's own logic. No target is credited with a judgment the heuristic
did not actually make. The cost is more states to handle at every
consumer of a receipt or audit verdict than a simple pass/fail model
would require — a cost the architecture treats as necessary, per
`docs/INTERFACES.md` property 3: "null never means a guess."
