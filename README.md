# autoprover-core

Machine-checked Lean proofs, the architecture of the kind of automated
proving pipeline that produces such corpora, and a runnable reference
implementation of that pipeline.

## Contents

- `corpus/` — 62 Lean modules formalizing classical results, bounded
  variants, and counterexamples across seven areas (distributed systems,
  order theory, concurrency, process calculi, security, probability,
  reliability). Pure Lean core, no dependencies.
  Build: `cd corpus && lake build`.
- `docs/` — the architecture of an automated proving system
  ([ARCHITECTURE.md](docs/ARCHITECTURE.md)), the interface discipline it
  depends on ([INTERFACES.md](docs/INTERFACES.md)), the honest scope of
  what the proofs do and do not establish ([LIMITATIONS.md](docs/LIMITATIONS.md)),
  and how the pieces fit together and how to add one
  ([EXTENDING.md](docs/EXTENDING.md)).
- `reference/` — a dependency-free Python reference implementation of the
  pipeline the docs describe: versioned receipt and audit schemas, an
  evidence-driven work queue whose state is folded from an append-only
  log, a pluggable kernel gate, structural audit checks (vacuity,
  name/content correspondence, scope), a small bounded model checker that
  reports each obligation's status (held / vacuous / not-exercised /
  failed), and a monotone ratchet — with a test suite and a worked Lean
  example. It is a skeleton that makes the pattern concrete, not a product.
  Run: `cd reference && python3 run_tests.py`.

## Claims

Every proof is checked by the Lean kernel; the claim of each file is
exactly its theorem statements, as accepted by the kernel, under the
hypotheses named there. The classical results are attributed to their
origins and claim no novelty.

## Scope

The pipeline pattern documented here covers domains where a sound
checker exists (a proof kernel, a model checker). Where no such oracle
exists, different machinery is required; that is out of scope here.
[LIMITATIONS.md](docs/LIMITATIONS.md) states the boundary in full — these
are kernel-checked theorems about models, mostly safety properties over
finite structures, not verified implementations or liveness guarantees.

Toolchains are pinned per package. License: Apache-2.0.
