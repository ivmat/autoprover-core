# autoprover-core

Machine-checked Lean proofs, and the architecture of the kind of
automated proving pipeline that produces such corpora.

## Contents

- `corpus/` — 53 Lean modules formalizing classical results, bounded
  variants, and counterexamples across seven areas (distributed systems,
  order theory, concurrency, process calculi, security, probability,
  reliability). Pure Lean core, no dependencies.
  Build: `cd corpus && lake build`.
- `docs/` — the architecture of an automated proving system
  ([ARCHITECTURE.md](docs/ARCHITECTURE.md)) and the interface discipline
  it depends on ([INTERFACES.md](docs/INTERFACES.md)).

## Claims

Every proof is checked by the Lean kernel; the claim of each file is
exactly its theorem statements, as accepted by the kernel, under the
hypotheses named there. The classical results are attributed to their
origins and claim no novelty.

## Scope

The pipeline pattern documented here covers domains where a sound
checker exists (a proof kernel, a model checker). Where no such oracle
exists, different machinery is required; that is out of scope here.

Toolchains are pinned per package. License: Apache-2.0.
