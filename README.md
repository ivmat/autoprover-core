# autoprover-core

Machine-checked Lean proofs, the architecture of the kind of automated
proving pipeline that produces such corpora, and a runnable reference
implementation of that pipeline.

This README is the entry point and index, adapted from
[arc42](https://arc42.org) for a documentation-and-reference-code repo
(no deployed system, so §4 "runtime view" reads as an evidence flow, not
a running service).

## 1. Introduction & goals

The repository has three parts, meant to be read together:
`corpus/` (the machine-checked results), `docs/` (the architecture that
would produce such a corpus, and its honest limits), and `reference/`
(a runnable skeleton of that architecture). See
[`docs/EXTENDING.md`](docs/EXTENDING.md) for how a single result travels
through all three.

## 2. Context & scope

The pipeline pattern documented here covers domains where a sound
checker exists — a proof kernel, a model checker. Where no such oracle
exists, different machinery is required; that is out of scope here.
[`docs/LIMITATIONS.md`](docs/LIMITATIONS.md) states the boundary in
full: these are kernel-checked theorems about models, mostly safety
properties over finite structures, not verified implementations or
liveness guarantees.

Toolchains are pinned per package. License: Apache-2.0.

## 3. Building blocks

- **`corpus/`** — 74 Lean modules formalizing classical results, bounded
  variants, and counterexamples across seven areas (distributed systems,
  order theory, concurrency, process calculi, security, probability,
  reliability). Pure Lean core, no dependencies.
  [`CATALOG.md`](corpus/CATALOG.md) indexes every module — what it
  proves, its attribution, and an honest scope flag (`full` vs.
  deliberately `scoped`; see [`docs/GLOSSARY.md`](docs/GLOSSARY.md)).
  Build: `cd corpus && lake build`.
- **`docs/`** — the architecture of an automated proving system
  ([`ARCHITECTURE.md`](docs/ARCHITECTURE.md)), the interface discipline
  it depends on ([`INTERFACES.md`](docs/INTERFACES.md)), the honest
  scope of what the proofs do and do not establish
  ([`LIMITATIONS.md`](docs/LIMITATIONS.md)), the public derivation of
  the control-receipt machinery ([`PROVENANCE.md`](docs/PROVENANCE.md)),
  and how the pieces fit together and how to add one
  ([`EXTENDING.md`](docs/EXTENDING.md)).
- **`reference/`** — a dependency-free Python reference implementation
  of the pipeline the docs describe: versioned receipt and audit
  schemas, an evidence-driven work queue whose state is folded from an
  append-only log, a pluggable kernel gate, structural audit checks
  (vacuity, unexercised hypothesis, name/content correspondence, scope),
  a small bounded model checker that reports each obligation's status
  (`held` / `vacuous` / `not-exercised` / `failed`), and a monotone
  ratchet — with a test suite and a worked Lean example. It is a
  skeleton that makes the pattern concrete, not a product.
  Run: `cd reference && python3 run_tests.py`.
- **[`ASSUMPTIONS.md`](ASSUMPTIONS.md)** — top-level because it is a
  shared artifact: the assumptions the whole apparatus stands on
  (corpus, architecture, and any receipt the pipeline pattern
  produces), each with what would falsify it.

## 4. Runtime view: how one result flows

A target moves through a small, closed-state queue: `queued →
attempting → candidate-produced → kernel-checked → audited → accepted`,
with explicit retry/abandon exits at each gate. The kernel gate is
where soundness is enforced; the audit layer is heuristic semantic
checking — it can miss, and abstains where it cannot tell (see
[`docs/LIMITATIONS.md`](docs/LIMITATIONS.md) §7) — that catches what
the kernel structurally cannot see; the ratchet is what keeps
"accepted" from silently regressing.
See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) §2 for the queue and
its diagram, and §6 for the ratchet.

## 5. Schemas

The repository's machine-readable interface — its first-class artifacts
— are three versioned JSON Schemas in `reference/schema/`:

| file | version | role |
|---|---|---|
| [`reference/schema/receipt.schema.json`](reference/schema/receipt.schema.json) | 1.0.0 | The original verification-receipt contract. Kept at its published path; still valid for documents that declare it. |
| [`reference/schema/receipt.schema-2.0.0.json`](reference/schema/receipt.schema-2.0.0.json) | 2.0.0 | The current verification-receipt contract: adds `toolchain`, `subject`, `claim_id` provenance, a self-describing `error` verdict (`failure_kind`), per-obligation `coverage`, and the optional `control` block. |
| [`reference/schema/audit.schema.json`](reference/schema/audit.schema.json) | 1.2.0 | The versioned contract for a semantic audit verdict. |

See [`docs/INTERFACES.md`](docs/INTERFACES.md) for the doctrine these
schemas implement, and [ADR-002](docs/decisions/ADR-002-receipt-schema-versioning.md)
for why the receipt schema versions as a new file rather than a widened
one.

## 6. Architecture decisions

Recorded as short ADRs, indexed at
[`docs/decisions/README.md`](docs/decisions/README.md): the kernel gate
as where trust is decided, receipt schema versioning, the monotone
ratchet, and the abstain-vs-fail / vacuous-vs-not-exercised discipline.

## 7. Glossary

Every term of art — target, obligation, receipt, `claim_grade`, control
block, and the rest — is defined in
[`docs/GLOSSARY.md`](docs/GLOSSARY.md).

## 8. Limitations & assumptions

[`docs/LIMITATIONS.md`](docs/LIMITATIONS.md) states, as plainly as
possible, what the proofs in this repository do and do not establish.
[`ASSUMPTIONS.md`](ASSUMPTIONS.md) states what the whole apparatus
stands on underneath that — kernel soundness, toolchain semantics,
receipt authenticity, and the fact that no such list can ever be
complete.

## Claims

Every proof is checked by the Lean kernel; the claim of each file is
exactly its theorem statements, as accepted by the kernel, under the
hypotheses named there. The classical results are attributed to their
origins and claim no novelty.

## For users

Everything in sections 1–8 above is written for a user of the corpus,
the docs, or the reference implementation. Suggested reading order:

1. This README, for the map.
2. [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) §0 for the argument in
   brief, then the rest for the full pattern.
3. [`docs/LIMITATIONS.md`](docs/LIMITATIONS.md) and
   [`ASSUMPTIONS.md`](ASSUMPTIONS.md), before relying on any claim.
4. [`corpus/CATALOG.md`](corpus/CATALOG.md) or
   [`reference/README.md`](reference/README.md), depending on whether
   you're after the proofs or the pipeline code.
5. [`docs/GLOSSARY.md`](docs/GLOSSARY.md) and
   [`docs/decisions/`](docs/decisions/) as reference, as terms and
   design choices come up.

## For maintainers

[`maintainers/`](maintainers/) — working material for repo maintainers
and their agents; nothing in it is needed to use the corpus, the docs,
or the reference implementation.
