# How the pieces fit, and how to add one

This repository has three parts that are meant to be read together:

- `docs/` — the architecture (`ARCHITECTURE.md`), the interface discipline
  (`INTERFACES.md`), and the honest scope (`LIMITATIONS.md`).
- `corpus/` — the machine-checked results themselves, one classical result
  per Lean module.
- `reference/` — a runnable skeleton of the pipeline the docs describe.

This document explains how a single result travels through the pipeline,
and what it takes to add a new one to the corpus. It is a description of
the discipline, not an invitation to a particular contribution process.

## How one result flows through the pipeline

Follow a single target from idea to accepted, matching the sections of
`ARCHITECTURE.md` to the code in `reference/autoprover_ref/`:

1. **Target selection (§1).** A target is a precise statement plus its
   provenance: where the statement came from (a paper, a textbook) and
   what it is allowed to claim. In the reference code a target enters the
   queue with a provenance record; it guarantees a well-formed statement,
   *not* that the statement is true.
2. **Queue (§2).** The target lives in a work queue with a small closed set
   of states (`queue.py`). Its state is never a prose status an agent
   writes — it is folded from an append-only log of evidence events. A
   state that no evidence justifies cannot be set.
3. **Prover (§3).** A prover proposes a candidate proof. In the reference
   implementation the prover is an *injected command* — the point of the
   architecture is that soundness never depends on how plausible a
   candidate looks, only on what the gate downstream decides.
4. **Kernel gate (§4).** The candidate is checked by a sound oracle
   (`kernel_gate.py`). For a proof kernel the receipt carries a
   re-runnable certificate; for a bounded model checker
   (`model_checker.py`) the receipt is valid only relative to its harness,
   bound, and environment assumptions, and carries no kernel-grade
   certificate — the code enforces that distinction in the receipt type,
   not in a comment.
5. **Audit (§5).** A kernel-accepted candidate still has to pass a semantic
   audit (`audit.py`): is the precondition satisfiable (non-vacuous), does
   the statement correspond to its claimed name and scope? These checks are
   honest heuristics — they abstain rather than guess — and a failure
   routes the target back to the queue, it is not silently dropped.
6. **Ratchet (§6).** Only a target with both a kernel-accept receipt and an
   audit pass is accepted into the monotone proven set (`ratchet.py`). It
   leaves that set only through an explicit, logged removal event.

Every boundary above emits a structured receipt (§7), and the five
result-as-API properties of `INTERFACES.md` apply to each one.

## Anatomy of a corpus module

Every module in `corpus/` follows the same shape. To add a result, mirror
an existing module in the same area, and hold to these rules:

- **One result per module, one classical source.** The file is named for
  the result; the namespace is flat (`namespace AutoproverCorpus.<Name>`).
- **A header that states the claim exactly.** Open with a `/- ... -/` block
  giving: the module path, a plain-language statement of what is proved, an
  `Attribution:` line crediting the real academic origin (these are
  classical results; they claim no novelty), and the standard disclaimer
  that the claim is exactly the theorem statements as accepted by the
  kernel, under their named hypotheses.
- **A name is a claim.** The module and theorem names must be defensible to
  a reviewer who reads only the statements. If you can prove only a
  restricted form — a finite instance, one direction of a biconditional, a
  safety property without the matching liveness — then *name it for the
  restricted form* and add a prominent scope note saying what is not
  proved. An honest fragment is worth more than an overclaiming headline.
- **Show non-vacuity.** Where a result is a "nothing bad happens" property,
  include a concrete, `decide`-checked witness that the interesting case is
  genuinely reachable/exercised, so the property is not true merely because
  its precondition never fires.
- **Register it.** Add an `import AutoproverCorpus.<Area>.<Name>` line to
  `corpus/AutoproverCorpus.lean`, placed alphabetically in its area block —
  the library builds what is imported there.

## Working in core Lean

The corpus is deliberately **core Lean 4 with no external libraries** (no
mathlib), which keeps the trusted base and the build small and self-
contained. The cost is that many familiar conveniences are absent, and a
few general facts about core Lean are worth knowing before you start:

- Tactics like `by_contra`, `ring`, `push_neg`, and `norm_num` are library
  tactics, not core; the core equivalents are `Classical.byContradiction`,
  `grind`, `omega`, and `decide`, chosen per goal.
- There is no `Real`; prefer `Nat`, `Int`, `Bool`, `Fin`, and other finite,
  decidable models. `Rat` literal arithmetic is a sharp edge because its
  operations are irreducible, so `decide`/`rfl` can get stuck on it — a
  reason most results here live over `Nat`/`Int` or finite carriers.
- `decide` needs its predicates reducible: mark small definitions used in
  concrete `decide`-checked examples `abbrev` (or `@[reducible]`), or
  instance synthesis will not unfold them.

## Building and checking

- Build the corpus: `cd corpus && lake build` (build one module at a time
  while developing; the whole library is rebuilt from the imports in
  `AutoproverCorpus.lean`).
- Run the reference implementation's tests: `cd reference && python3
  run_tests.py` (standard library only, no Lean required).
- Run the worked pipeline example (needs Lean on the path): `cd reference &&
  python3 examples/run_example.py`.

The two build systems are independent and pinned separately; a change to
one does not silently affect the other.
