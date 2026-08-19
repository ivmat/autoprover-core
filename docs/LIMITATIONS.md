# Limitations and scope

A machine-checked corpus is easy to overread. This document states, as
plainly as possible, what the proofs in this repository do and do **not**
establish. None of it is a caveat buried to be found later — it is the
honest boundary of the claim, and reading it is part of reading the
corpus.

## 1. The kernel checks the object, not the label

A green proof means exactly this: the Lean kernel accepts a proof term
for the theorem *as stated*, under the hypotheses *as named*. It does not
mean the theorem's name is apt, that its English gloss matches its formal
content, or that the statement is the one a reader cares about. The kernel
has no opinion about names, comments, or changelog entries — it checks the
formal object and is silent about the label attached to it. A theorem
called `system_is_correct` that formally states only a triviality is still
kernel-green. Guarding against that gap is the job of the semantic audit
layer described in `ARCHITECTURE.md` §5 — and that layer is a set of
heuristics, not a sound procedure (see §7).

## 2. Models, not implementations

Every result here is a theorem about a **mathematical model** written in
Lean — a model of a protocol, a data type, an order, a lattice of security
levels. No result is connected to a running program by a refinement
theorem. A proof about a Lean model of two-phase commit says nothing,
formally, about any particular Erlang, Rust, or TLA⁺ artifact that also
calls itself two-phase commit. Bridging a model to an implementation is a
separate, substantial obligation this corpus does not discharge.

## 3. Safety, rarely liveness

The overwhelming majority of these results are **safety** properties —
"nothing bad happens": two majorities always intersect, a merge only
grows a state, an approved-and-not-revoked check never both approves and
revokes. **Liveness, progress, and termination are largely absent.**
Except where a specific module states otherwise, the corpus does not claim
that any modelled system makes progress, terminates, or avoids deadlock.
In particular, proving that a protocol's *safety* invariant holds is not a
claim that the protocol is *fault-tolerant* or *non-blocking*; the classic
blocking and impossibility results remain real and are not waved away by a
green safety proof.

## 4. Results differ in kind — a raw count overstates depth

Not all machine-checked results carry the same weight, and summing them
into a single "N theorems proved" number is misleading. It helps to keep
three kinds distinct:

- **Design validation** — true largely by construction of the model. The
  statement essentially restates a definition; the value is in pinning the
  definition down precisely, not in a hard argument.
- **Substantive verification** — a genuine theorem whose proof needs a
  non-trivial argument that could have failed.
- **Checker correspondence** — a proof that a *model of a checker* is
  sound, which is not the same as verifying the checker's actual
  implementation.

Where a module states which kind it is, cite that; where it does not, ask
the question before treating a result as deep. A headline number that
blends all three is a marketing artifact, not a measure of assurance.

## 5. Undischarged hypotheses and the trusted base

Each theorem is only as strong as the hypotheses named in its statement,
and several standing assumptions recur across the corpus and are **assumed,
never proved**:

- cryptographic idealizations — e.g. treating a hash link as injective /
  collision-free, or digests as opaque distinct tokens;
- distinctness / freshness assumptions — e.g. unique identifiers or
  sequence numbers;
- finiteness and bound assumptions — the state space, index set, or
  participant set is finite and often small.

Beneath all of it sits the trusted computing base: the Lean kernel and the
pinned toolchain version. "Kernel-checked" means "checked by *that* kernel";
a bug in the kernel or a mismatch in toolchain version is outside what any
proof here can attest to. Toolchains are pinned per package precisely so
that "checked" names a specific, reproducible checker.

The hypotheses above are the local half of this. The standing assumptions
the whole apparatus rests on — kernel soundness, toolchain semantics,
receipt authenticity, and the fact that no such list can ever be complete —
are enumerated, each with what would falsify it, in
[ASSUMPTIONS.md](ASSUMPTIONS.md).

## 6. Finite and bounded by construction

This corpus is written in **core Lean 4 with no external libraries** (no
mathlib). That is a deliberate constraint — it keeps the trusted base and
build small and the proofs self-contained — but it pushes many results
toward finite carriers and bounded, decidable models closed by `decide`.
A finite instance is evidence, not the general theorem: unless a module
explicitly proves the arbitrary-`n` (or arbitrary-carrier) form, read it
as the bounded statement it actually makes. Several modules include an
explicit non-vacuity witness for exactly this reason — to show the
interesting case is genuinely exercised, not vacuously true.

## 7. The reference implementation is a skeleton

The pipeline code in `reference/` exists to make the architecture concrete
and runnable, not to be a production system. Its prover is an injected
command; its audit checks (vacuity, unexercised hypothesis, name/content
correspondence, scope) are **honestly-labelled heuristics, not sound
decision procedures** — they
can miss and, where they cannot tell, they abstain rather than guess; its
bounded model checker is a small self-contained toy, not an industrial
tool. What it demonstrates is the *interface discipline* — evidence-driven
state, structured receipts, the kernel-versus-model-checker distinction,
a monotone ratchet — not robustness at scale.

## 8. Where the whole approach stops

The pipeline pattern documented here applies to domains where a **sound
checker exists** — a proof kernel, a bounded model checker for the
properties it decides. Where no such oracle is available, the central
soundness argument of this architecture does not apply and different
machinery is required. That boundary is not a limitation to be engineered
away here; it is the edge of the pattern's applicability, stated so it is
not mistaken for universal.

---

Stated positively: this repository is a set of precisely-stated,
kernel-checked theorems about models, most of them safety properties over
finite structures, plus a reference skeleton showing how such a corpus can
be produced under an interface discipline. That is a real and useful
thing. It is not a verified implementation of anything, not a liveness
guarantee, and not a single number to be quoted — and this document exists
so no reader mistakes it for one.
