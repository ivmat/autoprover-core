# Architecture: how to build an autonomous proving system

This document describes a general pattern for a system that grows a
machine-checked body of mathematical results with LLMs doing the proof
search. It is written as a how-to, not as a report on any particular
running instance: the point is the shape, not the numbers.

The thesis behind every design choice here is simple: **rigor has to live
on the interfaces, not just inside the components.** An LLM prover, a proof
checker, and an audit step can each be individually well-built and the
system can still be untrustworthy, if the *handoffs* between them are
prose ("looks fine to me") instead of contracts (typed inputs, typed
verdicts, checkable postconditions). Every section below follows the same
template: state what a component may **assume** on entry, and what it must
**guarantee** on exit, as a structured artifact — never as a sentence.

## 1. Target selection and decomposition

The system needs a supply of things to prove. A target is a candidate
theorem statement: something with a precise, checkable meaning in the
target logic, plus enough context (definitions, prior lemmas, the source
it's drawn from) for a prover to attempt it.

Two disciplines matter here, both well established in interactive-theorem-
proving practice:

- **Decomposition before proof search.** A large target is broken into a
  dependency graph of smaller lemmas before any prover touches it. This is
  standard mathematical practice — big theorems are proved via a chain of
  smaller ones — and it matters more, not less, once an LLM is doing the
  search: smaller targets are easier to state precisely, easier to check
  for vacuity (see §4), and easier to re-attempt independently when one
  step fails.
- **Explicit provenance.** Every target records where its statement came
  from (a textbook, a paper, a spec) and, once proved, what it's allowed to
  claim. This is the assumption that closes the "kernel proved *something*,
  but does it match what we said it proved" gap discussed below.

**Contract:** a target entering the queue guarantees it has a well-formed
statement in the target logic and a provenance record. It does not
guarantee it is true, or that it is stated the way its eventual name will
claim.

## 2. A work queue with explicit states

Everything the system is working on lives in a queue with a small, closed
set of states and one-directional transitions. A representative state
machine:

```
queued → attempting → candidate-produced → kernel-checked
                                          ↘ kernel-rejected → queued (retry) | abandoned
kernel-checked → audited → accepted (ratcheted) | audit-rejected → queued (retry) | abandoned
```

The state is not a status field an agent writes prose into — it is a
value produced by a specific transition function, driven by a specific
artifact (a checker verdict, an audit verdict). No component may set a
state it did not produce evidence for. This is the same discipline used in
any well-built build or CI pipeline: state changes are caused by evidence,
not asserted.

**Why a queue at all, rather than a single monolithic loop:** it makes
partial failure legible. A target that fails at the prover stage is
distinguishable from one that fails at the kernel stage or the audit
stage, and each failure mode calls for a different response (retry with
more context, fix the statement, escalate to a human).

## 3. LLM provers generating candidate proofs

A prover component takes a target (statement + context) and attempts to
produce a candidate proof term or script in the target logic. This is the
generative, unreliable part of the system by design — it is expected to
be wrong often, expected to hallucinate, expected to produce proofs of the
wrong statement or no proof at all.

**Assume:** a well-formed target with provenance, as guaranteed by §1.
**Guarantee:** either a candidate artifact in the exact syntax the checker
in §4 consumes, tagged with the target it claims to address, or an
explicit "no candidate" result. A prover output is never treated as a
verdict — it is only ever an *input* to the next gate.

This is the place where LLM-specific practice differs from older
automated-theorem-proving pipelines mainly in scale and cost, not in kind:
more candidates can be tried per unit time, so the system's soundness has
to depend entirely on what happens downstream, never on how plausible the
candidate looks.

## 4. The kernel gate: the proof checker as a sound oracle

Every candidate passes through a small, trusted proof checker (a kernel,
in the interactive-theorem-prover sense — see the trusted-kernel
architecture used by systems such as Lean, Coq, or a bounded model
checker like Kani for the properties it decides). The kernel is the one
component in the system permitted to be a black box to everything else,
*because* it is small enough and old enough in its design lineage to be
trusted directly, rather than through another layer of checking.

**Assume:** a candidate in the checker's input syntax, addressed to a
specific target statement.
**Guarantee:** a binary, machine-readable verdict — accepted or rejected —
plus, on acceptance, a certificate the kernel itself can re-verify (a
re-runnable proof object, not a log line saying "passed").

This is a genuine oracle in the technical sense: nothing downstream needs
to re-derive what the kernel decided, only re-run its check if it wants
independent confirmation. That is the entire value of a small trusted
kernel — and also its entire limit, which is the subject of the next
section.

A proof kernel and a bounded model checker are not interchangeable
oracles, and their receipts must not be treated the same way. A proof
kernel's acceptance yields a re-checkable proof object: an artifact that
anyone can re-run against the same statement and definitions to get the
same verdict, independent of the tool that produced it. A bounded model
checker's acceptance yields a verdict that is valid only relative to the
recorded harness, the bound on the state space explored, the
environment assumptions encoded in the harness, and the checker's own
version — change any of those and the verdict no longer applies. Its
receipt must record all four explicitly, and must not claim to carry a
re-runnable proof object; presenting a bounded-model-checker verdict as
if it had kernel-grade portability is exactly the kind of unlabeled
category collapse this architecture exists to prevent.

## 5. Why the kernel is not enough: the semantic audit layer

A proof checker answers exactly one question: *does this proof term
establish this formal statement, given these definitions?* It answers
nothing about whether that formal statement is the theorem anyone wanted,
or whether it says anything at all.

Two well-known failure modes make this concrete, and both are visible
without any private example — they show up constantly in ordinary formal
verification work, including public tooling:

- **Vacuous acceptance.** A statement of the form "if P then Q" is proved
  the moment P is shown to be impossible — Q never has to hold. A checker
  correctly accepts such a proof, because it *is* a valid derivation. But
  a theorem whose precondition can never fire is worthless as a claim
  about the world, even though the kernel is green. Bounded model checkers
  have the same failure mode in a different guise: a harness whose
  preconditions are unsatisfiable will report "no counterexample found"
  for the trivial reason that no input satisfies them, which is
  indistinguishable at the verdict level from genuine coverage unless the
  tool also reports whether any input was actually explored. This is
  precisely the gap that motivated exhaustive, vacuity-visible property
  reporting in real model checkers — see `docs/INTERFACES.md`.
- **Name/content mismatch.** A theorem named `sort_is_correct` might
  formally state only that the output has the same length as the input —
  true, kernel-checked, and a wildly overclaiming name. Nothing in the
  kernel's verdict says anything about the *name*, the surrounding prose,
  or the changelog entry that will describe the result to a human reader.
  The kernel checks the object; humans read the label.

A semantic audit layer exists specifically to catch what the kernel
structurally cannot see: does the formal statement correspond to its
stated intent, and is the proof non-vacuous (the precondition is
satisfiable, the interesting case is actually exercised)? This layer does
not re-derive the kernel's verdict — that would be redundant with a
trusted kernel — it checks a different, non-formal property: correspondence
between statement and claim.

**Assume:** a kernel-accepted candidate plus its target's provenance
record.
**Guarantee:** a structured audit verdict — pass, or a specific,
machine-readable failure reason (vacuous precondition, name/content
mismatch, scope narrower than claimed, etc.) — never a free-text opinion.
A target that fails audit returns to the queue; it is *not* silently
dropped, and it is not treated as proved.

The kernel is necessary and sound; it is not sufficient. The audit layer
is where the system's honesty about its own claims actually lives.

## 6. The ratchet: the proven set never silently shrinks

Once a target is kernel-checked and audit-passed, it is accepted into the
proven set. The proven set is monotone by construction: a result, once
accepted, can only leave the set through an explicit, logged removal
event (a discovered unsoundness in a dependency, a definition change that
invalidates the statement) — never through a silent re-run that happens
to fail this time and gets treated as "the old result must have been
wrong, moving on."

Concretely, this means every accepted result is re-checked on every change
to anything it depends on (a shared definition, a library the kernel
trusts, the kernel version itself), and a re-check failure is a loud
event — it blocks further progress on anything downstream of that result
until resolved — rather than a quiet queue-state change. This is the same
discipline as a regression-gated build: the corpus is a ratchet, not a
snapshot, and the ratchet's whole value is that "currently proven" always
means what it says.

**Assume:** a change to any shared dependency.
**Guarantee:** every affected accepted result is re-verified, and any
newly-failing result becomes a blocking, logged event before anything
else proceeds.

## 7. Receipts: every interface is a contract

Nothing above works without one closing discipline: **every verification
run — kernel or audit — emits a structured, machine-readable result
artifact**, never a log message meant for a human to interpret. A receipt
records at minimum: which target, which candidate, which checker version,
what verdict, and (on acceptance) a re-verifiable certificate.

This is the same idea generalized across the whole pipeline: the queue
transitions in §2 are driven by receipts, not assertions; the audit
verdicts in §5 are receipts with structured failure codes, not prose;
the ratchet in §6 is only trustworthy because every re-check produces a
new receipt rather than reusing an old, possibly stale one.

Put together, the architecture's actual claim to rigor is not "there is a
proof checker somewhere in the loop." Plenty of unsound pipelines have
one. The claim is narrower and stronger: **every boundary between
components is a typed contract with a structured verdict on both
sides** — but the two verdict kinds are not the same thing. The kernel's
verdict in §4 is machine-*checkable*: an independent party can re-run it
against the recorded proof object and get the same answer, without
trusting the party that produced it. The audit verdict in §5 is
machine-*readable* — structured, typed, parseable — but it is a judgment
about correspondence between a statement and its stated intent, not a
fact with an independent re-derivation procedure; re-running the audit
can produce a different judgment without either run being "wrong" in the
kernel's sense. The architecture treats the two accordingly: kernel
verdicts gate the ratchet in §6 directly, audit verdicts route a target
back to the queue on failure rather than being re-run for a tie-break.
No component ever has to trust another component's *prose* about what it
did, but not every non-prose verdict carries the same kind of guarantee.
`docs/INTERFACES.md` develops the same doctrine for what a verification
tool owes its callers, using the public SARIF result format as its
worked example.

## A reference implementation

The sections above are a pattern, not pseudocode. A runnable,
dependency-free reference implementation of that pattern lives in
`reference/`: the versioned receipt and audit schemas (§7, and the five
properties of `docs/INTERFACES.md`), the closed-state work queue whose
state is folded from an append-only evidence log rather than asserted
(§2), a pluggable kernel gate that treats a checker's exit status as the
only verdict (§4), the two structural audit checks for vacuity and
name/content correspondence (§5), and the monotone ratchet with an
explicit, logged removal path (§6). It is deliberately a skeleton — the
prover of §3 is an injected command, and the audit checks are honestly
labelled heuristics, not sound procedures — so that the *interfaces*, not
any one component, are what the code makes concrete. A worked example
drives one genuine and one vacuously-true theorem through the whole
pipeline and shows the kernel accepting both while the audit layer
rejects the vacuous one.
