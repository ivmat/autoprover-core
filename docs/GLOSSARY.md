# Glossary

One or two plain sentences per term, alphabetical. Each entry links the
document or schema field where the term is defined normatively; read
that source for the exact rule, not this page.

---

## audit verdict

A structured, machine-readable result from the semantic audit layer:
`pass`, or a specific, machine-readable failure reason — never a
free-text opinion. See [`docs/ARCHITECTURE.md`](ARCHITECTURE.md) §5 and
[`reference/schema/audit.schema.json`](../reference/schema/audit.schema.json).

## candidate

A prover's attempted output for a target: either a candidate proof term
or script in the target logic's exact checker-input syntax, tagged with
the target it claims to address, or an explicit "no candidate" result.
A candidate is never treated as a verdict. See
[`docs/ARCHITECTURE.md`](ARCHITECTURE.md) §3.

## certificate

On a proof kernel's acceptance, a re-runnable reference (the checked
file plus the toolchain identifier) that anyone can re-run against the
same statement and definitions to get the same verdict — never a log
line saying "passed." Present only when `checker.kind == "kernel"` and
`verdict == "accepted"`. See [`docs/ARCHITECTURE.md`](ARCHITECTURE.md)
§4 and
[`reference/schema/receipt.schema.json`](../reference/schema/receipt.schema.json)'s
`certificate` field.

## claim_grade (probe / contract)

A declared distinction between a **probe** — a check hard-coded to a
fixture's types or sizes, valid as evidence about that fixture — and a
**contract** — the general statement a caller may rely on. A claim
presented as contract-grade has to carry evidence: a `control` of kind
`mutation`, predicted `red` and observed `red` — a check that was
watched to fail. An `ablation` control is adjacent (it shows a
precondition is load-bearing) but does not by itself qualify. See
[`docs/PROVENANCE.md`](PROVENANCE.md) §1 and
[`reference/autoprover_ref/audit.py`](../reference/autoprover_ref/audit.py).

## claim_id

The aggregation key under which a receipt is evidence. One claim (a
manifest clause, say) is typically discharged by many receipts — one
per harness, per unit, per checker family — and `claim_id` is what
joins them; it is not the target id. See
[`reference/schema/receipt.schema-2.0.0.json`](../reference/schema/receipt.schema-2.0.0.json)'s
`claim_id` field.

## control block (ablation / mutation / planted-twin)

An optional part of a receipt schema 2.0.0 document that attests some
other claim's oracle or precondition is load-bearing, rather than
establishing the claim itself: **ablation** removes a
precondition/hypothesis and expects the property to break; **mutation**
perturbs the implementation and expects the oracle to catch it;
**planted-twin** checks a deliberately-wrong sibling artifact and
expects it to be rejected. See
[`reference/schema/receipt.schema-2.0.0.json`](../reference/schema/receipt.schema-2.0.0.json)'s
`control` field and [`docs/PROVENANCE.md`](PROVENANCE.md) §2.

## coverage

What an enumerating checker measured about one obligation's
precondition: how many explored states satisfied it, how many violated
it, and whether the exploration was exhaustive. Carried on the receipt
so the semantic audit layer can judge hypothesis coverage on receipt
evidence instead of abstaining for want of it. See
[`reference/schema/receipt.schema-2.0.0.json`](../reference/schema/receipt.schema-2.0.0.json)'s
per-obligation `coverage` field.

## design validation vs. substantive verification vs. checker correspondence

Three kinds of machine-checked result that should not be summed into one
"N theorems proved" count: **design validation** is true largely by
construction of the model (the value is in pinning a definition down
precisely); **substantive verification** is a genuine theorem whose
proof needed a non-trivial argument that could have failed; **checker
correspondence** is a proof that a *model of a checker* is sound, not a
verification of the checker's actual implementation. See
[`docs/LIMITATIONS.md`](LIMITATIONS.md) §4.

## held / vacuous / not-exercised / failed

The closed, four-value status an obligation is reduced to. `held` means
the precondition was exercised — it fired in at least one explored
state — and the property held on every state where it fired;
`vacuous` means the precondition never fired, and exploration was
exhaustive; `not-exercised` means the precondition never fired, but
exploration was bound-truncated so that outcome can't be attributed to
the system's semantics; `failed` means the property failed on at least
one explored state where the precondition fired (a violating exercised
state was found). `vacuous` and `not-exercised` are first-class and
distinct from `held`, so an obligation that was never really tested can
never look identical to one that was. See
[`reference/schema/receipt.schema.json`](../reference/schema/receipt.schema.json)'s
`obligations[].status` field and
[`reference/README.md`](../reference/README.md)'s "The model checker"
section.

## kernel gate

The wrapper around a sound checker (a proof kernel or a bounded model
checker) that treats the checker's exit status as the only verdict.
"The kernel is the one component in the system permitted to be a black
box to everything else, *because* it is small enough and old enough in
its design lineage to be trusted directly." See
[`docs/ARCHITECTURE.md`](ARCHITECTURE.md) §4 and
[`reference/autoprover_ref/kernel_gate.py`](../reference/autoprover_ref/kernel_gate.py).

## monotone accepted set — see **ratchet**

## name/content mismatch

An audit failure reason: a theorem's name overclaims relative to what
its formal statement actually says — "a theorem named `sort_is_correct`
might formally state only that the output has the same length as the
input." The kernel checks the object; it has no opinion about the
label. See [`docs/ARCHITECTURE.md`](ARCHITECTURE.md) §5 and
[`docs/LIMITATIONS.md`](LIMITATIONS.md) §1.

## obligation

One property or condition a checker was asked to check about a
candidate. A receipt's `obligations` array is an exhaustive account of
every obligation the checker was asked about, including the ones never
meaningfully exercised — never just the list of what passed. See
[`reference/schema/receipt.schema.json`](../reference/schema/receipt.schema.json)'s
`obligations` field and [`docs/INTERFACES.md`](INTERFACES.md)
property 2.

## provenance record

The part of a target that records where its statement came from (a
textbook, a paper, a spec) and, once proved, what it is allowed to
claim. This is what closes the "the kernel proved *something*, but does
it match what we said it proved" gap. See
[`docs/ARCHITECTURE.md`](ARCHITECTURE.md) §1.

## ratchet

The rule that the proven set only grows by construction: a result, once
accepted, can only leave the set through an explicit, logged removal
event — never through a silent re-run that happens to fail and gets
treated as "the old result must have been wrong." See
[`docs/ARCHITECTURE.md`](ARCHITECTURE.md) §6 and
[ADR-003](decisions/ADR-003-monotone-ratchet.md).

## receipt

A structured, machine-readable result artifact that every verification
run — kernel or audit — emits, recording at minimum which target, which
candidate, which checker version, and what verdict. A kernel-checker
receipt additionally carries, on acceptance, a re-verifiable
**certificate** (present only when `checker.kind == "kernel"` and
`verdict == "accepted"` — see the **certificate** entry above); an
audit verdict is a separate contract, with no independent re-derivation
procedure of its own. Never a log message meant for a human to
interpret. See [`docs/ARCHITECTURE.md`](ARCHITECTURE.md) §7.

## scoped vs. full

The honesty flag [`corpus/CATALOG.md`](../corpus/CATALOG.md) attaches
to every module. `full` means the module proves the general result its
name suggests. `scoped` means the module is deliberately restricted — a
fixed finite instance, one direction of a biconditional, a safety-only
property with no liveness claim, an assumed rather than proved
hypothesis — with a few words on what is restricted, taken from the
module's own header. See
[`corpus/CATALOG.md`](../corpus/CATALOG.md)'s introduction.

## subject / toolchain

`subject` is what a receipt's verdict is ABOUT, at commit granularity
(repo, commit, and an optional sub-unit — module, crate, package, or
file). `toolchain` is the build identity the verdict is relative to
(the exact tool build, its dependencies, and the flags/features in
force) — a version string alone cannot distinguish two builds of one
release, and a flag that changes semantics changes what the verdict
means. Both are receipt schema 2.0.0 additions over 1.0.0. See
[`reference/schema/receipt.schema-2.0.0.json`](../reference/schema/receipt.schema-2.0.0.json)'s
`subject` and `toolchain` fields.

## target

A candidate theorem statement: something with a precise, checkable
meaning in the target logic, plus enough context (definitions, prior
lemmas, the source it's drawn from) for a prover to attempt it. A target
entering the queue guarantees a well-formed statement and a provenance
record — never that the statement is true. See
[`docs/ARCHITECTURE.md`](ARCHITECTURE.md) §1.

## trusted computing base

What every proof here ultimately rests on beneath its named hypotheses:
the Lean kernel and the pinned toolchain version. "Kernel-checked" means
"checked by *that* kernel"; a bug in the kernel or a toolchain-version
mismatch is outside what any proof here can attest to. See
[`docs/LIMITATIONS.md`](LIMITATIONS.md) §5.

## unexercised hypothesis

The mirror image of vacuous acceptance: a precondition that *every*
enumerated state satisfies has pruned nothing, so the implication was
never exercised as an implication. Vacuity asks whether the hypothesis
can ever fire; this asks whether it ever failed to. See
[`docs/ARCHITECTURE.md`](ARCHITECTURE.md) §5.

## vacuous acceptance

A statement of the form "if P then Q" that is proved the moment P is
shown impossible — Q never has to hold. The checker correctly accepts
such a proof, because it *is* a valid derivation, but a theorem whose
precondition can never fire is worthless as a claim about the world even
though the kernel is green. See
[`docs/ARCHITECTURE.md`](ARCHITECTURE.md) §5.

## watched fail

**Informal phrase, not a schema status.** Shorthand used in prose (the
honesty notes, `docs/PROVENANCE.md`) for a control receipt of kind
`mutation` whose prediction was `red` and whose observation was also
`red` — a check that somebody actually watched fail, as opposed to one
that has only ever been observed passing. An `ablation` control is
adjacent — it shows a precondition is load-bearing — but does not
qualify: it does not by itself demonstrate the oracle can fail. It does
not appear as an enum value anywhere in the schemas; the
machine-readable form of the same idea is the `control` block's
`kind`/`expectation`/`observed` fields. See
[`docs/PROVENANCE.md`](PROVENANCE.md) §2 and
[ADR-004](decisions/ADR-004-abstain-vs-fail.md).
