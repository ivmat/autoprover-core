# ADR-005: An acceptance manifest is a generated projection of the receipt store — never a hand-written artifact

**Status:** Accepted

## Context

`docs/ARCHITECTURE.md` §7 states the receipt discipline: every
verification run — kernel or audit — emits a structured, machine-readable
result artifact, one per run, scoped to one target and one candidate.
That is deliberately a low-level, per-run granularity: a `claim_id`
joins the receipts behind one claim (`docs/GLOSSARY.md`'s `claim_id`
entry — "one claim ... is typically discharged by many receipts ...
`claim_id` is what joins them"), but reading receipts alone does not
tell a reader whether a target is *currently* accepted — that also
depends on the audit verdict over those receipts and the target's
current standing in the ratchet (`docs/ARCHITECTURE.md` §6).

That granularity is the wrong shape for a different, adjacent question:
"what does this project claim overall, and on what basis, in one place a
reader does not have to reconstruct by walking every receipt." Answering
that well needs its own document shape — one row per claim, a closed
vocabulary for how strong the evidence behind it is, and a place to
record what would have to be true for the claim to be believed. That is
a different layer than a receipt, not a bigger receipt, and general
enough that it should not be reinvented per project.
[acceptance-format](https://github.com/ivmat/acceptance-format) is such
a format: a project-agnostic, plain-text specification for exactly this
one-row-per-claim, certificate-of-record layer, with structured claim
fields of its own — claim-level `grade` and `bounds`, a `self_verify`
table with its `positive_control` — distinct from this repository's
receipt and audit vocabulary.

## Decision

If this repository's receipts are ever projected into an acceptance
manifest, that manifest is generated — mechanically, by a tool that
reads the receipt store — never hand-authored. Not every field in a
manifest row is receipt-derived: a claim's text, its clause/item
identity, and its declared `self_verify` commands are inputs someone
states, not facts a receipt contains, and an honestly unweighted claim
may carry no receipt at all. What the receipt store must be the sole
source of is a row's *evidentiary* content: every evidentiary assertion
a row makes has to trace back, via `claim_id`, to one or more receipts
already on disk, and it may never read as stronger evidence than the
kernel or audit verdict those receipts actually record. A person
editing a manifest row's evidentiary content directly, without a
receipt behind the edit, is exactly the failure mode receipts exist to
prevent one layer down (`docs/ARCHITECTURE.md` §7): a claim that looks
identical to an evidenced one but is not.

This mirrors the discipline this repository already applies to itself
in [ADR-004](ADR-004-abstain-vs-fail.md) and
[ADR-002](ADR-002-receipt-schema-versioning.md): structure, not prose,
is what a caller is allowed to rely on for an evidentiary claim. For
this repository, a hand-written manifest's evidentiary content would be
prose wearing a table's shape — the public format itself permits
hand-authored manifests; the generated-only rule for evidentiary
content is this repository's own discipline, not one the format
imposes. A generated manifest inherits whatever distinctions the
receipts already draw — including the one `docs/ARCHITECTURE.md` §4
insists on keeping separate: a kernel receipt's re-runnable certificate
and a bounded model checker's harness-relative verdict must not
collapse into one undifferentiated "accepted" row at the manifest layer
either, for the same reason they must not collapse at the receipt
layer.

## Consequences

A manifest's evidentiary content, built this way, must be deterministic
for a fixed receipt snapshot, a fixed set of declared inputs, and a
fixed generator version — regenerating it must not silently produce a
different evidentiary claim (modulo timestamps). That is analogous *in
purpose*, not identical in mechanism, to what [ADR-002](ADR-002-receipt-schema-versioning.md)
already refuses at the receipt layer — reinterpreting an artifact
silently under a different schema — not a rule ADR-002 itself states
about manifests. Whoever wires a generator for this repository inherits
[ADR-001](ADR-001-kernel-gate-not-prover.md)'s boundary as well: a
generator may use only kernel receipts and audit verdicts as evidence —
raw prover output can never raise a row's evidentiary strength.

This repository contains neither such a generator nor a generated
acceptance manifest.
