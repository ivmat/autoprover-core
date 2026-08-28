# Provenance of the control-receipt machinery

Two pieces of this repository are less obvious than the rest, and a
reader is entitled to ask where they came from:

- the **control block** on receipt schema 2.0.0 (`control`: `ablation` /
  `mutation` / `planted-twin`, carrying a declared expectation and a
  separately-recorded observation), together with `claim_grade` on a
  target's provenance and the `check_controls` audit check that reads
  them (`reference/autoprover_ref/audit.py`, `receipts.py`);
- the **unexercised-hypothesis check** (`check_unexercised_hypothesis`,
  fed by `model_checker.hypothesis_coverage`).

Neither is novel, and neither is derived from anything unpublished. This
note records the derivation so that claim can be checked rather than
taken on trust. It is kept as its own document rather than folded into
`EXTENDING.md` because `EXTENDING.md` tells a contributor how to add a
module — a different job from citing where a design came from, and one
that would be diluted by mixing the two.

## 1. Unexercised preconditions, and probes that are not contracts

Both ideas arrived as **review feedback received in public**, on a public
pull request, from a maintainer of a public verification project.

> Felipe R. Monteiro (`feliperodri`), review of pull request #618 on
> `model-checking/verify-rust-std`, 2026-08-16 —
> <https://github.com/model-checking/verify-rust-std/pull/618#pullrequestreview-4947435599>

Two points from that review are the direct ancestors of the code here.

**The unexercised precondition.** The review observes that a contract's
precondition can be doc-faithful and the proof still be "near-vacuous
with respect to that precondition", because the harness only ever
supplies inputs that satisfy it — the guard is never put to work, and
dropping it entirely leaves the verification passing. That is exactly the
finding `check_unexercised_hypothesis` reports: an obligation whose
precondition *no* explored state violated. It is the mirror image of the
older vacuity check (which asks whether a precondition can fire at all),
and the two are kept as distinct findings for the reason
`reference/README.md` gives — collapsing them would flatten two different
facts into one ambiguous verdict.

**Probe versus contract.** The same review repeatedly separates a
*bounded probe* — a check hard-coded to a fixture's types or sizes, valid
as evidence about that fixture — from *the contract*, the general
statement a caller may rely on, and asks that anything of the first kind
be labelled as such rather than counted as the second. `claim_grade`
(`probe` / `contract`) is that distinction made machine-readable, and
`check_controls` is what stops the stronger label from being free: a
claim presented as contract-grade has to carry evidence that its oracle
can fail.

That review was addressed to work of ours, in public, on a public
tracker; nothing about it is confidential, and this note cites it in the
form anyone can read it.

## 2. Controls: why "predicted red, observed red"

The discipline `check_controls` enforces — that a claim is not
contract-grade until some run has been observed to *fail* by design — is
the standard argument of mutation testing, and predates this repository
by decades.

> R. A. DeMillo, R. J. Lipton, F. G. Sayward, "Hints on Test Data
> Selection: Help for the Practicing Programmer", *IEEE Computer*
> 11(4):34–41, 1978.

The mutation-testing argument is that a test suite's value is measured by
what it *rejects*: deliberately perturb the artifact, and a suite that
still passes has been shown not to be watching. `control.kind ==
"mutation"` with `expectation: "red"` and `observed: "red"` is that
experiment recorded as a receipt — a mutant was introduced, the check was
predicted to fail, and it did. The prediction and the measurement are
separate fields on purpose: a control that records only its own outcome
cannot distinguish a check that failed as designed from one that failed.

Two design choices follow from the literature rather than from taste, and
are argued in `check_controls`' docstring:

- the *revert* leg of a mutation experiment (predict green, observe
  green) demonstrates only that the experiment was reversible. It does
  not show anyone watching the oracle fail, so it does not satisfy a
  requirement whose entire content is that somebody did.
- an **ablation** — removing a precondition and seeing what breaks —
  attests that the precondition is load-bearing. That is adjacent to, but
  not the same as, falsifiability of the claim's oracle, so ablations are
  recorded and reported but do not by themselves qualify.

## 3. Vacuity detection

The older vacuity check, and the framing of "passes for the trivial
reason" as a first-class verification finding rather than a nuisance, is
standard model-checking practice:

> I. Beer, S. Ben-David, C. Eisner, Y. Rodeh, "Efficient Detection of
> Vacuity in ACTL Formulas", *CAV 1997*, LNCS 1254.

> O. Kupferman, M. Y. Vardi, "Vacuity detection in temporal model
> checking", *STTT* 4(2):224–233, 2003.

The `held` / `vacuous` / `not-exercised` / `failed` split that
`receipt.schema.json` makes first-class is this literature's distinction
carried into the receipt format: a property that passed and a property
that passed because nothing tested it are different results, and a format
that cannot tell them apart loses the difference at exactly the moment it
matters.

## 4. What is deliberately not here

The machinery above is the *interface*: a place to record a control, a
grade on a claim, and a check that refuses the stronger grade without
evidence. The harder question — how to choose which mutants are worth
planting, and how much a set of controls should raise confidence in a
claim — is a judgment problem this repository does not solve and does not
pretend to. `LIMITATIONS.md` §7 states the same boundary for the audit
layer as a whole: these are honestly-labelled heuristics with an evidence
discipline around them, not a sound decision procedure.
