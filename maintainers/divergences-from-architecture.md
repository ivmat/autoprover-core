# Maintainer note: where the code diverges from ARCHITECTURE.md's prose

This is maintainer working material: a record of the specific places
`reference/`'s code makes a choice that `docs/ARCHITECTURE.md`'s prose
leaves open, plus the gaps between the two that have since been closed.
Moved here from `reference/README.md` (with sentence-level
Simple-Technical-English edits; content unchanged).

---

## Divergences from a literal reading of ARCHITECTURE.md

`docs/ARCHITECTURE.md` is prose; this package is code, and in two places
the code makes a choice the prose leaves open. Both are recorded here
rather than smoothed over, because the difference is the kind of thing a
reader reconciling the two documents will otherwise trip on:

1. **The `kernel-checked → audited → accepted | audit-rejected` hop.**
   ARCHITECTURE.md §2's diagram draws one arrow chain through an
   `audited` intermediate state. `queue.TargetQueue.record_audit`
   realizes this as **two** evidence-consuming log events recorded from
   the same audit verdict artifact (`kernel-checked → audited`, then
   `audited → accepted|audit-rejected`), both appended within one call.
   This is a fidelity choice. An evidence-per-transition discipline,
   applied literally to a diagram with a named intermediate state, has
   to pass through that state explicitly. The reference implementation
   errs on the side of that literalism, rather than collapsing the two
   hops into one transition function. Either reading is defensible; the
   diagram doesn't say which.
2. **"Kernel gate" is not exclusively about proof kernels.** §4 treats a
   proof kernel and a bounded model checker as two *kinds* of sound
   oracle occupying the same slot in the pipeline, but the §2 diagram
   names the queue state `kernel-checked` regardless of which kind
   produced the accepting receipt. `queue.record_kernel_receipt` follows
   the diagram's literal state name and accepts a receipt from either
   `checker.kind`. A reader taking the state name at face value might
   expect it to reject a model-checker receipt; a doc note saying "this
   state's name is a holdover from the diagram, not a restriction" would
   close that gap.

Five further gaps between the prose and this package have since been
closed. They are kept in this section, as implemented features rather
than as gaps, so the history of the interface stays legible:

- **Provenance, a reachable `error` verdict, coverage on the receipt, and
  control receipts** were all absent from receipt schema 1.0.0, and each
  absence had a consequence. A verdict recorded only `checker.version`,
  which cannot distinguish two builds of one release and cannot record
  which semantics flags were in force, so a verdict could not be
  attributed to a build and therefore could not be reproduced. There was
  no `claim_id`, so per-harness receipts could not be aggregated under
  one claim. `verdict: "error"` was in the enum but unreachable in code:
  a checker that timed out or met a construct it could not model was
  reported as `rejected`, i.e. as if the candidate had been refuted.
  `CheckerResult` could not carry hypothesis coverage, so the
  unexercised-hypothesis audit check abstained on everything driven
  through `Pipeline` — the numbers the model checker had just computed
  were dropped between the checker and the audit. And an ablation or
  mutation run — the evidence that an oracle or a precondition is
  load-bearing at all — had no representation. Receipt schema **2.0.0**
  closes all five: `toolchain` (tool build identity, dependency
  versions, flags, features) and `subject` (repo, commit, unit),
  `claim_id`, `failure_kind` (`timeout` / `oom` /
  `unsupported-construct` / `tool-error`, non-null exactly when the
  verdict is `error`), a per-obligation `coverage` block, and an
  optional `control` block (`ablation` / `mutation` / `planted-twin`
  with a declared expectation and a measured observation). The checker
  seam gained a timeout to match, and `KernelGate` maps any reported
  `failure_kind` to `error` with the kind recorded rather than to
  `rejected`.

- **Obligation-level vacuity/not-exercised detection** has no home in the
  kernel gate alone:
  `kernel_gate.KernelGate.check`'s default path only produces
  `held`/`failed` per obligation, because a plain accept/reject checker
  invocation (e.g. a whole-file `lean` run) has no way to know on its own
  whether an obligation was vacuous or unexercised. The gate exposes a
  per-obligation `obligation_statuses` seam (see
  `kernel_gate.CheckerResult.obligation_statuses`) for a checker that can
  say more, but a bare kernel invocation cannot fill it.
  `autoprover_ref/model_checker.py` now closes that gap: its bounded
  breadth-first exploration derives `vacuous` (precondition unsatisfiable
  in an exhaustively-explored state space) vs. `not-exercised`
  (precondition unsatisfiable in a bound-truncated one) directly from
  whether the exploration reached a fixed point, and reports both through
  exactly that `obligation_statuses` seam via
  `model_checker.model_checker_command`. See
  [`reference/README.md`](../reference/README.md)'s "The model checker"
  section.
- **`unexercised-hypothesis`**, the mirror image of the vacuity check,
  was not implemented in any version of this package before the audit
  schema's 1.1.0 revision: the model checker could already tell a caller
  that an obligation's precondition never *fired* (`vacuous` /
  `not-exercised`), but nothing reported the opposite finding — a
  precondition that every enumerated state satisfies, so the implication
  was never exercised and the guard did no work.
  `model_checker.hypothesis_coverage` now reports the satisfying/violating
  split per obligation and `audit.check_unexercised_hypothesis` judges it,
  producing the new `unexercised-hypothesis` failure reason. That reason
  is a new value in a closed enum, which a consumer must be able to
  notice, so it travels with an audit-schema version bump (1.0.0 →
  1.1.0, INTERFACES.md property 5); 1.0.0 documents still validate and
  are forbidden by the schema from carrying the 1.1.0-only code. The
  receipt schema is versioned separately.
- **`missing-control`** (audit schema 1.2.0) closes the loop the previous
  four checks leave open. Every one of them judges what a target SAYS —
  whether its hypothesis can fire, whether it ever failed to, whether its
  name is reflected in its statement, whether its scope is as broad as
  claimed. None of them can tell a real proof from one whose oracle is
  too weak to fail. A postcondition that excludes nothing passes every
  ordinary run indistinguishably from one that excludes the right things.
  The only artifact that separates them is a run in which the check DID
  fire. `audit.check_controls` requires a claim presented as
  contract-grade (`TargetProvenance.claim_grade == "contract"`) to carry
  a control receipt in the evidence set gathered under its `claim_id`.
  That receipt must be of kind `mutation`, predicted `red`, and observed
  `red` — a check somebody watched fail. It abstains for probe-grade or
  ungraded claims, and when no evidence set is supplied at all. It runs
  LAST, because a question about the evidence set is worth asking only
  once every question about the statement itself has been answered.
- **`scope-narrower-than-claimed`** was schema-defined but not
  implemented — this reference package originally shipped only two audit
  checks (vacuity, name/content) and left this one as a documented gap
  rather than a stub that would always vacuously
  pass. `audit.check_scope` now implements it as a third structural
  heuristic: given a target's declared `claimed_scope` and its statement
  text, it flags a statement that shows structural evidence of being
  restricted to a fixed instance (a would-be-universal variable pinned to
  one numeral, a named single-instance carrier, or no quantified-variable
  binder at all) when the claim asserts generality. Like the other two
  checks, it is honestly a heuristic over text/metadata, not a semantic
  generality prover, and it abstains (passes) rather than guesses when
  `claimed_scope` is absent or doesn't itself assert generality — see
  [`reference/README.md`](../reference/README.md)'s "Honesty notes"
  section and `audit.py`'s module docstring.
