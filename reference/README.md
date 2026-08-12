# `reference/` — a reference implementation of the pipeline

This directory turns `docs/ARCHITECTURE.md` and `docs/INTERFACES.md`
from an essay into runnable code: a small, standard-library-only Python
package that realizes the seven-section pipeline pattern and the
five-property result-as-API doctrine those documents describe.

**Scope note: this is a reference implementation, not a product.** It
exists to make the architecture concrete and testable, and to give
anyone building on top of the pattern a working starting point with the
right invariants already enforced in code (not just in prose). It is
not tuned for performance, does not include an LLM prover (see
`autoprover_ref/pipeline.py`'s module docstring for why), and its audit
heuristics and its bounded model checker are intentionally small (see
`autoprover_ref/audit.py`, `autoprover_ref/model_checker.py`) —
extending any of these is ordinary, contributable engineering, not a
redesign.

## Requirements

Python 3.11+, standard library only. No `pip install` needed anywhere in
this directory — that includes JSON Schema validation, which is
hand-rolled in `autoprover_ref/jsonschema_min.py` rather than depending
on the third-party `jsonschema` package, matching the zero-dependency
ethos of `corpus/`.

The one place this directory touches an external tool at all is
`reference/examples/`, which can optionally invoke a real `lean`
executable — see below.

## Layout and the ARCHITECTURE.md mapping

| path | ARCHITECTURE.md section | what it is |
|---|---|---|
| `schema/receipt.schema.json` | §4, §7 | The versioned contract for a verification receipt. |
| `schema/audit.schema.json` | §5, §7 | The versioned contract for a semantic audit verdict. |
| `autoprover_ref/receipts.py` | §7 | Receipt/audit-verdict dataclasses, schema validation, atomic writes. |
| `autoprover_ref/queue.py` | §2 | The evidence-driven target queue state machine. |
| `autoprover_ref/kernel_gate.py` | §4 | The checker-as-sound-oracle wrapper (pluggable checker command). |
| `autoprover_ref/audit.py` | §5 | The semantic audit layer: vacuity, name/content, and scope heuristics. |
| `autoprover_ref/model_checker.py` | §4, §5 | A bounded model checker realizing the exhaustive obligation-level `held`/`vacuous`/`not-exercised`/`failed` bucket, wired in as a `kernel_gate.CheckerCommand`. |
| `autoprover_ref/ratchet.py` | §6 | The monotone accepted set, explicit removal, dependency recheck. |
| `autoprover_ref/pipeline.py` | §§2–7 | Glue: drives one target through all of the above. |
| `autoprover_ref/jsonschema_min.py` | — | The hand-rolled JSON Schema validator subset the two schemas use. |

§1 (target selection and decomposition) and §3 (LLM provers) are
represented as *contracts* rather than components: `queue.TargetEntry`
encodes §1's "well-formed statement + provenance" guarantee, and
`queue.CandidateArtifact` / `queue.NoCandidateProduced` encode §3's "a
candidate, or an explicit no-candidate result, never a verdict"
guarantee. Neither section names an algorithm this reference package
should implement — decomposing a target into a dependency graph and
generating candidate proofs are both open-ended, model/domain-specific
concerns outside a stdlib reference package's scope.

## The five INTERFACES.md properties, concretely

1. **Structured, not narrative** — every receipt/audit verdict is a
   dataclass with a fixed shape, never a string a caller has to parse.
2. **Exhaustive, not partial** — `Receipt.obligations` always lists
   every requested obligation, with `held` / `vacuous` / `not-exercised`
   / `failed` as distinct values (`schema/receipt.schema.json`). A plain
   kernel accept/reject checker can only ever reduce every obligation to
   `held`/`failed`; `autoprover_ref/model_checker.py`'s bounded
   exploration is what actually realizes the other two values, deriving
   `vacuous` vs. `not-exercised` from whether its exploration was
   exhaustive or bound-truncated — see "The model checker" below.
3. **Null never means a guess** — `certificate`, `harness`, `bound`,
   `env_assumptions`, and `failure_reason` are explicit, schema-checked
   nullable fields; the schemas enforce exactly when each may/must be
   null (see the `allOf`/`if`/`then`/`else` blocks in both schema
   files).
4. **Atomic, exists-implies-complete writes** — `receipts.atomic_write_json`
   writes to a temp file in the target directory, `fsync`s, then
   `os.replace`s; a file that exists at the expected path is always the
   finished artifact.
5. **Explicit schema versioning** — both schemas carry `schema_version`
   as a required, validated field (`"1.0.0"` today); `receipts.py`
   validates it as part of every read.

## Running the tests

```sh
cd reference
python3 run_tests.py
```

(equivalently: `PYTHONPATH=. python3 -m unittest discover -s tests -p "test_*.py" -v`,
run from `reference/`). This is pure Python — **no Lean installation is
needed** for anything under `tests/`. See "Report" in the delivery notes
for the exact summary from the last run.

## Running the worked example

```sh
cd reference/examples
python3 run_example.py
```

See `examples/README.md` for the full walkthrough: two tiny,
self-contained Lean files (kept entirely inside `reference/examples/`,
never touching `corpus/`), driven through the whole pipeline, showing
the kernel accept both while the audit layer flags the vacuous one. If
`lean` isn't on `PATH`, the script says so and exits cleanly — the
kernel gate's checker command is fully pluggable
(`autoprover_ref.kernel_gate.KernelGate(checker_command=...)`), so
wiring in a different checker (or a mock, as `reference/tests/` does)
never requires touching `queue.py`, `audit.py`, `ratchet.py`, or
`pipeline.py`.

## The model checker

```sh
cd reference/examples
python3 model_check_example.py
```

This is pure Python and needs no external tool at all (unlike
`run_example.py` above, which needs `lean`). `autoprover_ref/model_checker.py`
is a small, self-contained bounded model checker: it takes a tiny finite
transition system (a set of initial states plus a successor function) and
a set of named obligations (a precondition predicate plus a property
predicate each), explores the bounded reachable state space breadth-first,
and reduces each obligation to exactly one of `held` / `vacuous` /
`not-exercised` / `failed` — never collapsing "never got a chance to check
this" into "checked and it passed".

The rule it uses: if bounded exploration reaches a fixed point (empties
its frontier) before hitting the bound, the explored set is the system's
*whole* reachable closure, and an obligation whose precondition never
fired anywhere in it is genuinely **vacuous**. If the bound is hit first,
the exploration is truncated — states beyond the bound were never
visited — and the same "precondition never fired" outcome is instead
**not-exercised**: the bound, not the system's semantics, is why nothing
was seen. This is the exact ambiguity ARCHITECTURE.md §5 and
`docs/INTERFACES.md` property 2 describe for real bounded model checkers
("no counterexample found" looks identical to genuine coverage unless the
tool also reports whether anything was actually explored), made
structurally visible instead of collapsed.

`model_checker.model_checker_command(system, obligations, bound)` builds a
`kernel_gate.CheckerCommand`, so a model-checker run flows through exactly
the same `KernelGate` → `Pipeline` → queue → ratchet wiring a Lean-backed
kernel run does (see `examples/model_check_example.py`, which drives one
scenario all the way through the ratchet and confirms the resulting
receipt never carries a certificate and always carries its
harness/bound/env_assumptions triple — the kernel-vs-model-checker
distinction from ARCHITECTURE.md §4, enforced in code by `kernel_gate.py`
and `receipts.Receipt.__post_init__`, not just documented here).
`model_check_example.py` runs three toy scenarios chosen specifically to
exhibit all four obligation statuses — a small closed traffic-light
system for `held` and `vacuous`, a long linear counter explored under a
small bound for `not-exercised`, and a buggy variant of the traffic light
for `failed` — and prints which statuses it observed.

## Honesty notes (heuristic vs. sound, by design)

- `kernel_gate.py` is the only sound component in this package: its
  verdict comes entirely from a checker process's exit status, never
  from the prover's own claim. This is enforced by *not giving
  `KernelGate.check` any other input to base a verdict on* — there is
  no code path that reads a "prover says this is correct" flag.
- `audit.py`'s three checks (vacuity, name/content, and — as of this
  version — scope) are explicitly documented, in the module docstring and
  in code comments, as structural heuristics operating on provenance
  text/metadata — never as sound verification. A target can pass all
  three checks and still be wrong in a way a human would catch
  immediately; that trade-off is the one ARCHITECTURE.md §7 draws
  between a kernel verdict (independently re-derivable) and an audit
  verdict (a judgment). The scope check (`audit.check_scope`) in
  particular only judges a target that supplies `TargetProvenance.
  claimed_scope` with a signal asserting generality ("for all", "any",
  "arbitrary", ...); it *abstains* (passes without judging) on any target
  that doesn't declare a claimed scope, or whose claimed scope doesn't
  itself assert generality — exactly the same abstain-rather-than-guess
  discipline `check_name_content` already uses for keywords outside its
  lexicon.
- `autoprover_ref/model_checker.py`'s bounded exploration is likewise
  honestly bounded, not sound in the way `kernel_gate.py` is: a `held`
  status means "true on every state this run actually explored", not
  "true for all reachable states of the real system" unless the
  exploration also came back `exhaustive` (see "The model checker"
  above and the module's docstring). `KernelGate`'s existing
  `kind="model-checker"` enforcement (no certificate, mandatory
  harness/bound/env_assumptions) is what keeps a model-checker receipt
  from ever being read as carrying kernel-grade portability.

## Divergences from a literal reading of ARCHITECTURE.md

These are worth flagging explicitly — they are exactly the kind of
finding that means a doc could be tightened, not bugs to silently paper
over:

1. **The `kernel-checked → audited → accepted | audit-rejected` hop.**
   ARCHITECTURE.md §2's diagram draws one arrow chain through an
   `audited` intermediate state. `queue.TargetQueue.record_audit`
   realizes this as **two** evidence-consuming log events recorded from
   the same audit verdict artifact (`kernel-checked → audited`, then
   `audited → accepted|audit-rejected`), both appended within one call.
   This is a fidelity choice: an evidence-per-transition discipline
   applied literally to a diagram with a named intermediate state has to
   pass through that state explicitly, and the reference implementation
   errs on the side of that literalism rather than collapsing the two
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

Two earlier divergences in this list have since been closed, and are
recorded here as implemented rather than as gaps:

- **Obligation-level vacuity/not-exercised detection**, at the time this
  note was first written, was not implemented anywhere in the pipeline:
  `kernel_gate.KernelGate.check`'s default path only produces
  `held`/`failed` per obligation, because a plain accept/reject checker
  invocation (e.g. a whole-file `lean` run) has no way to know on its own
  whether an obligation was vacuous or unexercised — the gate's
  per-obligation `obligation_statuses` seam existed (see
  `kernel_gate.CheckerResult.obligation_statuses`), but nothing shipped
  in this package used it to produce `vacuous`/`not-exercised`.
  `autoprover_ref/model_checker.py` now closes that gap: its bounded
  breadth-first exploration derives `vacuous` (precondition unsatisfiable
  in an exhaustively-explored state space) vs. `not-exercised`
  (precondition unsatisfiable in a bound-truncated one) directly from
  whether the exploration reached a fixed point, and reports both through
  exactly that `obligation_statuses` seam via
  `model_checker.model_checker_command`. See "The model checker" above.
- **`scope-narrower-than-claimed`** was schema-defined but not
  implemented — this reference package originally shipped only the two
  checks the initial task specified (vacuity, name/content) and left this
  one as a documented gap rather than a stub that would always vacuously
  pass. `audit.check_scope` now implements it as a third structural
  heuristic: given a target's declared `claimed_scope` and its statement
  text, it flags a statement that shows structural evidence of being
  restricted to a fixed instance (a would-be-universal variable pinned to
  one numeral, a named single-instance carrier, or no quantified-variable
  binder at all) when the claim asserts generality. Like the other two
  checks, it is honestly a heuristic over text/metadata, not a semantic
  generality prover, and it abstains (passes) rather than guesses when
  `claimed_scope` is absent or doesn't itself assert generality — see the
  honesty note above and `audit.py`'s module docstring.
