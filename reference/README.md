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
| `schema/receipt.schema.json` | §4, §7 | The verification-receipt contract, version 1.0.0 (kept at its published path; still valid for documents that declare it). |
| `schema/receipt.schema-2.0.0.json` | §4, §7 | The current verification-receipt contract: 1.0.0 plus `toolchain` / `subject` / `claim_id` provenance, a self-describing `error` verdict (`failure_kind`), per-obligation `coverage`, and the optional `control` block. |
| `schema/audit.schema.json` | §5, §7 | The versioned contract for a semantic audit verdict. |
| `autoprover_ref/receipts.py` | §7 | Receipt/audit-verdict dataclasses, schema validation, atomic writes. |
| `autoprover_ref/queue.py` | §2 | The evidence-driven target queue state machine. |
| `autoprover_ref/kernel_gate.py` | §4 | The checker-as-sound-oracle wrapper (pluggable checker command, with a timeout and a tool-failure-vs-property-failure seam). |
| `autoprover_ref/audit.py` | §5 | The semantic audit layer: vacuity, unexercised-hypothesis, name/content, scope, and missing-control heuristics. |
| `autoprover_ref/model_checker.py` | §4, §5 | A bounded model checker realizing the exhaustive obligation-level `held`/`vacuous`/`not-exercised`/`failed` bucket, wired in as a `kernel_gate.CheckerCommand`; also reports per-obligation precondition coverage for the audit layer. |
| `autoprover_ref/ratchet.py` | §6 | The monotone accepted set, explicit removal, dependency recheck. |
| `autoprover_ref/pipeline.py` | §§2–7 | Glue: drives one target through all of the above. |
| `autoprover_ref/adapters/kani.py` | §4, §7 | Adapter: parses a bounded-model-checker run log into one 2.0.0 receipt per harness, cross-checking the run's own harness counts and reporting every line it cannot classify. |
| `autoprover_ref/jsonschema_min.py` | — | The hand-rolled JSON Schema validator subset the schemas use. |

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
   `env_assumptions`, `failure_kind`, `control`, per-obligation
   `coverage`, `subject.unit` and `toolchain.features` are explicit,
   schema-checked nullable fields. The schemas enforce exactly when each
   may/must be null (see the `allOf`/`if`/`then`/`else` blocks in the
   schema files). Where two nulls would mean different things, they are
   given different encodings instead: `toolchain.features: null` means
   the tool has no feature-selection concept; `[]` means it has one and
   none were enabled.
4. **Atomic, exists-implies-complete writes** — `receipts.atomic_write_json`
   writes to a temp file in the target directory, `fsync`s, then
   `os.replace`s; a file that exists at the expected path is always the
   finished artifact.
5. **Explicit schema versioning** — every schema carries
   `schema_version` as a required, validated field, and `receipts.py`
   validates it as part of every read. The receipt format is at 2.0.0
   and the audit-verdict format at 1.2.0. Writers emit the current
   version; readers accept every published version and dispatch on the
   document's own `schema_version`, so a 1.0.0 receipt on disk still
   validates as 1.0.0 and is never re-read as if it were 2.0.0. Both
   directions are enforced and tested: an old document may not carry a
   field or code its own version never defined, and a new one may not
   omit what its version requires.

## Running the tests

```sh
cd reference
python3 run_tests.py
```

(equivalently: `PYTHONPATH=. python3 -m unittest discover -s tests -p "test_*.py" -v`,
run from `reference/`). This is pure Python — **no Lean installation is
needed** for anything under `tests/`. The runner prints the per-test
summary and the total itself, so the current count is whatever your own
run reports; `.github/workflows/ci.yml` runs exactly this command on
every push.

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
`model_checker.hypothesis_coverage(exploration, obligations)` reports the
other half of the picture the four statuses cannot express: for each
obligation, how many explored states SATISFIED its precondition and how
many VIOLATED it. An obligation no explored state violated the
precondition of has a guard that pruned nothing — its implication was
never exercised as an implication, which is what
`audit.check_unexercised_hypothesis` flags (see "Honesty notes" below).
The function only counts; the judgment lives in the audit layer, on the
§4 → §5 seam, exactly as the four statuses are assigned here and judged
there.

`model_check_example.py` runs four toy scenarios. Three exhibit all four
obligation statuses — a small closed traffic-light system for `held` and
`vacuous`, a long linear counter explored under a small bound for
`not-exercised`, and a buggy variant of the traffic light for `failed`.
The fourth checks one obligation, whose guard is "the light is not
stuck", against both traffic lights: it comes back `held` from both runs,
but the correct light never produces a state violating the guard (so the
audit layer flags `unexercised-hypothesis`) while the buggy one does (so
the audit passes). That a single status cannot separate those two cases
is exactly why this finding lives in the audit layer rather than as a
fifth status. The script prints which statuses it observed and whether
the unexercised hypothesis was flagged.

## Honesty notes (heuristic vs. sound, by design)

- `kernel_gate.py` is the only sound component in this package: its
  verdict comes entirely from a checker process's exit status, never
  from the prover's own claim. This is enforced by *not giving
  `KernelGate.check` any other input to base a verdict on* — there is
  no code path that reads a "prover says this is correct" flag.
- `audit.py`'s five HEURISTIC checks (vacuity, unexercised hypothesis,
  name/content, scope, and missing control) are explicitly documented, in
  the module docstring and in code comments, as structural heuristics
  operating on provenance text/metadata, reported enumeration counts and
  the shape of an evidence set — never as
  sound verification. (Its sixth check, obligation status, is not a
  heuristic: it reports what the checker itself said, per obligation, on
  the receipt under audit.) A target can pass all
  six checks and still be wrong in a way a human would catch
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
- `audit.check_unexercised_hypothesis` judges *counts an enumerating
  checker reported*, not semantics: "no explored state violated this
  precondition" is a fact about the states one run happened to enumerate,
  never a proof that the hypothesis is redundant. It abstains on any
  target that records no enumerated-obligation evidence (a proof-kernel
  target has no enumerated state space at all), skips unconditional
  obligations (nothing to exercise), and deliberately does NOT re-report
  the case where the precondition never fired — that is the
  vacuous/not-exercised finding the model checker already reports per
  obligation, and flattening the two would produce one ambiguous verdict
  where there are two distinct findings.
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

Moved to [`maintainers/divergences-from-architecture.md`](../maintainers/divergences-from-architecture.md).
