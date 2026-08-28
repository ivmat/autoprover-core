# Assumptions

**What this file is.** The list of *known* assumptions everything here
rests on — the corpus's kernel-green claim, the architecture's soundness
argument, and any receipt this pipeline pattern produces. It includes the
assumptions that are irrelevant almost always, because "almost always" is
itself an assumption. `docs/LIMITATIONS.md` states what the proofs do and do
not establish; this file states what the whole apparatus stands on
underneath that.

**The contract this file keeps.**

- Entries are **IN FOCUS** (critical, actively examined; each names what
  would falsify it and what leans on it) or **OUT OF FOCUS** (parked, but
  never removed from mind).
- An assumption leaves this file only by **tombstone** — moved to §T with
  the reason recorded — never by deletion. Ids are never reused.
- The list is bounded by what we know to ask about. It cannot enumerate
  unknown unknowns, and **A-0 exists so that limit is stated inside the
  list rather than around it.** No claim of the form "all assumptions are
  stated" is made anywhere in this repository.

Format: `A-<n> · statement · fails-if: <how we would notice, or what
would change our mind> · load-bearing-for: <what leans on it>`. The
numbering gap between the two sections is deliberate: the low range is
reserved for in-focus entries.

## In focus

- **A-0 · This list is incomplete.** There exist assumptions we have not
  identified.
  *fails-if:* never falsifiable; the entry exists to block
  "fully enumerated" overclaims.
  *load-bearing-for:* every claim of the form "all assumptions stated".

- **A-1 · An LLM-based autoprover system can be built and be SOUND.**
  There is no proof of this; it is the founding bet. The architecture
  reduces it to "soundness lives entirely in the non-LLM gates" (kernel,
  checker, audit). That reduces A-1 to A-2..A-5, plus the claim that no
  LLM output reaches a trust decision ungated. **That reduction is an
  argument, not a theorem.**
  *fails-if:* any path is found where generative output changes accepted
  state without passing a sound gate; or a gate proves game-able by
  adversarial candidate structure.
  *load-bearing-for:* the entire pattern documented in
  `docs/ARCHITECTURE.md`.

- **A-2 · The proof kernels are sound** — the Lean 4 kernel at the pinned
  toolchain version, and a bounded model checker's core decision
  procedures for the properties it decides.
  *fails-if:* upstream soundness advisories; differentials between
  independent checkers on the same obligation (checker diversity exists
  precisely to bound this).
  *load-bearing-for:* every kernel-checked and model-checked claim.

- **A-3 · The toolchains do what their semantics promise** — a compiler
  compiles per its reference, Lean elaborates per its typing rules, the
  language model a bounded checker uses matches the language. We verify
  artifacts, not the compilers that build them.
  *fails-if:* miscompilation evidence at the pinned versions;
  toolchain supply-chain compromise.
  *load-bearing-for:* the bridge from "verified model" to "the artifact
  actually shipped" — see `docs/LIMITATIONS.md` §2, which is the same gap
  stated from the other side.

- **A-4 · The LLM vendor's models act in good faith within their stated
  behavior** — no deliberate sabotage, no hidden agenda in generated
  proofs or code; failures are incompetence-shaped, not adversarial.
  The architecture is deliberately built so this assumption carries as
  little weight as possible (generated output is never a verdict), but
  orchestration, judgment calls, and every prose summary still lean on
  it.
  *fails-if:* behavioral evidence of systematic deception; vendor
  incident disclosures.
  *load-bearing-for:* everything a generative session produced that a
  gate did not check — including most prose documentation.

- **A-5 · The gates actually run, and their receipts are authentic** —
  the hooks fire, the logs read back are the logs the runs wrote, and the
  clock and filesystem of the machine that ran them are honest.
  *fails-if:* a fixture designed to fail stops failing; receipt hashes
  that do not match the artifacts they name; scheduling or lock
  anomalies in the runner that make "this ran" unverifiable.
  *load-bearing-for:* the entire evidence chain — a receipt is worth
  exactly what its production is worth.

- **A-6 · The operators are honest with the ledger** — the people and
  sessions in the loop record what happened, not what should have
  happened. This assumption is known-weak: in practice it fails by
  **drift**, not malice — a probe described later as if it had been a
  contract, a green reported in prose without the artifact behind it.
  That is exactly why the gates exist, and why machinery that does not
  depend on this assumption is preferred wherever it can be built.
  *fails-if:* a rigor re-review finds claims with no artifact behind
  them.
  *load-bearing-for:* everything not yet machine-checked.

## Out of focus (parked, not gone)

- **A-10 · The code host serves the repositories faithfully** — no
  tampering, no silent history rewrite, and repositories marked private
  are actually private.
  *fails-if:* object hashes that disagree with a local clone (git's
  content-addressing makes tampering detectable *if* you compare — which
  is rarely done).
  *load-bearing-for:* every "the published branch contains X" claim.

- **A-11 · Rented compute executes what we boot** — no hypervisor-level
  result tampering; preemption is availability-shaped, not adversarial.
  *load-bearing-for:* every receipt produced somewhere other than the
  machine reading it. Such receipts are currently unsigned, which is a
  known gap rather than a solved problem.

- **A-12 · The machine a check runs on is uncompromised** — kernel,
  service manager, and `PATH` hygiene. `PATH` shadowing in particular is
  treated as a live hazard, not a theoretical one: the wrong binary
  answering to the right name is the cheapest way to fake a green.
  *load-bearing-for:* local receipts, keys, everything produced locally.

- **A-13 · Package registries deliver the bytes their lockfiles name.**
  Pins name versions and hashes check integrity where lockfiles exist,
  but the resolution infrastructure itself is trusted.
  *load-bearing-for:* every build.

- **A-14 · The classical results formalized here are correctly attributed,
  and the models model them.** A Lean theorem about "Dekker's algorithm"
  is a theorem about *this repository's* transition system, not about
  history's; the correspondence is scholarly diligence, not proof. Each
  corpus module states its own scope for this reason.
  *load-bearing-for:* the corpus's value as evidence about anything
  outside itself.

- **A-15 · Time meters are honest** — wall clocks order the evidence, and
  quotas and alerts mean what they say.
  *load-bearing-for:* every timestamp in every receipt.

- **A-16 · Git itself** — object integrity, no collision exploitation
  against these repositories.
  *load-bearing-for:* every commit-pinned claim in every receipt.

## §T Tombstones

None yet. Retiring an assumption requires the reason to be recorded here;
that is what makes the list append-only in practice and not just in
intent.
