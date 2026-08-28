# ADR-001: The kernel gate, not the prover, is where trust is decided

**Status:** Accepted

## Context

An LLM prover component generates candidate proofs. It is expected to be
wrong often — to hallucinate, to produce a proof of the wrong statement, or
no proof at all. `docs/ARCHITECTURE.md` §3 states the prover's contract: it
guarantees either a candidate artifact in the checker's exact input syntax,
tagged with the target it claims to address, or an explicit "no candidate"
result — never a verdict. "A prover output is never treated as a verdict —
it is only ever an input to the next gate." Because more candidates can be
generated per unit time than in older, non-LLM proving pipelines, "the
system's soundness has to depend entirely on what happens downstream,
never on how plausible the candidate looks."

## Decision

Soundness is placed entirely in `kernel_gate.py`, the reference
implementation of `docs/ARCHITECTURE.md` §4's checker-as-sound-oracle. Its
verdict comes entirely from a checker process's exit status, never from
the prover's own claim: there is no code path that reads a "prover says
this is correct" flag. `kernel_gate.py` is documented as the only sound
component in the reference package for exactly this reason.

## Consequences

A prover can be swapped, extended, or run many times in parallel without
touching the trust boundary, because nothing it emits is ever read as a
verdict. Every downstream component (audit, ratchet) can rely on "kernel
gate accepted" as a fact about the checker's exit status, never as a fact
mediated by prover confidence, prose, or prompt engineering. This is also
why the kernel gate, and not the prover or the audit layer, is the
component `docs/LIMITATIONS.md` and `reference/README.md`'s honesty notes
single out as sound rather than heuristic.
