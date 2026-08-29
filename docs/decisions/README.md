# Architecture decisions

Short ADRs (Context / Decision / Consequences), each `Accepted`. Each cites
the repository text it extracts from; see `docs/GLOSSARY.md` for the terms
they use.

- [ADR-001 — The kernel gate, not the prover, is where trust is decided](ADR-001-kernel-gate-not-prover.md)
- [ADR-002 — The receipt schema is explicitly versioned, and a breaking change ships as a new file](ADR-002-receipt-schema-versioning.md)
- [ADR-003 — The proven set is monotone; it only shrinks through a logged removal event](ADR-003-monotone-ratchet.md)
- [ADR-004 — A result that was never exercised is not the same as one that failed — and a heuristic that cannot tell, abstains](ADR-004-abstain-vs-fail.md)
- [ADR-005 — An acceptance manifest is a generated projection of the receipt store — never a hand-written artifact](ADR-005-manifest-is-generated-from-receipts.md)
