# ADR-002: The receipt schema is explicitly versioned, and a breaking change ships as a new file

**Status:** Accepted

## Context

`docs/INTERFACES.md` property 5 states the doctrine: "The result format
itself is a contract with its own consumers. Its schema is versioned
explicitly, so that a consumer can tell 'this is an old-format result I
should not over-interpret' from 'this is the current format.' A breaking
change to the result shape is a version bump, not a silent field rename."

The receipt format needed a breaking change: version 1.0.0 could not
attribute a verdict to an exact build (only `checker.version`, which
cannot distinguish two builds of one release), had no `claim_id` to
aggregate per-harness receipts under one claim, could not reach the
`error` verdict in practice, dropped hypothesis-coverage numbers between
the checker and the audit layer, and had no representation for a control
receipt (see `maintainers/divergences-from-architecture.md` for the full
account of what 1.0.0 lacked and why each absence mattered).

## Decision

`reference/schema/receipt.schema-2.0.0.json` ships as its own file,
alongside `reference/schema/receipt.schema.json` (1.0.0), rather than
widening the 1.0.0 schema in place. Every document declares its own
`schema_version` as a required, `const`-validated field; a conforming
reader must dispatch on that field and validate against the matching
schema, rather than re-reading an old document as if it were the new
format. As the 2.0.0 schema's own description states: "a 1.0.0 reader
meeting a 2.0.0 document would find fields it cannot interpret, and a
1.0.0 document may not carry them."

## Consequences

A 1.0.0 receipt on disk still validates as 1.0.0, and a conforming
reader must not misread it as 2.0.0; a 2.0.0 document may not omit what
2.0.0 requires, and a 1.0.0 document may not carry 2.0.0-only fields
(`toolchain`, `subject`, `claim_id`, `failure_kind`, per-obligation
`coverage`, `control`) — enforced by the schema, not by convention, and
covered by `reference/tests/test_receipts.py`'s version-discipline
tests. The same discipline applies to the audit-verdict schema, which
has grown two further versions (1.1.0 for `unexercised-hypothesis`,
1.2.0 for `missing-control`) as additive, `enum`-gated changes within
`reference/schema/audit.schema.json` rather than as new files: each
addition is forbidden to documents written to an earlier version and
not required of later ones, per that schema's own version-history
description.
