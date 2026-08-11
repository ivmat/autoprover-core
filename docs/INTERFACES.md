# Interfaces: verification output is an API

`docs/ARCHITECTURE.md` states the general rule: every boundary between
components in an autonomous proving system has to be a typed contract with
a structured verdict, not a prose summary — a proof-kernel or
model-checker oracle's verdict is machine-*checkable* (independently
re-derivable from the recorded artifact); an audit verdict is
machine-*readable* (structured, typed) but is a judgment, not a fact with
an independent re-derivation procedure. This document states the
structured-output half of that doctrine concretely, and what it implies
for every boundary in the architecture.

## The doctrine

A verifier's result is not a log to be read. It is an **API response**,
and it should be held to the same standard any API response is held to:

1. **Structured, not narrative.** A caller should be able to consume the
   result programmatically — parse a field, branch on an enum — without
   ever grepping human prose for the word "failed."
2. **Exhaustive, not partial.** Every property or obligation the tool was
   asked to check gets an entry in the result, including the ones that
   were *not* meaningfully checked. A result that only lists what passed
   and is silent about what wasn't exercised looks identical to a result
   with genuine full coverage — and that ambiguity is exactly the
   vacuous-acceptance failure mode described in `docs/ARCHITECTURE.md`
   §5. The fix is structural: give "this obligation was vacuous / never
   reached" its own explicit, first-class bucket in the output, so it is
   visibly distinct from "this obligation was checked and held."
3. **Null never means a guess.** If a field is absent or a status is
   unknown, the schema must say so as a distinct, explicit value — never
   as an empty string or a missing key that a caller might silently
   coerce into "false" or "passed." A consumer should never have to infer
   intent from absence.
4. **Atomic, exists-implies-complete writes.** A result artifact should
   never be observable in a partially-written state. If a file with the
   expected name exists, it is the finished result — not a result that
   might still be being appended to. This is ordinary durability
   discipline (write to a temp path, then atomically rename), applied
   because a scheduler consuming these results has no other way to know
   whether a file it sees is done.
5. **Schema versioning discipline.** The result format itself is a
   contract with its own consumers. Its schema is versioned explicitly, so
   that a consumer can tell "this is an old-format result I should not
   over-interpret" from "this is the current format." A breaking change to
   the result shape is a version bump, not a silent field rename.

None of this is exotic. It is the same discipline any well-built API or
event schema is held to. What is worth stating explicitly is that a
*verification tool's output* deserves exactly the same treatment — because
the temptation, in tooling built for humans to read, is to treat the
result as a report rather than as an interface.

## Where this shows up in real verifiers

Mature verification tools are converging on the same conclusion. Static
analyzers and verifiers increasingly emit structured, machine-readable
result formats (SARIF being the ecosystem-wide example) precisely because
downstream systems — CI pipelines, dashboards, schedulers — cannot be
built on terminal prose. But general-purpose result formats are usually
built around *findings* (things that went wrong), and a proving pipeline
needs the dual as well: a first-class, exhaustive account of what was
*proved*, what was *vacuous*, and what was *never exercised*. That is the
gap the doctrine above addresses, and closing it in any given verifier is
ordinary, contributable engineering — a schema, an exporter, and the five
properties applied without exception.

The connection to this project's architecture is direct: an autonomous
proving system composed of many verification boundaries (kernel, audit,
ratchet) is only as trustworthy as its least-structured interface.
Treating every one of those interfaces as an API with the same five
properties is the concrete form the doctrine takes.
