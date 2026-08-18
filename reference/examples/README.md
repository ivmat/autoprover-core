# Worked example: kernel accepts both, audit flags one

This directory drives two tiny, self-contained Lean targets through the
full reference pipeline (`autoprover_ref.pipeline.Pipeline`) and shows
the point of `docs/ARCHITECTURE.md` §5 concretely: **the kernel gate
alone cannot distinguish a genuine result from a vacuous one — both
targets below are kernel-accepted — and the semantic audit layer is what
tells them apart.**

## The two targets

- **`lean/Genuine.lean`** — `nonempty_has_length_ge_one`: if a list has
  at least one element, its length is at least 1. Genuinely conditional
  — the precondition `0 < l.length` is satisfiable, and the file also
  ships `nonempty_witness`, a concrete instance (`l = [1]`, checked by
  `decide`) showing it. That witness is what the vacuity check in
  `autoprover_ref/audit.py` looks for.
- **`lean/Vacuous.lean`** — `falsely_sorted_claim`: named and claimed as
  a sortedness result, but its precondition `l.length < 0` can never
  hold for a `List Nat`. The proof is real (the kernel is right to
  accept it — the derivation is valid), but the claim it licenses is
  empty: `Sorted l` is never actually exercised. No non-vacuity witness
  is recorded, because none exists.

Both files are pure Lean 4 core with no imports (same zero-dependency
style as `corpus/`), each a single isolated file. **Neither is part of
`corpus/` and running this example never invokes `lake build`.**

## Running it

```sh
cd reference/examples
python3 run_example.py
```

This invokes the real `lean` executable (found on `PATH`) on exactly
these two files — nothing else — via
`autoprover_ref.kernel_gate.lean_checker_command`, which is one
interchangeable value for the gate's injectable `checker_command`
parameter (see `reference/autoprover_ref/kernel_gate.py`). If `lean` is
not installed, the script explains that and exits 0 without attempting
the Lean-backed run; every test in `reference/tests/` still runs with no
Lean installed at all.

Receipts are written under `reference/examples/_run/` (gitignored — it's
a run artifact, regenerated every time you run the script, not checked
in as source).

## What actually happened when this was run

Both targets reach `kernel verdict: accepted` — the kernel is a sound
oracle for exactly the question it answers ("does this derivation
establish this statement"), and both derivations are valid. The audit
layer then diverges:

| target    | kernel verdict | audit verdict | failure_reason          | final queue state |
|-----------|-----------------|----------------|--------------------------|--------------------|
| genuine   | accepted        | pass           | *(null)*                | `accepted` (ratcheted) |
| vacuous   | accepted        | fail           | `vacuous-precondition`  | `queued` (returned for retry) |

The genuine target's receipt (`genuine.genuine-v1.kernel.json`):

```json
{
  "schema_version": "1.0.0",
  "target_id": "genuine",
  "candidate_id": "genuine-v1",
  "checker": {"kind": "kernel", "name": "lean", "version": "Lean (version 4.31.0, ...)"},
  "verdict": "accepted",
  "certificate": {
    "checked_file": ".../reference/examples/lean/Genuine.lean",
    "toolchain_id": "leanprover/lean4:v4.31.0"
  },
  "harness": null,
  "bound": null,
  "env_assumptions": null,
  "obligations": [{"id": "genuine", "status": "held"}],
  "produced_at": "2026-08-12T21:23:23.873682+00:00"
}
```

and its audit verdict (`genuine.genuine-v1.audit.json`) — `pass`, with
`failure_reason: null`:

```json
{
  "schema_version": "1.0.0",
  "target_id": "genuine",
  "candidate_id": "genuine-v1",
  "verdict": "pass",
  "failure_reason": null,
  "details": {
    "checks_run": ["vacuity", "name_content"],
    "vacuity": {"check": "vacuity", "preconditions_checked": ["0 < l.length"]},
    "name_content": {"check": "name_content", "keywords_judged": []}
  },
  "produced_at": "2026-08-12T21:23:23.874915+00:00"
}
```

The vacuous target's kernel receipt looks structurally the same shape as
the genuine one — `verdict: "accepted"`, a real certificate — which is
exactly the point: nothing in the kernel receipt itself distinguishes
it. Its audit verdict (`vacuous.vacuous-v1.audit.json`) is where the
difference becomes a structured, machine-readable fact:

```json
{
  "schema_version": "1.0.0",
  "target_id": "vacuous",
  "candidate_id": "vacuous-v1",
  "verdict": "fail",
  "failure_reason": "vacuous-precondition",
  "details": {
    "check": "vacuity",
    "missing_witness_for": ["l.length < 0"]
  },
  "produced_at": "2026-08-12T21:23:24.051167+00:00"
}
```

Because the ratchet (`autoprover_ref/ratchet.py`) only admits a target on
a checker-accepted receipt **and** an audit-pass verdict together, the
vacuous target never enters the accepted set — the pipeline instead logs
a `RequeueDecision` and returns it to `queued` (see
`autoprover_ref/pipeline.py`). Re-run `run_example.py` to reproduce this
end to end; the script itself checks this exact pattern and prints
`Expected pattern observed: True` on success.

## The other example in this directory

`model_check_example.py` (run with `python3 model_check_example.py`, same
directory, no `lean` needed) is a separate worked example: it drives
`autoprover_ref/model_checker.py`, a small bounded model checker, through
four toy scenarios: three exhibit all four obligation statuses (`held`,
`vacuous`, `not-exercised`, `failed`) that `receipt.schema.json` makes
first-class, and the fourth exhibits the finding no status can express —
an obligation whose precondition NO explored state violated, `held` in
both runs, flagged by the audit layer against the system whose states
never violate the guard and passing against the one whose states do. See
`reference/README.md`'s "The model checker" section for the walkthrough.

## Divergence note

The audit layer's vacuity check operates on the *provenance record*
(`TargetProvenance.preconditions` / `.non_vacuity_witness` in
`autoprover_ref/audit.py`), not on the Lean statement itself — it is a
structural check on whether a witness was recorded, not a satisfiability
solver. In this worked example the provenance is written by hand to
match what the Lean file actually states (see `run_example.py`), which
is realistic: in a real pipeline, target selection (ARCHITECTURE.md §1)
is responsible for producing that provenance record honestly in the
first place. A provenance record that lies about its own preconditions
is outside what any purely-structural audit check can catch — this is
the same "machine-readable judgment, not an independently re-derivable
fact" caveat ARCHITECTURE.md §7 draws for the whole audit layer.
