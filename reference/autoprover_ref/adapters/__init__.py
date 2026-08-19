"""Adapters: turn a real verification tool's output into receipts.

Everything under this package converts one tool's native output — a log,
a report file, an exit status — into `receipts.Receipt` objects the rest
of the pipeline can consume. An adapter is where the doctrine in
`docs/INTERFACES.md` meets a tool that does not yet follow it: the tool
emits prose for a human, and the adapter is the (small, testable, loudly
failing) layer that recovers structure from it.

Two rules every adapter here follows:

  * **Nothing is silently dropped.** A line the adapter cannot classify
    is reported as a finding, not skipped. A count the tool reports about
    itself is cross-checked against what the adapter parsed, and a
    mismatch is an error — an adapter that quietly returns 340 receipts
    for a 347-harness run is worse than one that refuses.
  * **What the log cannot say, the adapter does not invent.** Provenance
    the output does not contain (which build, which source commit, which
    claim this run is evidence for) is supplied by the caller and
    recorded as given; it is never guessed from context.
"""
