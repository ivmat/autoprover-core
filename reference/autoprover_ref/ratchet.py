"""The ratchet: the monotone accepted set (ARCHITECTURE.md §6).

The accepted set only grows through `accept()`, which requires *both* a
checker-accepted receipt and an audit-pass verdict presented together —
the ratchet re-reads the artifacts itself rather than trusting a
caller's summary of what upstream stages did. A result leaves the set
only through an explicit, logged `remove()` call (a discovered
unsoundness in a dependency, a definition change that invalidates the
statement) — never through a re-run that happens to fail once and is
quietly treated as "must have been wrong before."

`recheck_dependents()` is the hook ARCHITECTURE.md §6 asks for: when a
shared dependency changes, every accepted result depending on it is
marked for re-verification, and a re-check that comes back failing
raises a loud, logged blocking event rather than a quiet state change.
`record_recheck_result()` is a RE-verification path only, and enforces
that: it refuses a target with no outstanding mark for the dependency it
names, and it validates the receipt/audit pair exactly as `accept()`
does — so it can refresh an entry, never create one.
Like the queue in `queue.py`, the ratchet's history is an append-only
JSONL event log; the accepted set and the blocking-event list are both
derived by folding it.
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional, Union

from .receipts import AuditVerdict, Receipt, now_iso

__all__ = [
    "RatchetError",
    "AcceptedEntry",
    "RemovalEvent",
    "BlockingEvent",
    "Ratchet",
]


class RatchetError(Exception):
    """Raised when an accept/remove/recheck operation is not justified
    by the evidence it was given."""


@dataclass(frozen=True)
class AcceptedEntry:
    target_id: str
    candidate_id: str
    receipt: Receipt
    audit: AuditVerdict
    accepted_at: str

    def to_dict(self) -> dict:
        return {
            "target_id": self.target_id,
            "candidate_id": self.candidate_id,
            "receipt": self.receipt.to_dict(),
            "audit": self.audit.to_dict(),
            "accepted_at": self.accepted_at,
        }


@dataclass(frozen=True)
class RemovalEvent:
    target_id: str
    reason: str
    removed_at: str


@dataclass(frozen=True)
class BlockingEvent:
    """A loud, logged event: an accepted result stopped holding after a
    dependency changed. Per ARCHITECTURE.md §6 this must block further
    progress on anything downstream of the affected target until
    resolved — this reference implementation surfaces the event and
    leaves the "block downstream progress" enforcement to the caller
    (a real scheduler would refuse to schedule work depending on a
    target with an open blocking event; this module just makes that
    event impossible to miss)."""

    target_id: str
    triggering_dependency: str
    reason: str
    raised_at: str


class Ratchet:
    def __init__(self, log_path: Union[str, Path]):
        self.log_path = Path(log_path)
        self._events: list[dict] = []
        if self.log_path.exists():
            self._events = self._read_log(self.log_path)
        self._accepted: dict[str, AcceptedEntry] = {}
        self._blocking: list[BlockingEvent] = []
        # target_id -> the dependencies whose change is still owed a
        # re-verification for that target. Keyed rather than a bare set
        # because `record_recheck_result` must be able to ask "was THIS
        # target marked for THIS dependency", not merely "was something
        # marked at some point".
        self._marked_for_recheck: dict[str, set[str]] = {}
        self._fold()

    # -- persistence -----------------------------------------------------

    @staticmethod
    def _read_log(path: Path) -> list[dict]:
        events = []
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line:
                    events.append(json.loads(line))
        return events

    def _fold(self) -> None:
        """Rebuild the accepted set, blocking events, and pending-recheck
        marks purely by folding the event log — same discipline as
        `queue.TargetQueue`."""
        for event in self._events:
            etype = event["type"]
            if etype == "accept":
                receipt = Receipt.from_dict(event["receipt"])
                audit = AuditVerdict.from_dict(event["audit"])
                self._accepted[event["target_id"]] = AcceptedEntry(
                    target_id=event["target_id"],
                    candidate_id=event["candidate_id"],
                    receipt=receipt,
                    audit=audit,
                    accepted_at=event["at"],
                )
                self._marked_for_recheck.pop(event["target_id"], None)
            elif etype == "remove":
                self._accepted.pop(event["target_id"], None)
                self._marked_for_recheck.pop(event["target_id"], None)
            elif etype == "recheck_marked":
                self._marked_for_recheck.setdefault(event["target_id"], set()).add(
                    event["triggering_dependency"]
                )
            elif etype == "recheck_confirmed":
                receipt = Receipt.from_dict(event["receipt"])
                audit = AuditVerdict.from_dict(event["audit"])
                self._accepted[event["target_id"]] = AcceptedEntry(
                    target_id=event["target_id"],
                    candidate_id=event["candidate_id"],
                    receipt=receipt,
                    audit=audit,
                    accepted_at=event["at"],
                )
                # Only the confirmed dependency is discharged - a target
                # marked for multiple dependency changes stays marked
                # for the rest until each is confirmed in turn.
                outstanding = self._marked_for_recheck.get(event["target_id"])
                if outstanding is not None:
                    outstanding.discard(event["triggering_dependency"])
                    if not outstanding:
                        self._marked_for_recheck.pop(event["target_id"], None)
            elif etype == "blocking_event":
                self._blocking.append(BlockingEvent(
                    target_id=event["target_id"],
                    triggering_dependency=event["triggering_dependency"],
                    reason=event["reason"],
                    raised_at=event["at"],
                ))
                self._accepted.pop(event["target_id"], None)
                self._marked_for_recheck.pop(event["target_id"], None)
            else:  # pragma: no cover - defensive; log is append-only by this module only
                raise RatchetError(f"unknown ratchet event type {etype!r}")

    def _append(self, event: dict) -> None:
        with open(self.log_path, "a", encoding="utf-8") as f:
            f.write(json.dumps(event, sort_keys=True) + "\n")
            f.flush()
            os.fsync(f.fileno())
        self._events.append(event)

    # -- queries -----------------------------------------------------------

    @property
    def accepted_targets(self) -> frozenset[str]:
        return frozenset(self._accepted)

    def entry_for(self, target_id: str) -> Optional[AcceptedEntry]:
        return self._accepted.get(target_id)

    @property
    def blocking_events(self) -> tuple[BlockingEvent, ...]:
        return tuple(self._blocking)

    @property
    def marked_for_recheck(self) -> frozenset[str]:
        return frozenset(self._marked_for_recheck)

    # -- mutations -----------------------------------------------------------

    def accept(self, receipt: Receipt, audit: AuditVerdict) -> AcceptedEntry:
        """Accept a target into the monotone set. Requires BOTH a
        checker-accepted receipt AND an audit-pass verdict for the same
        target/candidate pair — checked directly against the artifacts,
        never inferred from a caller's say-so about upstream state."""
        if receipt.target_id != audit.target_id or receipt.candidate_id != audit.candidate_id:
            raise RatchetError(
                "receipt and audit verdict do not refer to the same target/candidate: "
                f"receipt=({receipt.target_id!r}, {receipt.candidate_id!r}) "
                f"audit=({audit.target_id!r}, {audit.candidate_id!r})"
            )
        if receipt.verdict != "accepted":
            raise RatchetError(
                f"ratchet requires a checker-accepted receipt, got verdict={receipt.verdict!r}"
            )
        if audit.verdict != "pass":
            raise RatchetError(
                f"ratchet requires an audit-pass verdict, got verdict={audit.verdict!r} "
                f"(failure_reason={audit.failure_reason!r})"
            )
        at = now_iso()
        self._append({
            "type": "accept",
            "target_id": receipt.target_id,
            "candidate_id": receipt.candidate_id,
            "receipt": receipt.to_dict(),
            "audit": audit.to_dict(),
            "at": at,
        })
        entry = AcceptedEntry(
            target_id=receipt.target_id,
            candidate_id=receipt.candidate_id,
            receipt=receipt,
            audit=audit,
            accepted_at=at,
        )
        self._accepted[receipt.target_id] = entry
        self._marked_for_recheck.pop(receipt.target_id, None)
        return entry

    def remove(self, target_id: str, reason: str) -> RemovalEvent:
        """Explicit, logged removal — the only way an accepted result
        leaves the set other than a failed recheck (`record_recheck_result`,
        which logs its own `blocking_event`)."""
        if target_id not in self._accepted:
            raise RatchetError(f"target {target_id!r} is not currently accepted")
        at = now_iso()
        self._append({"type": "remove", "target_id": target_id, "reason": reason, "at": at})
        del self._accepted[target_id]
        return RemovalEvent(target_id=target_id, reason=reason, removed_at=at)

    def recheck_dependents(self, changed_dep: str, dependents: Iterable[str]) -> list[str]:
        """Mark every currently-accepted target in `dependents` as
        needing re-verification because `changed_dep` changed
        (ARCHITECTURE.md §6). Returns the subset actually marked (targets
        not currently accepted are skipped — there is nothing to
        re-verify for them). Marking does not itself remove anything
        from the accepted set; call `record_recheck_result` with the
        fresh receipt/audit once the re-verification runs."""
        marked = []
        at = now_iso()
        for target_id in dependents:
            if target_id in self._accepted:
                self._append({
                    "type": "recheck_marked",
                    "target_id": target_id,
                    "triggering_dependency": changed_dep,
                    "at": at,
                })
                self._marked_for_recheck.setdefault(target_id, set()).add(changed_dep)
                marked.append(target_id)
        return marked

    def record_recheck_result(
        self,
        target_id: str,
        changed_dep: str,
        receipt: Optional[Receipt],
        audit: Optional[AuditVerdict],
    ) -> Optional[BlockingEvent]:
        """Record the outcome of re-verifying a marked target. If the
        fresh receipt/audit still justify acceptance, the entry is
        refreshed (new receipt/audit, same monotone membership). If not
        — receipt missing/rejected, or audit missing/failed — the target
        is removed from the accepted set and a loud BlockingEvent is
        raised and returned; this is the one path in this module where
        a re-run failing is *not* silently treated as "the old result
        must have been wrong, moving on" — it is a first-class, logged
        event a caller is expected to act on before letting anything
        downstream of `target_id` proceed.

        This is a RE-verification path, never a second admission path.
        Three things are therefore refused outright (RatchetError) rather
        than being recorded either way:

          * a target with no outstanding recheck mark — a target that was
            never accepted, or never marked by `recheck_dependents`, has
            no re-verification to record, and a first admission has to go
            through `accept()`;
          * a `changed_dep` this target was not marked for — the mark is
            what says which dependency change is owed a re-check, so an
            unrelated dependency cannot discharge it;
          * a receipt/audit pair that is not about one artifact, or not
            about `target_id` — the same validation `accept()` performs,
            for the same reason: a receipt about candidate A and an audit
            about candidate B are two statements about two things, and
            reading them as one is exactly how an unaudited candidate
            would enter the set.

        A refusal changes nothing: the entry stays as it was and the
        recheck mark stays outstanding, so the re-verification is still
        owed.
        """
        outstanding = self._marked_for_recheck.get(target_id)
        if outstanding is None:
            raise RatchetError(
                f"target {target_id!r} is not marked for re-verification; "
                f"record_recheck_result records the outcome of a mark made by "
                f"recheck_dependents(), it is not a second way into the accepted set "
                f"(use accept() with a receipt and an audit verdict)"
            )
        if changed_dep not in outstanding:
            raise RatchetError(
                f"target {target_id!r} is marked for re-verification after "
                f"{sorted(outstanding)!r} changed, not {changed_dep!r}"
            )

        if receipt is not None and audit is not None:
            if receipt.target_id != audit.target_id or receipt.candidate_id != audit.candidate_id:
                raise RatchetError(
                    "receipt and audit verdict do not refer to the same target/candidate: "
                    f"receipt=({receipt.target_id!r}, {receipt.candidate_id!r}) "
                    f"audit=({audit.target_id!r}, {audit.candidate_id!r})"
                )
            if receipt.target_id != target_id:
                raise RatchetError(
                    f"recheck artifacts are about target {receipt.target_id!r}, but the "
                    f"target being re-verified is {target_id!r}"
                )

        holds = (
            receipt is not None
            and audit is not None
            and receipt.verdict == "accepted"
            and audit.verdict == "pass"
        )
        at = now_iso()
        if holds:
            self._append({
                "type": "recheck_confirmed",
                "target_id": target_id,
                "candidate_id": receipt.candidate_id,
                "receipt": receipt.to_dict(),
                "audit": audit.to_dict(),
                "triggering_dependency": changed_dep,
                "at": at,
            })
            self._accepted[target_id] = AcceptedEntry(
                target_id=target_id,
                candidate_id=receipt.candidate_id,
                receipt=receipt,
                audit=audit,
                accepted_at=at,
            )
            # Discard only the dependency just confirmed - the target
            # stays marked for any other outstanding dependency until
            # its own confirmation arrives.
            outstanding.discard(changed_dep)
            if not outstanding:
                self._marked_for_recheck.pop(target_id, None)
            return None

        reason = "recheck failed after dependency change: "
        if receipt is None or audit is None:
            reason += "no fresh receipt/audit produced"
        elif receipt.verdict != "accepted":
            reason += f"checker verdict={receipt.verdict!r}"
        else:
            reason += f"audit verdict={audit.verdict!r} (failure_reason={audit.failure_reason!r})"

        self._append({
            "type": "blocking_event",
            "target_id": target_id,
            "triggering_dependency": changed_dep,
            "reason": reason,
            "at": at,
        })
        self._accepted.pop(target_id, None)
        self._marked_for_recheck.pop(target_id, None)
        event = BlockingEvent(
            target_id=target_id, triggering_dependency=changed_dep, reason=reason, raised_at=at
        )
        self._blocking.append(event)
        return event
