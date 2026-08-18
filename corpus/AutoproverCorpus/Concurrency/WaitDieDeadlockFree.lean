/-
  AutoproverCorpus.Concurrency.WaitDieDeadlockFree

  Timestamp-ordered deadlock PREVENTION: the wait-die and wound-wait rules of Rosenkrantz,
  Stearns and Lewis keep the wait-for graph acyclic, so a circular wait can never form.

  Under WAIT-DIE, a transaction requesting a lock held by another either waits — only if it is
  OLDER (smaller timestamp) than the holder — or dies (aborts and restarts). So every surviving
  wait-for edge points from an older transaction to a younger one, and the timestamp strictly
  INCREASES along it. Under WOUND-WAIT the decision is mirrored (an older requester wounds the
  younger holder; only a younger requester waits), so the timestamp strictly DECREASES along
  every wait-for edge. Either way a cycle would force a timestamp to be strictly below itself.

  Both rules are proved here as instances of one lemma (`no_cycle_of_strict_potential`): a
  wait-for graph carrying any strictly monotone integer potential along its edges is acyclic.

  This is NOT a restatement of this corpus's `ResourceOrderingAcyclic`, which prevents deadlock
  by imposing a fixed global order on RESOURCES and constraining which resource a process may
  request next. Here no order on resources is assumed and any request is permitted; acyclicity
  comes from the policy's ABORT decisions, ordered by transaction timestamps. The two modules
  share only the monotone-potential skeleton, which this module isolates as a lemma.

  SCOPE: safety only — the wait-for graph is acyclic, so no circular wait (and hence, by the
  disclosed textbook corollary, no deadlock under the Coffman conditions). Liveness is NOT
  proved: the classical no-starvation argument for wait-die and wound-wait — a restarted
  transaction keeps its ORIGINAL timestamp, so it eventually becomes the oldest and cannot be
  aborted forever — is not formalized here, and neither is the abort/restart machinery itself.

  Attribution: D. J. Rosenkrantz, R. E. Stearns and P. M. Lewis II, "System Level Concurrency
  Control for Distributed Database Systems", ACM TODS, 1978.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Order.TransitiveClosure

namespace AutoproverCorpus.WaitDieDeadlockFree

open AutoproverCorpus.TransitiveClosure (TC)

variable {Txn : Type}

/-! ### Lock state and the wait-for graph -/

/-- A snapshot of a lock manager: which transaction (if any) holds the lock on each data item,
    and which item (if any) each transaction is currently blocked requesting. Nothing here
    constrains WHICH item a transaction may request — that is the difference from ordered
    resource acquisition. -/
structure LockState (Txn : Type) where
  holder : Nat → Option Txn
  request : Txn → Option Nat

/-- A wait-for edge: `ti` is blocked requesting an item whose lock `tj` holds. -/
def WaitsFor (st : LockState Txn) (ti tj : Txn) : Prop :=
  ∃ r, st.request ti = some r ∧ st.holder r = some tj

/-- Reachability in the wait-for graph: the transitive closure of the edges. -/
abbrev Blocks (st : LockState Txn) (ti tj : Txn) : Prop := TC (WaitsFor st) ti tj

/-- No circular wait: no transaction waits, transitively, for itself. -/
def Acyclic (st : LockState Txn) : Prop := ∀ t, ¬ Blocks st t t

/-! ### The shared skeleton: a strictly monotone potential forbids cycles -/

/-- **Monotone-potential lemma.** If some `Nat`-valued potential strictly increases along every
    wait-for edge, the wait-for graph is acyclic: a cycle would carry the potential strictly
    above itself. The potential is arbitrary — the two timestamp rules below differ only in
    which potential they supply. -/
theorem no_cycle_of_strict_potential {st : LockState Txn} (pot : Txn → Nat)
    (hmono : ∀ ti tj, WaitsFor st ti tj → pot ti < pot tj) : Acyclic st := by
  have hreach : ∀ {ti tj : Txn}, Blocks st ti tj → pot ti < pot tj :=
    fun h => AutoproverCorpus.TransitiveClosure.tc_least
      (s := fun a b => pot a < pot b)
      (fun _ _ hxy => hmono _ _ hxy)
      (fun _ _ _ hxy hyz => Nat.lt_trans hxy hyz)
      h
  exact fun t ht => Nat.lt_irrefl (pot t) (hreach ht)

/-! ### The two timestamp rules -/

/-- **Wait-die.** A requester waits only when it is OLDER than the holder (its timestamp is
    smaller); otherwise it dies — aborts and restarts — and so contributes no wait-for edge.
    The predicate states exactly the invariant the rule maintains on surviving edges. -/
def WaitDie (ts : Txn → Nat) (st : LockState Txn) : Prop :=
  ∀ ti tj, WaitsFor st ti tj → ts ti < ts tj

/-- **Wound-wait.** The mirrored decision: an older requester WOUNDS the younger holder (which
    aborts), so only a YOUNGER requester is left waiting — every surviving wait-for edge points
    from a younger transaction to an older one. -/
def WoundWait (ts : Txn → Nat) (st : LockState Txn) : Prop :=
  ∀ ti tj, WaitsFor st ti tj → ts tj < ts ti

/-- **Wait-die prevents circular wait.** Timestamps strictly increase along wait-for edges, so
    they are the potential the lemma needs. -/
theorem waitDie_acyclic {ts : Txn → Nat} {st : LockState Txn} (h : WaitDie ts st) :
    Acyclic st :=
  no_cycle_of_strict_potential ts h

/-- **Wound-wait prevents circular wait.** Timestamps strictly DECREASE along wait-for edges,
    so the potential is their negation — expressed over `Nat` as a bound `B` minus the
    timestamp, for any bound `B` covering the timestamps in play. (Any strictly decreasing
    `Nat` chain is finite; using an explicit bound keeps the argument inside `Nat` without
    introducing `Int`.) -/
theorem woundWait_acyclic {ts : Txn → Nat} {st : LockState Txn} (B : Nat)
    (hB : ∀ t, ts t ≤ B) (h : WoundWait ts st) : Acyclic st :=
  no_cycle_of_strict_potential (fun t => B - ts t) (by
    intro ti tj hedge
    have hlt := h ti tj hedge
    have h1 := hB ti
    have h2 := hB tj
    omega)

/-- **The general contrapositive.** A circular wait can only arise in a state where the
    timestamp discipline was violated — for any timestamp assignment whatsoever. -/
theorem circular_wait_refutes_waitDie {ts : Txn → Nat} {st : LockState Txn}
    (h : ¬ Acyclic st) : ¬ WaitDie ts st :=
  fun hwd => h (waitDie_acyclic hwd)

/-! ### (a) Instance, positive: a three-transaction wait chain under wait-die -/

/-- Three transactions, timestamped in start order: `t1` oldest, `t3` youngest. -/
inductive Txn3 where
  | t1 | t2 | t3
  deriving DecidableEq

open Txn3

/-- Start timestamps: older transactions have smaller timestamps. -/
abbrev ts3 : Txn3 → Nat
  | .t1 => 10
  | .t2 => 20
  | .t3 => 30

/-- `t2` holds item `1`, `t3` holds item `2`; item `3` is free. -/
abbrev holder3 : Nat → Option Txn3
  | 1 => some t2
  | 2 => some t3
  | _ => none

/-- `t1` (oldest) is blocked on item `1`, `t2` on item `2`; `t3` waits for nothing. Both waits
    are wait-die-legal: in each case the requester is older than the holder. -/
abbrev request3 : Txn3 → Option Nat
  | .t1 => some 1
  | .t2 => some 2
  | .t3 => none

def st3 : LockState Txn3 := { holder := holder3, request := request3 }

/-- The state genuinely satisfies the wait-die invariant, checked edge by edge (the case
    analysis is over the finitely many transaction pairs, with the `WaitsFor` witness
    destructured). -/
theorem st3_waitDie : WaitDie ts3 st3 := by
  rintro ti tj ⟨r, hreq, hhold⟩
  cases ti with
  | t1 =>
    simp only [st3, request3, Option.some.injEq] at hreq
    subst hreq
    simp only [st3, holder3, Option.some.injEq] at hhold
    subst hhold
    decide
  | t2 =>
    simp only [st3, request3, Option.some.injEq] at hreq
    subst hreq
    simp only [st3, holder3, Option.some.injEq] at hhold
    subst hhold
    decide
  | t3 => simp [st3, request3] at hreq

/-- **Non-vacuity: the wait-for graph really has a two-hop path.** `t1` waits for `t2`, which
    waits for `t3` — the acyclicity theorem is applied to a state with genuine blocking, not to
    an empty graph. -/
theorem st3_blocks_t1_t3 : Blocks st3 t1 t3 :=
  TC.trans (TC.base (show WaitsFor st3 t1 t2 from ⟨1, rfl, rfl⟩))
           (TC.base (show WaitsFor st3 t2 t3 from ⟨2, rfl, rfl⟩))

/-- The main theorem applied: despite the genuine wait chain, no circular wait exists. -/
example : Acyclic st3 := waitDie_acyclic st3_waitDie

/-! ### (b) Instance, negative: the deadlock the rules exclude -/

/-- Two transactions in the classic lock-order inversion. -/
inductive Txn2 where
  | u1 | u2
  deriving DecidableEq

open Txn2

abbrev ts2 : Txn2 → Nat
  | .u1 => 10
  | .u2 => 20

/-- `u1` holds item `1`, `u2` holds item `2`. -/
abbrev holder2 : Nat → Option Txn2
  | 1 => some u1
  | 2 => some u2
  | _ => none

/-- Each transaction is blocked on the item the other holds — a lock manager with no timestamp
    discipline would leave both waiting. -/
abbrev request2 : Txn2 → Option Nat
  | .u1 => some 2
  | .u2 => some 1

def st2 : LockState Txn2 := { holder := holder2, request := request2 }

/-- **A genuine 2-cycle: this state is deadlocked.** -/
theorem st2_not_acyclic : ¬ Acyclic st2 := by
  intro hacyc
  exact hacyc u1 (TC.trans (TC.base (show WaitsFor st2 u1 u2 from ⟨2, rfl, rfl⟩))
                           (TC.base (show WaitsFor st2 u2 u1 from ⟨1, rfl, rfl⟩)))

/-- **Why it cannot arise under wait-die**: the edge `u2 → u1` has the YOUNGER transaction
    waiting, so wait-die would have aborted (`died`) `u2` instead of letting it wait. -/
theorem st2_not_waitDie : ¬ WaitDie ts2 st2 := by
  intro hwd
  have h : ts2 u2 < ts2 u1 := hwd u2 u1 ⟨1, rfl, rfl⟩
  exact absurd h (by decide)

/-- **Why it cannot arise under wound-wait either**: the edge `u1 → u2` has the OLDER
    transaction waiting, so wound-wait would have wounded `u2` rather than let `u1` wait. -/
theorem st2_not_woundWait : ¬ WoundWait ts2 st2 := by
  intro hww
  have h : ts2 u2 < ts2 u1 := hww u1 u2 ⟨2, rfl, rfl⟩
  exact absurd h (by decide)

/-- The counterexample packaged: a real circular wait, excluded by both timestamp rules — which
    is exactly the general contrapositive, exhibited on a concrete state. -/
theorem deadlock_requires_violating_both :
    ¬ Acyclic st2 ∧ ¬ WaitDie ts2 st2 ∧ ¬ WoundWait ts2 st2 :=
  ⟨st2_not_acyclic, st2_not_waitDie, st2_not_woundWait⟩

end AutoproverCorpus.WaitDieDeadlockFree
