/-
  AutoproverCorpus.Concurrency.TwoPhaseLocking

  Two-phase locking implies conflict-serializability: a 2PL-compliant schedule has an acyclic
  precedence graph (hence a topological order), via a lock-point argument.

  Attribution: Classical (Eswaran, Gray, Lorie and Traiger, 1976).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Concurrency.ConflictSerializability

namespace AutoproverCorpus.TwoPhaseLocking

open AutoproverCorpus.ConflictSerializability

/-! ### The lock-point device -/

/-- A faithful two-phase-locking account of a schedule `sch`: acquire/release ticks per
    `(transaction, resource)`, a per-transaction lock point, and the three defining conditions
    (op-under-hold well-formedness, lock-manager mutual exclusion, and the two-phase discipline
    itself) — see the header for exactly what each postulates versus derives. -/
structure LockSchedule (sch : Schedule) where
  /-- The tick at which `T` acquires the lock on `R` (irrelevant if `T` never touches `R`). -/
  acquireTime : TxId → ResId → Nat
  /-- The tick at which `T` releases the lock on `R` (irrelevant if `T` never touches `R`). -/
  releaseTime : TxId → ResId → Nat
  /-- `T`'s lock point: after all of `T`'s acquires, before all of `T`'s releases. -/
  lp : TxId → Nat
  /-- Well-formedness: every op in `sch` runs strictly between its transaction's acquire and
      release of the op's own resource. -/
  holds_at_op : ∀ i (hi : i < sch.length),
    acquireTime (sch[i]'hi).tx (sch[i]'hi).res ≤ i ∧
    i < releaseTime (sch[i]'hi).tx (sch[i]'hi).res
  /-- Lock-manager legality: an earlier op that conflicts with a later op forces the earlier
      transaction's release (of their shared resource) no later than the later transaction's
      acquire of it. POSTULATED — see header. -/
  mutex : ∀ i j (hi : i < sch.length) (hj : j < sch.length), i < j →
    Conflicts (sch[i]'hi) (sch[j]'hj) →
    releaseTime (sch[i]'hi).tx (sch[i]'hi).res ≤ acquireTime (sch[j]'hj).tx (sch[j]'hj).res
  /-- THE TWO-PHASE DISCIPLINE: for every resource, `T`'s acquire is at or before its lock point,
      and `T`'s release is strictly after it — growing phase then shrinking phase, pivoting at
      `lp T`. -/
  twoPhase : ∀ T R, acquireTime T R ≤ lp T ∧ lp T < releaseTime T R

/-! ### The substantive 2PL lemma: lock-point monotonicity along `PrecEdge` -/

/-- **The substantive 2PL lemma (Eswaran et al.).** A conflict edge `PrecEdge sch a b` forces
    `a`'s lock point strictly before `b`'s. Derived from `mutex` + `twoPhase` (see header for the
    three-step chain); `holds_at_op` is not needed in this particular derivation (it is exercised
    instead by the instance below). -/
theorem twoPL_lp_mono {sch : Schedule} (L : LockSchedule sch) {a b : TxId}
    (hab : PrecEdge sch a b) : L.lp a < L.lp b := by
  obtain ⟨i, j, hi, hj, hij, hai, hbj, hconf⟩ := hab
  have hmutex := L.mutex i j hi hj hij hconf
  rw [hai, hbj] at hmutex
  have h1 := (L.twoPhase a (sch[i]'hi).res).2
  have h2 := (L.twoPhase b (sch[j]'hj).res).1
  omega

theorem twoPL_acyclic {sch : Schedule} (L : LockSchedule sch) : Acyclic sch := by
  intro n hn
  exact Nat.lt_irrefl (L.lp n)
    (reach_rank_lt (rk := L.lp) (fun a b hab => twoPL_lp_mono L hab) hn)

theorem twoPL_hasTopoOrder {sch : Schedule} (L : LockSchedule sch) : HasTopoOrder sch :=
  hasTopoOrder_of_acyclic (twoPL_acyclic L)

theorem cyclicSchedule_no_lockSchedule (L : LockSchedule cyclicSchedule) : False := by
  have h12 := twoPL_lp_mono L cyclicSchedule_edge_12
  have h21 := twoPL_lp_mono L cyclicSchedule_edge_21
  omega

/-- The classic cyclic schedule has no 2PL-compliant lock schedule at all. -/
theorem cyclicSchedule_not_twoPL : ¬ Nonempty (LockSchedule cyclicSchedule) :=
  fun ⟨L⟩ => cyclicSchedule_no_lockSchedule L

theorem cyclicSchedule_no_lockSchedule_via_acyclic (L : LockSchedule cyclicSchedule) : False :=
  cyclicSchedule_not_acyclic (twoPL_acyclic L)

/-- Acquire ticks for `schedule2`: `t1` acquires both its locks up front (a valid, conservative
    special case of 2PL); `t2` acquires `a` right when it needs it (tick 1) and `b` right when it
    needs it (tick 3). -/
def acquireTime2 : TxId → ResId → Nat
  | .t1, .a => 0
  | .t1, .b => 0
  | .t2, .a => 1
  | .t2, .b => 3

/-- Release ticks for `schedule2`: `t1` releases `a` right after using it (tick 1, exactly when
    `t2` acquires it) and `b` right after using it (tick 3, exactly when `t2` acquires it); `t2`'s
    releases are unconstrained by any later conflict, set past the schedule's end. -/
def releaseTime2 : TxId → ResId → Nat
  | .t1, .a => 1
  | .t1, .b => 3
  | .t2, .a => 4
  | .t2, .b => 5

/-- Lock points: `t1`'s pivot is tick `0` (all its acquires are at `0`, its first release is at
    `1`); `t2`'s pivot is tick `3` (its acquires are at `1` and `3`, its first release is at
    `4`). -/
def lp2 : TxId → Nat
  | .t1 => 0
  | .t2 => 3

theorem schedule2_holds_at_op : ∀ i (hi : i < schedule2.length),
    acquireTime2 (schedule2[i]'hi).tx (schedule2[i]'hi).res ≤ i ∧
    i < releaseTime2 (schedule2[i]'hi).tx (schedule2[i]'hi).res := by
  intro i hi
  have hi4 : i < 4 := hi
  have hiv : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hiv with rfl | rfl | rfl | rfl <;> decide +revert

theorem schedule2_mutex : ∀ i j (hi : i < schedule2.length) (hj : j < schedule2.length),
    i < j → Conflicts (schedule2[i]'hi) (schedule2[j]'hj) →
    releaseTime2 (schedule2[i]'hi).tx (schedule2[i]'hi).res ≤
      acquireTime2 (schedule2[j]'hj).tx (schedule2[j]'hj).res := by
  intro i j hi hj hij hconf
  have hi4 : i < 4 := hi
  have hj4 : j < 4 := hj
  have hiv : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hjv : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hiv with rfl | rfl | rfl | rfl <;> rcases hjv with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd hij (by decide)
      | exact absurd hconf (by decide +revert)
      | decide +revert

theorem schedule2_twoPhase : ∀ T R, acquireTime2 T R ≤ lp2 T ∧ lp2 T < releaseTime2 T R := by
  intro T R
  cases T <;> cases R <;> decide

/-- **A genuine 2PL-compliant lock schedule for `schedule2`** — not merely numbers satisfying
    `mutex`/`twoPhase` in isolation, but (via `holds_at_op`) actually consistent with `schedule2`'s
    own op positions. -/
def lockSchedule2 : LockSchedule schedule2 where
  acquireTime := acquireTime2
  releaseTime := releaseTime2
  lp := lp2
  holds_at_op := schedule2_holds_at_op
  mutex := schedule2_mutex
  twoPhase := schedule2_twoPhase

/-- `schedule2` is 2PL-compliant, hence its precedence graph is acyclic. -/
theorem schedule2_twoPL_acyclic : Acyclic schedule2 := twoPL_acyclic lockSchedule2

/-- `schedule2` admits a topological order under 2PL. -/
theorem schedule2_twoPL_hasTopoOrder : HasTopoOrder schedule2 := twoPL_hasTopoOrder lockSchedule2

/-- The topological order witnessed by `lockSchedule2`'s own lock points: `t1 ↦ 0 < 3 ↦ t2`. -/
example : lockSchedule2.lp TxId.t1 < lockSchedule2.lp TxId.t2 := by decide

end AutoproverCorpus.TwoPhaseLocking
