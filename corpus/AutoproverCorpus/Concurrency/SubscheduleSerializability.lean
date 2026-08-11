/-
  AutoproverCorpus.Concurrency.SubscheduleSerializability

  Sub-schedule closure of conflict-serializability: removing operations (or a whole transaction)
  from a conflict-serializable schedule keeps it conflict-serializable - precedence edges of a
  sub-schedule are a subset, so reachability shrinks and acyclicity is preserved. One direction
  only: the converse (upward closure) is refuted with a witness.

  Attribution: Classical closure property of conflict-serializability.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Concurrency.ConflictSerializability
import AutoproverCorpus.Order.TransitiveReduction

namespace AutoproverCorpus.SubscheduleSerializability

open AutoproverCorpus.ConflictSerializability
open AutoproverCorpus.TransitiveReduction (tc_mono)

-- `<+` (`List.Sublist`) is `scoped` to the `List` namespace (core:
-- `Init/Data/List/Basic.lean`); no file in this repo has opened it yet. `open scoped List`
-- brings the notation into scope without importing all of `List`'s plain names.
open scoped List

/-! ### Two generic list lemmas: indices ↔ a 2-element `<+`-sublist -/

/-- Two indices `i < j` into a list `l` witness the 2-element sublist
    `[l[i], l[j]] <+ l` — "`l[i]` occurs before `l[j]` in `l`". Proved by structural
    induction on `l`. -/
theorem pairSublist_of_lt {α : Type} {l : List α} :
    ∀ {i j : Nat} (hi : i < l.length) (hj : j < l.length), i < j →
      [l[i]'hi, l[j]'hj] <+ l := by
  induction l with
  | nil =>
    intro i j hi hj hij
    simp only [List.length_nil] at hi
    omega
  | cons a t ih =>
    intro i j hi hj hij
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => simp
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have hi' : i < t.length := by simpa using hi
        have hj' : j < t.length := by simpa using hj
        have hij' : i < j := by omega
        have hres := (ih hi' hj' hij').cons a
        simpa using hres

/-- The converse: a 2-element sublist witness `[o1, o2] <+ l` yields indices `i < j` with
    `l[i] = o1`, `l[j] = o2`. Proved by structural induction on `l`, via
    `List.sublist_cons_iff` (peel the head, or find `o1` at the head) and
    `List.getElem_of_mem` (an index witness for `o2`'s membership). -/
theorem pairSublist_to_indices {α : Type} :
    ∀ {l : List α} {o1 o2 : α}, [o1, o2] <+ l →
      ∃ i j, ∃ (hi : i < l.length) (hj : j < l.length),
        i < j ∧ l[i]'hi = o1 ∧ l[j]'hj = o2 := by
  intro l
  induction l with
  | nil =>
    intro o1 o2 h
    exact absurd (List.eq_nil_of_sublist_nil h) (List.cons_ne_nil o1 [o2])
  | cons a t ih =>
    intro o1 o2 h
    rcases List.sublist_cons_iff.mp h with h' | ⟨r, hreq, hrsub⟩
    · obtain ⟨i, j, hi, hj, hij, hie, hje⟩ := ih h'
      refine ⟨i + 1, j + 1,
        by simp only [List.length_cons]; omega,
        by simp only [List.length_cons]; omega,
        by omega, ?_, ?_⟩
      · simpa using hie
      · simpa using hje
    · injection hreq with ha hr
      have hrsub' : ([o2] : List α) <+ t := by rw [hr]; exact hrsub
      have hmem : o2 ∈ t := List.singleton_sublist.mp hrsub'
      obtain ⟨j0, hj0, hj0eq⟩ := List.getElem_of_mem hmem
      refine ⟨0, j0 + 1,
        by simp only [List.length_cons]; omega,
        by simp only [List.length_cons]; omega,
        by omega, ?_, ?_⟩
      · simpa using ha.symm
      · simpa using hj0eq

/-! ### The edge-subset bridge -/

/-- **THE BRIDGE.** A precedence edge is exactly a witnessing pair of ops forming a
    2-element `<+`-sublist of the schedule (plus their tx/conflict data). Unlike
    `PrecEdge`'s own index form, this form composes under `Sublist.trans`. -/
theorem precEdge_iff_pairSublist {sch : Schedule} {a b : TxId} :
    PrecEdge sch a b ↔
      ∃ o1 o2 : Op, [o1, o2] <+ sch ∧ o1.tx = a ∧ o2.tx = b ∧ Conflicts o1 o2 := by
  constructor
  · rintro ⟨i, j, hi, hj, hij, ha, hb, hconf⟩
    exact ⟨sch[i]'hi, sch[j]'hj, pairSublist_of_lt hi hj hij, ha, hb, hconf⟩
  · rintro ⟨o1, o2, hsub, ha, hb, hconf⟩
    obtain ⟨i, j, hi, hj, hij, hie, hje⟩ := pairSublist_to_indices hsub
    refine ⟨i, j, hi, hj, hij, ?_, ?_, ?_⟩
    · rw [hie, ha]
    · rw [hje, hb]
    · rw [hie, hje]; exact hconf

/-- **PrecEdge of a sub-schedule implies PrecEdge of the full schedule** — the precedence
    graph of `sub` is a subgraph of `sch`'s. Via the bridge: pull the pair-sublist witness
    out of `sub`, compose with `sub <+ sch` by `Sublist.trans`, re-package. -/
theorem precEdge_sublist_subset {sub sch : Schedule} (hsubl : sub <+ sch) {a b : TxId}
    (h : PrecEdge sub a b) : PrecEdge sch a b := by
  obtain ⟨o1, o2, hpair, ha, hb, hconf⟩ := precEdge_iff_pairSublist.mp h
  exact precEdge_iff_pairSublist.mpr ⟨o1, o2, hpair.trans hsubl, ha, hb, hconf⟩

/-! ### Reach shrinks, acyclicity is preserved -/

theorem reach_sublist_subset {sub sch : Schedule} (hsubl : sub <+ sch) {a b : TxId}
    (h : Reach sub a b) : Reach sch a b :=
  tc_mono (fun _ _ hxy => precEdge_sublist_subset hsubl hxy) h

/-- **THE HEADLINE, acyclicity form.** A self-loop in `sub`'s precedence graph would give
    one in `sch`'s (via `reach_sublist_subset`), contradicting `sch`'s acyclicity — so a
    sub-schedule of an acyclic schedule is itself acyclic. -/
theorem acyclic_sublist {sub sch : Schedule} (hsubl : sub <+ sch) (hacyc : Acyclic sch) :
    Acyclic sub := fun n hn => hacyc n (reach_sublist_subset hsubl hn)

theorem subschedule_hasTopoOrder {sub sch : Schedule} (hsubl : sub <+ sch)
    (h : HasTopoOrder sch) : HasTopoOrder sub := by
  have hacycSch : Acyclic sch := hasTopoOrder_iff_acyclic.mp h
  have hacycSub : Acyclic sub := acyclic_sublist hsubl hacycSch
  exact hasTopoOrder_iff_acyclic.mpr hacycSub

/-- **"...or a whole transaction."** Removing every op of a transaction `t` from `sch` is
    `sch.filter (fun o => o.tx ≠ t)`, a sublist by core's `List.filter_sublist` — instantiate
    the headline directly. -/
theorem remove_transaction_hasTopoOrder {sch : Schedule} (t : TxId) (h : HasTopoOrder sch) :
    HasTopoOrder (sch.filter (fun o => decide (o.tx ≠ t))) :=
  subschedule_hasTopoOrder List.filter_sublist h

/-! ### Instance, positive — a proper sub-schedule of `schedule2` -/

theorem schedule2_tail_hasTopoOrder : HasTopoOrder schedule2.tail :=
  subschedule_hasTopoOrder (List.tail_sublist schedule2) schedule2_hasTopoOrder

/-- The "remove a whole transaction" corollary, concretely: dropping every `t1`-op from
    `schedule2` keeps it serializable. -/
theorem schedule2_drop_t1_hasTopoOrder :
    HasTopoOrder (schedule2.filter (fun o => decide (o.tx ≠ TxId.t1))) :=
  remove_transaction_hasTopoOrder TxId.t1 schedule2_hasTopoOrder

/-! ### Counterexample separating the hypotheses — closure runs downward only, not upward -/

def cyclicPrefix : Schedule :=
  [⟨TxId.t1, ResId.a, OpKind.write⟩, ⟨TxId.t2, ResId.a, OpKind.read⟩]

/-- `cyclicPrefix` is a (literal-prefix) sublist of `cyclicSchedule`. -/
theorem cyclicPrefix_sublist : cyclicPrefix <+ cyclicSchedule :=
  List.sublist_append_left cyclicPrefix [⟨TxId.t1, ResId.a, OpKind.write⟩]

/-- No `t2 → t1` edge in `cyclicPrefix` (only positions `0, 1` exist: position `0` is `t1`,
    position `1` is `t2`). -/
theorem cyclicPrefix_no_reverse : ¬ PrecEdge cyclicPrefix TxId.t2 TxId.t1 := by
  rintro ⟨i, j, hi, hj, hij, ha, hb, hconf⟩
  have hi2 : i < 2 := hi
  have hj2 : j < 2 := hj
  have hiv : i = 0 ∨ i = 1 := by omega
  have hjv : j = 0 ∨ j = 1 := by omega
  rcases hiv with rfl | rfl <;> rcases hjv with rfl | rfl <;>
    first
      | exact absurd hij (by decide +revert)
      | exact absurd ha (by decide +revert)
      | exact absurd hb (by decide +revert)
      | exact absurd hconf (by decide +revert)

theorem cyclicPrefix_hasTopoOrder : HasTopoOrder cyclicPrefix := by
  refine ⟨rk2, ?_⟩
  intro x y hxy
  cases x <;> cases y
  · exact absurd rfl hxy.tx_ne
  · exact (by decide : rk2 TxId.t1 < rk2 TxId.t2)
  · exact absurd hxy cyclicPrefix_no_reverse
  · exact absurd rfl hxy.tx_ne

/-- **The separating fact, packaged.** A proper sub-schedule of a non-serializable schedule
    can be serializable — closure runs downward only, never upward: `subschedule_hasTopoOrder`
    is not, and must not be read as, an `↔`. -/
theorem closure_is_one_way :
    cyclicPrefix <+ cyclicSchedule ∧ HasTopoOrder cyclicPrefix ∧
      ¬ HasTopoOrder cyclicSchedule :=
  ⟨cyclicPrefix_sublist, cyclicPrefix_hasTopoOrder, cyclicSchedule_no_topoOrder⟩

end AutoproverCorpus.SubscheduleSerializability
