/-
  AutoproverCorpus.Concurrency.ConflictSerializability

  Conflict-serializability iff the precedence (conflict) graph is acyclic, with a cyclic non-
  serializable witness schedule.

  Attribution: Classical (Eswaran, Gray, Lorie and Traiger, 1976; Bernstein et al.).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Order.TransitiveClosure

namespace AutoproverCorpus.ConflictSerializability

open AutoproverCorpus.TransitiveClosure (TC tc_least)

/-! ### Model -/

inductive OpKind
  | read | write
  deriving DecidableEq, Repr

inductive TxId
  | t1 | t2
  deriving DecidableEq, Repr

inductive ResId
  | a | b
  deriving DecidableEq, Repr

/-- A single schedule operation: which transaction, which resource, read or write. -/
structure Op where
  tx   : TxId
  res  : ResId
  kind : OpKind
  deriving Repr

/-- A schedule is a finite list of operations, in execution order. -/
abbrev Schedule := List Op

/-- Two ops conflict: same resource, different transactions, at least one a write.
    `abbrev` so `decide`'s instance search can see through it. -/
abbrev Conflicts (o1 o2 : Op) : Prop :=
  o1.res = o2.res ∧ o1.tx ≠ o2.tx ∧ (o1.kind = OpKind.write ∨ o2.kind = OpKind.write)

/-- The precedence (conflict) graph edge: some op of `a` conflicts with, and precedes, some op
    of `b` in `sch`. -/
def PrecEdge (sch : Schedule) (a b : TxId) : Prop :=
  ∃ i j, ∃ (hi : i < sch.length) (hj : j < sch.length),
    i < j ∧ (sch[i]'hi).tx = a ∧ (sch[j]'hj).tx = b ∧ Conflicts (sch[i]'hi) (sch[j]'hj)

/-- A precedence edge is always between DISTINCT transactions (`Conflicts` requires `tx ≠`). -/
theorem PrecEdge.tx_ne {sch : Schedule} {a b : TxId} (h : PrecEdge sch a b) : a ≠ b := by
  obtain ⟨_, _, _, _, _, ha, hb, hconf⟩ := h
  intro heq
  exact hconf.2.1 (ha.trans (heq.trans hb.symm))

abbrev Reach (sch : Schedule) : TxId → TxId → Prop := TC (PrecEdge sch)

def Acyclic (sch : Schedule) : Prop := ∀ n, ¬ Reach sch n n

/-! ### A topological order of the transactions -/

/-- A topological rank of the transactions, strictly respecting every precedence edge. The
    standard graph-theoretic characterization of conflict-serializability — see the header for
    exactly what this does and does not additionally claim. -/
def HasTopoOrder (sch : Schedule) : Prop :=
  ∃ rk : TxId → Nat, ∀ a b, PrecEdge sch a b → rk a < rk b

/-! ### Direction 1 (easy): a topological rank forces acyclicity -/

theorem reach_rank_lt {sch : Schedule} {rk : TxId → Nat}
    (hrank : ∀ a b, PrecEdge sch a b → rk a < rk b) {a b : TxId} (h : Reach sch a b) :
    rk a < rk b :=
  tc_least (fun x y hxy => hrank x y hxy) (fun _ _ _ hxy hyz => Nat.lt_trans hxy hyz) h

theorem acyclic_of_topoOrder {sch : Schedule} (h : HasTopoOrder sch) : Acyclic sch := by
  obtain ⟨rk, hrank⟩ := h
  intro n hn
  exact Nat.lt_irrefl (rk n) (reach_rank_lt hrank hn)

/-! ### A reusable list lemma: strict `countP` monotonicity -/

/-- If `q` holds whenever `p` does (pointwise over `l`), and some element of `l` witnesses
    `q` without `p`, then strictly more of `l` satisfies `q` than `p`. Core's `List.countP_mono
    _left` gives the non-strict `≤`; this is the strict refinement, not present in core. -/
theorem countP_strict_mono {α} {l : List α} {p q : α → Bool}
    (himp : ∀ x ∈ l, p x → q x) {x0 : α} (hx0 : x0 ∈ l) (hq0 : q x0 = true)
    (hp0 : p x0 = false) : l.countP p < l.countP q := by
  induction l with
  | nil => cases hx0
  | cons a t ih =>
    have hple : t.countP p ≤ t.countP q :=
      List.countP_mono_left (fun x hx => himp x (List.mem_cons_of_mem a hx))
    rcases List.mem_cons.mp hx0 with rfl | hx0t
    · rw [List.countP_cons_of_neg (show ¬ p x0 by simp [hp0]),
          List.countP_cons_of_pos (show q x0 by simp [hq0])]
      omega
    · have himp' : ∀ x ∈ t, p x → q x := fun x hx => himp x (List.mem_cons_of_mem a hx)
      have ihh := ih himp' hx0t
      by_cases hpa : p a
      · have hqa : q a := himp a List.mem_cons_self hpa
        rw [List.countP_cons_of_pos hpa, List.countP_cons_of_pos hqa]
        omega
      · by_cases hqa : q a
        · rw [List.countP_cons_of_neg hpa, List.countP_cons_of_pos hqa]
          omega
        · rw [List.countP_cons_of_neg hpa, List.countP_cons_of_neg hqa]
          omega

/-! ### Direction 2 (hard): acyclicity forces a topological rank -/

open Classical in
/-- The number of tx-occurrences in `sch` from which `v` is precedence-reachable. Used purely
    as a strictly-increasing rank witness; `noncomputable` since `Reach` is not core-decidable
    (`Classical.propDecidable`, as already used for `Classical.byContradiction` elsewhere in
    this repo) — nothing below evaluates it, only reasons about it. -/
noncomputable def reachCount (sch : Schedule) (v : TxId) : Nat :=
  (sch.map Op.tx).countP (fun u => decide (Reach sch u v))

theorem reachCount_strict_mono {sch : Schedule} {a b : TxId} (hab : PrecEdge sch a b)
    (hacyc : Acyclic sch) : reachCount sch a < reachCount sch b := by
  classical
  unfold reachCount
  refine countP_strict_mono
    (himp := fun u _ hu => decide_eq_true (TC.trans (of_decide_eq_true hu) (TC.base hab)))
    (x0 := a)
    (hx0 := ?_)
    (hq0 := decide_eq_true (TC.base hab))
    (hp0 := decide_eq_false (hacyc a))
  obtain ⟨i, _, hi, _, _, ha, _, _⟩ := hab
  have hmemS : sch[i]'hi ∈ sch := List.getElem_mem hi
  have hmemL : (sch[i]'hi).tx ∈ sch.map Op.tx := List.mem_map_of_mem hmemS
  rwa [ha] at hmemL

/-- **The hard direction.** An acyclic precedence graph admits a topological rank — the
    predecessor-count `reachCount` witnesses it. -/
theorem hasTopoOrder_of_acyclic {sch : Schedule} (hacyc : Acyclic sch) : HasTopoOrder sch :=
  ⟨reachCount sch, fun _ _ hab => reachCount_strict_mono hab hacyc⟩

/-! ### The serializability theorem -/

theorem acyclic_iff_hasTopoOrder {sch : Schedule} : Acyclic sch ↔ HasTopoOrder sch :=
  ⟨hasTopoOrder_of_acyclic, acyclic_of_topoOrder⟩

/-- **The serializability theorem, as proved here** (see header DEVIATION note for exactly
    what `HasTopoOrder` does and does not claim): a schedule's precedence graph is
    acyclic iff it admits a topological order of its transactions. -/
theorem hasTopoOrder_iff_acyclic {sch : Schedule} :
    HasTopoOrder sch ↔ Acyclic sch :=
  acyclic_iff_hasTopoOrder.symm

/-! ### Instance, negative — the classic two-transaction cycle -/

/-- The classic non-serializable schedule: `t1` reads `A`, `t2` reads `A`, `t1` writes `A`.
    `R2(A)` conflicts with the later `W1(A)` (`t2 → t1`), and `R1(A)` conflicts with the later
    `W1(A)` too, but the essential pair is the cycle-closing one below. -/
def cyclicSchedule : Schedule :=
  [⟨TxId.t1, ResId.a, OpKind.write⟩, ⟨TxId.t2, ResId.a, OpKind.read⟩,
   ⟨TxId.t1, ResId.a, OpKind.write⟩]

/-- `W1(A)` (position 0) precedes `R2(A)` (position 1): conflict, edge `t1 → t2`. -/
theorem cyclicSchedule_edge_12 : PrecEdge cyclicSchedule TxId.t1 TxId.t2 :=
  ⟨0, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `R2(A)` (position 1) precedes the second `W1(A)` (position 2): conflict, edge `t2 → t1`. -/
theorem cyclicSchedule_edge_21 : PrecEdge cyclicSchedule TxId.t2 TxId.t1 :=
  ⟨1, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **`cyclicSchedule` is not `Acyclic`** — `t1` reaches itself via the 2-cycle. -/
theorem cyclicSchedule_not_acyclic : ¬ Acyclic cyclicSchedule := fun hacyc =>
  hacyc TxId.t1 (TC.trans (TC.base cyclicSchedule_edge_12) (TC.base cyclicSchedule_edge_21))

/-- The classic cyclic schedule is not conflict-serializable. -/
theorem cyclicSchedule_no_topoOrder : ¬ HasTopoOrder cyclicSchedule := fun h =>
  cyclicSchedule_not_acyclic (hasTopoOrder_iff_acyclic.mp h)

/-! ### Instance, positive — an interleaved but acyclic schedule -/

/-- Interleaved (`t1,t2,t1,t2`) over two resources; both conflicts point the same way
    (`t1 → t2`), so this is acyclic despite not being literally serial as written. -/
def schedule2 : Schedule :=
  [⟨TxId.t1, ResId.a, OpKind.write⟩, ⟨TxId.t2, ResId.a, OpKind.read⟩,
   ⟨TxId.t1, ResId.b, OpKind.write⟩, ⟨TxId.t2, ResId.b, OpKind.read⟩]

/-- The witness rank: `t1 ↦ 0`, `t2 ↦ 1`. -/
def rk2 : TxId → Nat
  | .t1 => 0
  | .t2 => 1

/-- No edge of `schedule2` runs `t2 → t1` (checked over every position pair). -/
theorem sch2_no_reverse : ¬ PrecEdge schedule2 TxId.t2 TxId.t1 := by
  rintro ⟨i, j, hi, hj, hij, ha, hb, hconf⟩
  have hi4 : i < 4 := hi
  have hj4 : j < 4 := hj
  have hiv : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hjv : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hiv with rfl | rfl | rfl | rfl <;> rcases hjv with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd hij (by decide +revert)
      | exact absurd ha (by decide +revert)
      | exact absurd hb (by decide +revert)
      | exact absurd hconf (by decide +revert)

/-- **`schedule2` admits a topological order** — the concrete rank `rk2`. -/
theorem schedule2_topoOrder : HasTopoOrder schedule2 := by
  refine ⟨rk2, ?_⟩
  intro a b hab
  cases a <;> cases b
  · exact absurd rfl hab.tx_ne
  · exact (by decide : rk2 TxId.t1 < rk2 TxId.t2)
  · exact absurd hab sch2_no_reverse
  · exact absurd rfl hab.tx_ne

/-- The interleaved-but-consistent schedule is conflict-serializable. -/
theorem schedule2_hasTopoOrder : HasTopoOrder schedule2 := schedule2_topoOrder

/-- Bonus corollary via the main theorem: `schedule2` is consequently `Acyclic` too. -/
theorem schedule2_acyclic : Acyclic schedule2 := acyclic_of_topoOrder schedule2_topoOrder

end AutoproverCorpus.ConflictSerializability
