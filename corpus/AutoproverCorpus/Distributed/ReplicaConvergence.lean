/-
  AutoproverCorpus.Distributed.ReplicaConvergence

  Replica convergence for state-based replication: a commutative, associative, idempotent merge
  makes replicas that have seen the same set of updates agree, regardless of delivery order.

  Attribution: Classical (join-semilattice replication; Shapiro, Preguica, Baquero and Zawirski,
  2011).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.ReplicaConvergence

variable {S : Type}

/-! ### The three algebraic hypotheses (never `axiom`s — always explicit per-theorem
    arguments), and the absorbing fold. -/

/-- `merge` is commutative. -/
def Comm (merge : S → S → S) : Prop := ∀ a b, merge a b = merge b a

/-- `merge` is associative. -/
def Assoc (merge : S → S → S) : Prop := ∀ a b c, merge (merge a b) c = merge a (merge b c)

/-- `merge` is idempotent. -/
def Idem (merge : S → S → S) : Prop := ∀ a, merge a a = a

/-- `fold merge s l` absorbs the list `l` of received update-states into starting state
    `s`, one at a time, LEFT to right. -/
def fold (merge : S → S → S) (s : S) (l : List S) : S := l.foldl merge s

@[simp] theorem fold_nil (merge : S → S → S) (s : S) : fold merge s [] = s := rfl

@[simp] theorem fold_cons (merge : S → S → S) (s x : S) (l : List S) :
    fold merge s (x :: l) = fold merge (merge s x) l := rfl

/-- `fold` over an append: absorb `l1` first, then continue absorbing `l2` from the
    resulting state — a direct corollary of `List.foldl_append`. -/
theorem fold_append (merge : S → S → S) (s : S) (l1 l2 : List S) :
    fold merge s (l1 ++ l2) = fold merge (fold merge s l1) l2 := by
  unfold fold
  rw [List.foldl_append]

section
variable (merge : S → S → S)

/-! ### (a) Order independence -/

/-- `Comm` + `Assoc` give the "left-commutation" fact `List.Perm.foldl_eq'` needs as its
    per-pair commuting hypothesis: `merge (merge c a) b = merge (merge c b) a`. -/
theorem merge_left_comm (hassoc : Assoc merge) (hcomm : Comm merge) (c a b : S) :
    merge (merge c a) b = merge (merge c b) a := by
  rw [hassoc, hcomm a b, ← hassoc]

theorem fold_perm (hcomm : Comm merge) (hassoc : Assoc merge)
    (s : S) (l1 l2 : List S) (hp : l1.Perm l2) :
    fold merge s l1 = fold merge s l2 :=
  hp.foldl_eq' (fun x _ y _ z => merge_left_comm merge hassoc hcomm z x y) s

/-! ### (b) Multiplicity independence -/

/-- `Assoc` + `Idem` collapse one redundant absorb: re-merging the same state does
    nothing. -/
theorem merge_dup (hassoc : Assoc merge) (hidem : Idem merge) (s x : S) :
    merge (merge s x) x = merge s x := by
  rw [hassoc, hidem]

/-- **(b) Multiplicity independence, adjacent form.** A duplicate received update right
    next to itself does not change the resulting state. -/
theorem fold_dup_adjacent (hassoc : Assoc merge) (hidem : Idem merge)
    (s x : S) (l : List S) :
    fold merge s (x :: x :: l) = fold merge s (x :: l) := by
  simp only [fold_cons]
  rw [merge_dup merge hassoc hidem]

/-- **(b) Multiplicity independence, general form.** The adjacent-duplicate collapse
    works at ANY position in the list, not just the head — a direct consequence of
    `fold_append` plus `fold_dup_adjacent` applied from the new starting state
    `fold merge s l1`. -/
theorem fold_dup_anywhere (hassoc : Assoc merge) (hidem : Idem merge)
    (s x : S) (l1 l2 : List S) :
    fold merge s (l1 ++ x :: x :: l2) = fold merge s (l1 ++ x :: l2) := by
  rw [fold_append merge s l1 (x :: x :: l2), fold_append merge s l1 (x :: l2),
    fold_dup_adjacent merge hassoc hidem]

end

/-! ### (c) The main result — convergence -/

inductive SameUpdates : List S → List S → Prop
  | perm {l1 l2 : List S} (h : l1.Perm l2) : SameUpdates l1 l2
  | dup {l1 l2 : List S} (x : S) : SameUpdates (l1 ++ x :: x :: l2) (l1 ++ x :: l2)
  | symm {l1 l2 : List S} (h : SameUpdates l1 l2) : SameUpdates l2 l1
  | trans {l1 l2 l3 : List S} (h1 : SameUpdates l1 l2) (h2 : SameUpdates l2 l3) :
      SameUpdates l1 l3

/-- **(c) The main result.** Two replicas whose received-update histories are `SameUpdates`-
    related — i.e. one is reachable from the other by reordering and/or duplicate
    collapse, in either direction, chained — fold to the same state from the same
    starting state. This is strong eventual convergence for a state-based CRDT: the
    structural reason a replicated trust ledger cannot diverge. -/
theorem convergence (hcomm : Comm merge) (hassoc : Assoc merge) (hidem : Idem merge)
    (s : S) {l1 l2 : List S} (h : SameUpdates l1 l2) :
    fold merge s l1 = fold merge s l2 := by
  induction h with
  | perm hp => exact fold_perm merge hcomm hassoc s _ _ hp
  | dup x => exact fold_dup_anywhere merge hassoc hidem s x _ _
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### (d) Instances: a concrete join-semilattice, `Nat` under `max` -/

/-- The concrete merge operation: `Nat.max`. -/
def natMerge : Nat → Nat → Nat := Nat.max

/-- `Nat.max` is commutative — cited from core Lean, not reproved. -/
theorem natMerge_comm : Comm natMerge := Nat.max_comm

/-- `Nat.max` is associative — cited from core Lean, not reproved. -/
theorem natMerge_assoc : Assoc natMerge := Nat.max_assoc

/-- `Nat.max` is idempotent — cited from core Lean, not reproved. -/
theorem natMerge_idem : Idem natMerge := Nat.max_self

/-- Instance. Two different receive orders — `[3, 5, 2]` (no repeats) and
    `[2, 3, 5, 5, 2]` (reordered, with duplicates, same underlying set `{2, 3, 5}`) —
    converge to the same state `5` from genesis `0`, checked by `decide`. -/
theorem two_orders_converge :
    fold natMerge 0 [3, 5, 2] = fold natMerge 0 [2, 3, 5, 5, 2] := by decide

/-- The two concrete lists are genuinely different receive orders (not the same list),
    so `two_orders_converge` is not a vacuous `rfl`. -/
example : ([3, 5, 2] : List Nat) ≠ [2, 3, 5, 5, 2] := by decide

end AutoproverCorpus.ReplicaConvergence
