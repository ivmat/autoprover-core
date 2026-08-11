/-
  AutoproverCorpus.Order.TransitiveClosure

  The transitive closure is the least transitive relation containing a relation: it contains the
  relation, is transitive, and is minimal among such relations.

  Attribution: Classical (standard order/relation theory).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.TransitiveClosure

variable {α : Type} (r : α → α → Prop)

/-- The transitive closure of `r`: the least relation containing `r` and closed under
    composition. `base` gives containment; `trans` gives closure under composition
    (transitivity), by construction. -/
inductive TC : α → α → Prop where
  | base {a b : α} : r a b → TC a b
  | trans {a b c : α} : TC a b → TC b c → TC a c

variable {r}

/-- (a) `TC r` contains `r`: every `r`-edge is a `TC r`-edge. -/
theorem tc_contains {a b : α} (h : r a b) : TC r a b :=
  TC.base h

/-- (b) `TC r` is transitive, by construction. -/
theorem tc_transitive {a b c : α} (hab : TC r a b) (hbc : TC r b c) : TC r a c :=
  TC.trans hab hbc

/-- (c) LEAST: any transitive relation `s` that contains `r` also contains `TC r` — so
    `TC r` is the *least* transitive relation containing `r`, not merely *a* transitive
    relation containing it. Proved by induction on the `TC` derivation. -/
theorem tc_least {s : α → α → Prop} (hsub : ∀ a b, r a b → s a b)
    (htrans : ∀ a b c, s a b → s b c → s a c) {a b : α} (h : TC r a b) : s a b := by
  induction h with
  | base hr => exact hsub _ _ hr
  | trans _ _ ihab ihbc => exact htrans _ _ _ ihab ihbc

/-- (d) Idempotence corollary: closing `TC r` again yields nothing new — `TC (TC r)` and
    `TC r` agree exactly. The forward direction is `tc_least` applied with `s := TC r`
    (using `tc_contains`/`tc_transitive` to discharge its hypotheses); the backward
    direction is `tc_contains` for the relation `TC r` itself. -/
theorem tc_idempotent {a b : α} : TC (TC r) a b ↔ TC r a b := by
  constructor
  · intro h
    induction h with
    | base hr => exact hr
    | trans _ _ ihab ihbc => exact tc_transitive ihab ihbc
  · intro h
    exact TC.base h

section Instances

/-- Concrete base relation on `Fin 3`, as a `Bool`-valued step function: `0 ↦ 1`, `1 ↦ 2`
    only (no direct `0 ↦ 2` edge). `abbrev` so `decide` can unfold it (predicates used
    under `decide` must be reducible). -/
abbrev stepRel : Fin 3 → Fin 3 → Bool
  | 0, 1 => true
  | 1, 2 => true
  | _, _ => false

/-- The base relation as a `Prop`, decidable automatically via `DecidableEq Bool` since it
    is stated as a `Bool` equality. -/
abbrev step (a b : Fin 3) : Prop := stepRel a b = true

/-- (e1) `0` and `2` are NOT directly related by the base relation `step`. -/
theorem step_no_direct_edge : ¬ step (0 : Fin 3) (2 : Fin 3) := by decide

/-- (e2) `0` and `2` ARE related by the transitive closure `TC step`, via the two base
    edges `0 ↦ 1` and `1 ↦ 2`. This exhibits `TC` strictly extending `step`: a pair in
    `TC step` that is not a `step`-edge. -/
theorem tc_strictly_extends : TC step (0 : Fin 3) (2 : Fin 3) :=
  TC.trans (TC.base (show step (0 : Fin 3) (1 : Fin 3) by decide))
           (TC.base (show step (1 : Fin 3) (2 : Fin 3) by decide))

end Instances

end AutoproverCorpus.TransitiveClosure
