/-
  AutoproverCorpus.Order.Pigeonhole

  Pigeonhole principles for lists: a list of mapped values longer than the target's size cannot
  be duplicate-free; the distinct-pair form additionally requires the source list itself to be
  duplicate-free.

  Attribution: Classical (Dirichlet).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Distributed.QuorumIntersection

namespace AutoproverCorpus.Pigeonhole

/-! ### The counting lemma: a `Nodup` list of `Fin n` values has length ≤ n -/

theorem nodup_fin_length_le {n : Nat} (l : List (Fin n)) (h : l.Nodup) :
    l.length ≤ n := by
  have hsub : l ⊆ List.finRange n := by
    intro x _
    exact List.mem_finRange x
  have hle := AutoproverCorpus.QuorumIntersection.length_le_of_subset_of_nodup h hsub
  simpa [List.length_finRange] using hle

/-! ### The `Nodup`-flavored corollary — unconditionally true, exactly as specified -/

/-- If a list has more entries than there are buckets, its image under any `f : α → Fin n`
    cannot be `Nodup` — some collision is forced. Unconditional: no hypothesis on `l`
    itself is needed, since this is purely a statement about the structure of `l.map f`. -/
theorem pigeonhole_not_nodup {α : Type} {n : Nat} (l : List α) (f : α → Fin n)
    (h : l.length > n) : ¬ (l.map f).Nodup := by
  intro hnodup
  have hlen : (l.map f).length ≤ n := nodup_fin_length_le (l.map f) hnodup
  rw [List.length_map] at hlen
  omega

/-! ### Helper: injective-on-`l` (by value) plus `l.Nodup` gives `l.map f` `Nodup` -/

theorem map_nodup_of_injOn {α : Type} {n : Nat} (f : α → Fin n) :
    ∀ (l : List α), l.Nodup → (∀ x ∈ l, ∀ y ∈ l, x ≠ y → f x ≠ f y) → (l.map f).Nodup
  | [], _, _ => by simp
  | a :: t, hnodup, hinj => by
      rw [List.nodup_cons] at hnodup
      obtain ⟨hat, htnodup⟩ := hnodup
      have hinj' : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → f x ≠ f y :=
        fun x hx y hy hxy => hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy
      have htmap : (t.map f).Nodup := map_nodup_of_injOn f t htnodup hinj'
      have hanotin : f a ∉ t.map f := by
        intro hmem
        obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hmem
        have hax : a ≠ x := by
          intro h; subst h; exact hat hx
        exact (hinj a List.mem_cons_self x (List.mem_cons_of_mem a hx) hax) hfx.symm
      rw [List.map_cons, List.nodup_cons]
      exact ⟨hanotin, htmap⟩

/-! ### The main theorem: an explicit colliding pair (with `l.Nodup` added — see header) -/

theorem pigeonhole {α : Type} (l : List α) (n : Nat) (f : α → Fin n)
    (hnodup : l.Nodup) (h : l.length > n) :
    ∃ x y, x ∈ l ∧ y ∈ l ∧ x ≠ y ∧ f x = f y := by
  apply Classical.byContradiction
  intro hno
  have hinj : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → f x ≠ f y := by
    intro x hx y hy hxy hfxy
    exact hno ⟨x, y, hx, hy, hxy, hfxy⟩
  exact pigeonhole_not_nodup l f h (map_nodup_of_injOn f l hnodup hinj)

/-! ### Instances: concrete instances checked by `decide` -/

/-- A concrete 3-entry `Nodup` list of buckets `Fin 3`. -/
def sampleList : List (Fin 3) := [0, 1, 2]

/-- A concrete bucket assignment into only 2 buckets — fewer buckets than entries, so a
    collision is forced. -/
def sampleF : Fin 3 → Fin 2 := fun x => ⟨x.val % 2, by omega⟩

example : sampleList.Nodup := by decide
example : sampleList.length > 2 := by decide

/-- The main theorem applied concretely: `sampleList` has 3 distinct entries into 2
    buckets, so `pigeonhole` produces a genuine colliding pair. -/
example : ∃ x y, x ∈ sampleList ∧ y ∈ sampleList ∧ x ≠ y ∧ sampleF x = sampleF y :=
  pigeonhole sampleList 2 sampleF (by decide) (by decide)

/-- The forced collision is witnessed concretely: `0` and `2` both land in bucket `0`. -/
example : sampleF (0 : Fin 3) = sampleF (2 : Fin 3) := by decide
example : (0 : Fin 3) ≠ (2 : Fin 3) := by decide

/-- The `Nodup`-flavored corollary, concretely: `sampleList.map sampleF` cannot be
    `Nodup` (it is `[0, 1, 0]`, which repeats). -/
example : ¬ (sampleList.map sampleF).Nodup := by decide

end AutoproverCorpus.Pigeonhole
