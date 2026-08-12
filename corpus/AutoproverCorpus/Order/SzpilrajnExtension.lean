/-
  AutoproverCorpus.Order.SzpilrajnExtension

  The order-extension principle (Szpilrajn's theorem): every strict partial order extends to a
  strict total order. This module proves the two classical finite ingredients of that theorem:

  (1) THE ONE-STEP EXTENSION LEMMA (the inductive core): given a strict partial order `r` and
      two INCOMPARABLE elements `a`, `b`, orienting the pair (adding `a < b`, then closing under
      transitivity) yields a strict relation that is still a strict partial order, still
      contains every `r`-relation, and now relates `a` and `b`.

  (2) EVERY NONEMPTY FINITE strict partial order has a MAXIMAL element (no element above it) —
      the other classical ingredient a full topological-sort-style construction repeatedly
      consumes.

  SCOPE NOTE (read before citing this file as "Szpilrajn's theorem" without qualification):
  assembling (1) and (2) into a fully general, automatic construction of a total order for an
  ARBITRARY finite strict partial order (Szpilrajn's theorem in full) additionally needs a
  carrier-reduction argument (removing a maximal element, recursing on the smaller carrier, and
  re-inserting it on top) that this file does not carry out — that step is real additional
  engineering, not proved here. What IS proved is the one-step extension lemma exactly as
  specified, the finite existence-of-a-maximal-element lemma, and — concretely, by hand — a
  genuine total strict order on a 3-element carrier built by iterating the one-step lemma three
  times from the empty relation, worked out explicitly at the end of the file.

  Attribution: Szpilrajn, 1930 (order-extension principle).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.SzpilrajnExtension

/-- A strict partial order: irreflexive and transitive. -/
structure StrictPartialOrder {α : Type} (r : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬ r a a
  trans  : ∀ a b c, r a b → r b c → r a c

/-- Two elements are incomparable under `r` when neither relates to the other. `abbrev` (not
    `def`), so `decide` can see through it on concrete instances. -/
abbrev Incomparable {α : Type} (r : α → α → Prop) (a b : α) : Prop := ¬ r a b ∧ ¬ r b a

/-! ### (1) The one-step extension lemma -/

/-- Orient the pair `(a, b)`: add `a < b` to `r`, then close under transitivity. The closed
    form `(x = a ∨ r x a) ∧ (y = b ∨ r b y)` says "`x` is `a` or below `a`, and `y` is `b` or
    above `b`" — exactly the pairs that a transitive closure of `r ∪ {(a,b)}` forces, GIVEN
    that `r` is already transitive (so no longer chains are needed). `abbrev` (not `def`), so
    `decide` can see through it on concrete instances (see the header's SCOPE NOTE section for
    the worked example at the end of the file). -/
abbrev orient {α : Type} (r : α → α → Prop) (a b x y : α) : Prop :=
  r x y ∨ ((x = a ∨ r x a) ∧ (y = b ∨ r b y))

/-- `orient r a b` contains every `r`-relation. -/
theorem orient_extends {α : Type} (r : α → α → Prop) (a b : α) {x y : α} (h : r x y) :
    orient r a b x y := Or.inl h

/-- `orient r a b` genuinely relates `a` and `b`. -/
theorem orient_orients {α : Type} (r : α → α → Prop) (a b : α) : orient r a b a b :=
  Or.inr ⟨Or.inl rfl, Or.inl rfl⟩

/-- **The one-step extension lemma.** Orienting an incomparable pair of a strict partial
    order yields a strict partial order again. The proof only actually consumes the
    `¬ r b a` half of `Incomparable` (irreflexivity is what forbids the "wrong-direction"
    cycles), but the pair genuinely being incomparable — not merely `¬ r b a` — is what makes
    "orienting" it a meaningful extension step rather than a no-op or a contradiction. -/
theorem orient_spo {α : Type} {r : α → α → Prop} (hspo : StrictPartialOrder r) {a b : α}
    (hab : a ≠ b) (hinc : Incomparable r a b) : StrictPartialOrder (orient r a b) := by
  have hnba : ¬ r b a := hinc.2
  refine { irrefl := ?_, trans := ?_ }
  · intro x hx
    rcases hx with h | ⟨hxa, hxb⟩
    · exact hspo.irrefl x h
    · rcases hxa with rfl | hxa
      · rcases hxb with heq | hrba
        · exact hab heq
        · exact hnba hrba
      · rcases hxb with heq | hrbx
        · exact hnba (heq ▸ hxa)
        · exact hnba (hspo.trans _ _ _ hrbx hxa)
  · intro x y z hxy hyz
    rcases hxy with hxy | ⟨hxa, hyb⟩
    · rcases hyz with hyz | ⟨hya, hzb⟩
      · exact Or.inl (hspo.trans _ _ _ hxy hyz)
      · have hxa' : x = a ∨ r x a := by
          rcases hya with rfl | hya
          · exact Or.inr hxy
          · exact Or.inr (hspo.trans _ _ _ hxy hya)
        exact Or.inr ⟨hxa', hzb⟩
    · rcases hyz with hyz | ⟨hya, hzb⟩
      · have hzb' : z = b ∨ r b z := by
          rcases hyb with rfl | hyb
          · exact Or.inr hyz
          · exact Or.inr (hspo.trans _ _ _ hyb hyz)
        exact Or.inr ⟨hxa, hzb'⟩
      · exact Or.inr ⟨hxa, hzb⟩

/-! ### (2) Existence of a maximal element in a nonempty finite strict partial order -/

/-- The list-level workhorse: folding `r`'s "who dominates whom" test across a list `l`,
    starting from seed `c0`, produces an element `m` that (a) the seed reaches, `c0 = m ∨ r c0
    m` — proved by chaining `r`'s transitivity along every candidate advance — and (b) is not
    dominated by the seed or by anything in `l`. Proved by induction on `l`; at each step the
    running candidate either advances (if it is `r`-below the next element) or stays, and the
    strengthened "`c0` reaches `m`" fact is exactly what lets the proof rule out the next
    element dominating `m` when the candidate stays put. -/
theorem exists_maximal_of_list {α : Type} {r : α → α → Prop}
    (htrans : ∀ a b c, r a b → r b c → r a c) (hirr : ∀ a, ¬ r a a) (l : List α) (c0 : α) :
    ∃ m, (c0 = m ∨ r c0 m) ∧ ∀ y, (y = c0 ∨ y ∈ l) → ¬ r m y := by
  induction l generalizing c0 with
  | nil =>
    refine ⟨c0, Or.inl rfl, ?_⟩
    intro y hy
    rcases hy with heq | hy
    · subst y
      exact hirr c0
    · cases hy
  | cons x xs ih =>
    by_cases hcx : r c0 x
    · obtain ⟨m, hreach, hmax⟩ := ih x
      refine ⟨m, ?_, ?_⟩
      · rcases hreach with heq | hrxm
        · exact Or.inr (heq ▸ hcx)
        · exact Or.inr (htrans _ _ _ hcx hrxm)
      · intro y hy
        rcases hy with heq | hy
        · subst y
          intro hcontra
          exact (hmax x (Or.inl rfl)) (htrans m c0 x hcontra hcx)
        · rcases List.mem_cons.mp hy with heq | hy
          · subst y
            exact hmax x (Or.inl rfl)
          · exact hmax y (Or.inr hy)
    · obtain ⟨m, hreach, hmax⟩ := ih c0
      refine ⟨m, hreach, ?_⟩
      intro y hy
      rcases hy with heq | hy
      · subst y
        exact hmax c0 (Or.inl rfl)
      · rcases List.mem_cons.mp hy with heq | hy
        · subst y
          intro hcontra
          rcases hreach with heq2 | hrc0m
          · exact hcx (heq2 ▸ hcontra)
          · exact hcx (htrans c0 m x hrc0m hcontra)
        · exact hmax y (Or.inr hy)

/-- **Every nonempty finite strict partial order has a maximal element.** Instantiates the
    list-level lemma at `l := List.finRange n` (every element of `Fin n`, so the seed's own
    membership condition is subsumed) and any witness `x0 : Fin n` establishing nonemptiness. -/
theorem exists_maximal {n : Nat} {r : Fin n → Fin n → Prop} (hspo : StrictPartialOrder r)
    (x0 : Fin n) : ∃ m, ∀ y, ¬ r m y := by
  obtain ⟨m, -, hmax⟩ := exists_maximal_of_list hspo.trans hspo.irrefl (List.finRange n) x0

  exact ⟨m, fun y => hmax y (Or.inr (List.mem_finRange y))⟩

/-- Dual: every nonempty finite strict partial order has a MINIMAL element, by applying
    `exists_maximal` to the flipped relation. -/
theorem exists_minimal {n : Nat} {r : Fin n → Fin n → Prop} (hspo : StrictPartialOrder r)
    (x0 : Fin n) : ∃ m, ∀ y, ¬ r y m := by
  have hflip : StrictPartialOrder (fun x y => r y x) :=
    { irrefl := hspo.irrefl, trans := fun a b c hab hbc => hspo.trans c b a hbc hab }
  obtain ⟨m, hmax⟩ := exists_maximal hflip x0
  exact ⟨m, hmax⟩

/-! ### (3) A worked instance: a genuine total order on `Fin 3`, by iterating (1) three times

    Starting from the empty relation (trivially a strict partial order, with every pair
    incomparable), orienting `(0, 1)`, then `(0, 2)`, then `(1, 2)` in turn resolves all three
    pairs of `Fin 3` — concretely demonstrating the "iterate to a total order" content of
    Szpilrajn's theorem on a specific finite carrier, at the strength this file actually
    reaches (see the SCOPE NOTE above for what is not generalized to arbitrary `n`). -/

/-- Step 0: the empty relation on `Fin 3` — vacuously a strict partial order. -/
abbrev r0 (_ _ : Fin 3) : Prop := False

theorem r0_spo : StrictPartialOrder r0 :=
  { irrefl := fun _ h => h, trans := fun _ _ _ h _ => h }

/-- Step 1: orient `(0, 1)`. -/
abbrev r1 : Fin 3 → Fin 3 → Prop := orient r0 0 1

theorem r1_spo : StrictPartialOrder r1 :=
  orient_spo r0_spo (by decide) (by decide)

/-- Step 2: orient `(0, 2)`. -/
abbrev r2 : Fin 3 → Fin 3 → Prop := orient r1 0 2

theorem r2_spo : StrictPartialOrder r2 :=
  orient_spo r1_spo (by decide) (by decide)

/-- Step 3: orient `(1, 2)`. -/
abbrev r3 : Fin 3 → Fin 3 → Prop := orient r2 1 2

theorem r3_spo : StrictPartialOrder r3 :=
  orient_spo r2_spo (by decide) (by decide)

/-- `r3` is a genuine strict TOTAL order on `Fin 3`: every distinct pair is related one way or
    the other. Unfolding the `r3`/`r2`/`r1`/`r0`/`orient` chain explicitly first (rather than
    leaving it to `decide`'s own instance search) keeps this within reach: three layers of
    nested `Or`/`And` is more than `decide` resolves unaided here. -/
theorem r3_total : ∀ x y : Fin 3, x ≠ y → r3 x y ∨ r3 y x := by
  simp only [r3, r2, r1, r0, orient]
  simp
  decide

/-- `r3` is exactly `0 < 1 < 2`, concretely. -/
example : r3 0 1 ∧ r3 0 2 ∧ r3 1 2 := by
  simp only [r3, r2, r1, r0, orient]
  simp

/-- `r3`'s maximal element is `2`, concretely — and `exists_maximal` (not just `decide`) can
    exhibit a maximal element abstractly, matching this concrete one. -/
example : ¬ r3 2 0 ∧ ¬ r3 2 1 ∧ ¬ r3 2 2 := by
  simp only [r3, r2, r1, r0, orient]
  simp

example : ∃ m : Fin 3, ∀ y, ¬ r3 m y := exists_maximal r3_spo 0

end AutoproverCorpus.SzpilrajnExtension
