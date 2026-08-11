/-
  AutoproverCorpus.Order.NewmanLemma

  Newman's lemma: a locally confluent and terminating abstract rewriting system is confluent, by
  well-founded induction.

  Attribution: Classical (Newman, 1942).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.NewmanLemma

variable {α : Type}

/-! ### `RTC`: the reflexive-transitive closure, head-step first -/

inductive RTC (r : α → α → Prop) : α → α → Prop where
  | refl {a : α} : RTC r a a
  | head {a b c : α} : r a b → RTC r b c → RTC r a c

/-- A single `r`-step is an `RTC`-witness. -/
theorem rtc_single {r : α → α → Prop} {a b : α} (h : r a b) : RTC r a b :=
  RTC.head h RTC.refl

/-- `RTC r` is transitive. -/
theorem rtc_trans {r : α → α → Prop} : ∀ {a b c : α}, RTC r a b → RTC r b c → RTC r a c
  | _, _, _, RTC.refl, h => h
  | _, _, _, RTC.head hab hbc, h => RTC.head hab (rtc_trans hbc h)

/-- The case split the whole proof turns on: an `RTC`-witness is either the identity, or
    it takes a genuine first `r`-step. Direct from `RTC`'s own two constructors. -/
theorem rtc_cases {r : α → α → Prop} {a b : α} (h : RTC r a b) :
    a = b ∨ ∃ b1, r a b1 ∧ RTC r b1 b := by
  cases h with
  | refl => exact Or.inl rfl
  | head hab hbc => exact Or.inr ⟨_, hab, hbc⟩

/-- Local (weak) confluence: any two one-step divergences from a common source
    re-converge (via `RTC`, not necessarily in one step each). -/
def LocallyConfluent (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → ∃ d, RTC r b d ∧ RTC r c d

/-- (Global) confluence: any two `RTC`-divergences from a common source re-converge. -/
def Confluent (r : α → α → Prop) : Prop :=
  ∀ a b c, RTC r a b → RTC r a c → ∃ d, RTC r b d ∧ RTC r c d

/-- Termination as well-foundedness of the FLIPPED relation: `Acc (fun x y => r y x) a`
    unwinds to "every one-step `r`-successor of `a` is `Acc`" — Noetherian induction
    "forward" along `r`, which is the direction the proof needs (the induction hypothesis
    is invoked at `r`-successors of the current node). -/
def Terminating (r : α → α → Prop) : Prop :=
  WellFounded (fun x y => r y x)

/-! ### Newman's Lemma -/

/-- **Newman's Lemma (1942).** A terminating, locally confluent relation is confluent.
    By well-founded (Noetherian) induction on the shared source `a`, using `hSN` for
    accessibility. Case split on whether each of the two `RTC`-witnesses out of `a` is the
    identity or takes a first step (`rtc_cases`); in the fully general case (`x → b1 →* b`,
    `x → c1 →* c`), one shot of local confluence at `x` closes the bottom diamond
    (`b1, c1 ↦ d1`), and the induction hypothesis — applicable at `b1` and at `c1`, both
    strictly `r`-smaller than `x` — closes the two side diamonds in turn
    (`b, d1 ↦ e`, then `c, e ↦ f`), glued by `rtc_trans` into the final apex `f`. -/
theorem newman {r : α → α → Prop} (hSN : Terminating r) (hWCR : LocallyConfluent r) :
    Confluent r := by
  intro a
  refine hSN.induction
    (C := fun a => ∀ b c, RTC r a b → RTC r a c → ∃ d, RTC r b d ∧ RTC r c d) a ?_
  intro x ih b c hxb hxc
  rcases rtc_cases hxb with hbeq | ⟨b1, hxb1, hb1b⟩
  · exact ⟨c, hbeq ▸ hxc, RTC.refl⟩
  · rcases rtc_cases hxc with hceq | ⟨c1, hxc1, hc1c⟩
    · exact ⟨b, RTC.refl, hceq ▸ (RTC.head hxb1 hb1b)⟩
    · obtain ⟨d1, hb1d1, hc1d1⟩ := hWCR x b1 c1 hxb1 hxc1
      obtain ⟨e, hbe, hd1e⟩ := ih b1 hxb1 b d1 hb1b hb1d1
      have hc1e : RTC r c1 e := rtc_trans hc1d1 hd1e
      obtain ⟨f, hcf, hef⟩ := ih c1 hxc1 c e hc1c hc1e
      exact ⟨f, rtc_trans hbe hef, hcf⟩

/-! ### Instances: a concrete terminating, locally confluent relation -/

section Instances

/-- `0 → 1`, `0 → 2`, `1 → 2` — a small terminating relation on `Fin 3` where the one
    genuinely branching pair (`1`, `2`, both one-step successors of `0`) re-converges: `1`
    reduces on to `2` in one more step, and `2` needs none. -/
abbrev step : Fin 3 → Fin 3 → Bool
  | 0, 1 => true
  | 0, 2 => true
  | 1, 2 => true
  | _, _ => false

abbrev stepRel (a b : Fin 3) : Prop := step a b = true

/-- `0`'s only `stepRel`-successors are `1` and `2`; each is a genuine `decide`-checked
    finite fact (core Lean's `decidableForallFin` makes `∀ y : Fin 3, …` decidable, but
    `RTC`/existentials are NOT automatically decidable — these destructuring facts stay
    strictly Boolean, no `RTC` inside, which is why `decide` reaches them). -/
theorem stepRel_zero_dest : ∀ y : Fin 3, stepRel 0 y → y = 1 ∨ y = 2 := by decide

/-- `1`'s only `stepRel`-successor is `2`. -/
theorem stepRel_one_dest : ∀ y : Fin 3, stepRel 1 y → y = 2 := by decide

/-- `2` is a sink. -/
theorem stepRel_two_dest : ∀ y : Fin 3, ¬ stepRel 2 y := by decide

/-- **Termination**, by hand-building `Acc` for each of the 3 elements (finite, so this
    is exhaustive) rather than routing through an abstract measure — `Fin 3` is small
    enough that direct construction is both the shortest and the least error-prone route. -/
theorem stepRel_terminating : Terminating stepRel := by
  have hAcc2 : Acc (fun x y : Fin 3 => stepRel y x) 2 :=
    Acc.intro 2 (fun y hy => absurd hy (stepRel_two_dest y))
  have hAcc1 : Acc (fun x y : Fin 3 => stepRel y x) 1 :=
    Acc.intro 1 (fun y hy => (stepRel_one_dest y hy) ▸ hAcc2)
  have hAcc0 : Acc (fun x y : Fin 3 => stepRel y x) 0 :=
    Acc.intro 0 (fun y hy => (stepRel_zero_dest y hy).elim (· ▸ hAcc1) (· ▸ hAcc2))
  refine ⟨fun a => ?_⟩
  match a with
  | 0 => exact hAcc0
  | 1 => exact hAcc1
  | 2 => exact hAcc2

/-- **Local confluence**, by cases on the (finitely many) sources: `0`'s two successors
    `1`/`2` both reach `2` (`1` in one more step, `2` in zero); `1`'s and `2`'s own
    successor sets each have at most one element, so trivially confluent. -/
theorem stepRel_locallyConfluent : LocallyConfluent stepRel := by
  intro a b c hab hac
  match a with
  | 0 =>
    rcases stepRel_zero_dest b hab with rfl | rfl <;>
      rcases stepRel_zero_dest c hac with rfl | rfl
    · exact ⟨1, RTC.refl, RTC.refl⟩
    · exact ⟨2, rtc_single (by decide), RTC.refl⟩
    · exact ⟨2, RTC.refl, rtc_single (by decide)⟩
    · exact ⟨2, RTC.refl, RTC.refl⟩
  | 1 =>
    rw [stepRel_one_dest b hab, stepRel_one_dest c hac]
    exact ⟨2, RTC.refl, RTC.refl⟩
  | 2 => exact absurd hab (stepRel_two_dest b)

/-- The one genuinely branching case, `0 → 1` and `0 → 2`, produces (via `newman`) an
    actual confluence witness. -/
example : ∃ d, RTC stepRel (1 : Fin 3) d ∧ RTC stepRel (2 : Fin 3) d :=
  newman stepRel_terminating stepRel_locallyConfluent 0 1 2 (rtc_single (by decide))
    (rtc_single (by decide))

end Instances

end AutoproverCorpus.NewmanLemma
