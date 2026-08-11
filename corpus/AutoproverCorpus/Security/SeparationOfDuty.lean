/-
  AutoproverCorpus.Security.SeparationOfDuty

  Separation of duty: if two roles conflict and no actor holds both, no single actor can
  complete a dual-control action.

  Attribution: Classical (Clark and Wilson, 1987).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.SeparationOfDuty

variable {Actor Role : Type}

/-- No actor holds two conflicting roles. -/
def StaticSoD (holds : Actor → Role → Prop) (conflicting : Role → Role → Prop) : Prop :=
  ∀ a r1 r2, conflicting r1 r2 → holds a r1 → ¬ holds a r2

/-- Exercising a role's side of a dual-control action requires holding that role. -/
def CompletesImpliesHolds (completes holds : Actor → Role → Prop) : Prop :=
  ∀ a r, completes a r → holds a r

section
variable {holds completes : Actor → Role → Prop} {conflicting : Role → Role → Prop}

/-! ### (a) Distinct actors -/

/-- **(a)** Under `StaticSoD`, any completed dual-control action has at least two
    DISTINCT actors. -/
theorem two_distinct_actors (hsod : StaticSoD holds conflicting)
    (hcih : CompletesImpliesHolds completes holds)
    (a1 a2 : Actor) (r1 r2 : Role)
    (h1 : completes a1 r1) (h2 : completes a2 r2) (hconf : conflicting r1 r2) :
    a1 ≠ a2 := by
  intro heq
  subst heq
  exact hsod a1 r1 r2 hconf (hcih a1 r1 h1) (hcih a1 r2 h2)

/-! ### (b) Counting form -/

/-- **(b)** The list of actors involved in a completed dual-control action is `Nodup` —
    the two actors are genuinely distinct, not a repeated count. -/
theorem actors_involved_nodup (hsod : StaticSoD holds conflicting)
    (hcih : CompletesImpliesHolds completes holds)
    (a1 a2 : Actor) (r1 r2 : Role)
    (h1 : completes a1 r1) (h2 : completes a2 r2) (hconf : conflicting r1 r2) :
    ([a1, a2] : List Actor).Nodup := by
  have hne : a1 ≠ a2 := two_distinct_actors hsod hcih a1 a2 r1 r2 h1 h2 hconf
  simp [List.nodup_cons, hne]

/-- **(b) The counting form.** The set of actors involved in a completed dual-control
    action is genuinely distinct (`Nodup`) and has size `≥ 2`. -/
theorem actors_involved_size_ge_two (hsod : StaticSoD holds conflicting)
    (hcih : CompletesImpliesHolds completes holds)
    (a1 a2 : Actor) (r1 r2 : Role)
    (h1 : completes a1 r1) (h2 : completes a2 r2) (hconf : conflicting r1 r2) :
    ([a1, a2] : List Actor).Nodup ∧ 2 ≤ ([a1, a2] : List Actor).length :=
  ⟨actors_involved_nodup hsod hcih a1 a2 r1 r2 h1 h2 hconf, by simp⟩

end

/-! ### (c) The violation face — exhibited concretely -/

/-- A two-actor, two-role instance where every actor holds every role (no separation of
    duty at all). -/
def ViolatingHolds : Bool → Bool → Prop := fun _ _ => True

/-- Roles `true` and `false` are declared conflicting. -/
abbrev ViolatingConflicting : Bool → Bool → Prop := fun r1 r2 => r1 ≠ r2

/-- **(c), part 1.** `StaticSoD` genuinely FAILS for `ViolatingHolds`: the actor `true`
    holds both conflicting roles. -/
theorem violating_not_staticSoD :
    ¬ StaticSoD ViolatingHolds ViolatingConflicting := by
  intro hsod
  exact hsod true true false (by decide) trivial trivial

/-- **(c), part 2 — the concrete violation.** A SINGLE actor (`true`) completes BOTH
    sides of the dual-control action for the conflicting roles `true`/`false`. This is
    exactly the scenario `StaticSoD` exists to rule out, and shows the hypothesis is
    non-vacuous: drop it, and one actor alone genuinely can complete a dual-control
    action. -/
theorem single_actor_holds_both_conflicting_roles :
    ∃ a : Bool, ViolatingHolds a true ∧ ViolatingHolds a false ∧
      ViolatingConflicting true false :=
  ⟨true, trivial, trivial, by decide⟩

/-! ### (d) Composition: the n-role generalization -/

/-- A `Pairwise`-not-equal-under-`f` list has a `Nodup` image under `f` — a
    self-contained structural-recursion proof, no `Fin n` codomain restriction. -/
theorem map_nodup_of_pairwise_ne {α β : Type} {f : α → β} :
    ∀ l : List α, l.Pairwise (fun x y => f x ≠ f y) → (l.map f).Nodup
  | [], _ => by simp
  | a :: t, hpw => by
      rw [List.pairwise_cons] at hpw
      obtain ⟨hallne, htpw⟩ := hpw
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, map_nodup_of_pairwise_ne t htpw⟩
      intro hmem
      obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hmem
      exact hallne x hx hfx.symm

/-- **(d) The n-role generalization.** Given a `List Role` that is pairwise-conflicting
    and an `assign : Role → Actor` picking the completing actor for each role in the
    list, the number of DISTINCT actors involved equals the number of roles — in
    particular, `StaticSoD` over a set of pairwise-conflicting roles forces at least as
    many distinct actors as roles. -/
theorem nrole_distinct_actors {holds completes : Actor → Role → Prop}
    {conflicting : Role → Role → Prop}
    (hsod : StaticSoD holds conflicting) (hcih : CompletesImpliesHolds completes holds)
    (assign : Role → Actor) (hassign : ∀ r, completes (assign r) r)
    (roles : List Role) (hpw : roles.Pairwise conflicting) :
    (roles.map assign).Nodup ∧ (roles.map assign).length = roles.length := by
  have key : ∀ {r1 r2 : Role}, conflicting r1 r2 → assign r1 ≠ assign r2 := by
    intro r1 r2 hconf heq
    have h1 : holds (assign r1) r1 := hcih _ _ (hassign r1)
    have h2 : holds (assign r2) r2 := hcih _ _ (hassign r2)
    rw [heq] at h1
    exact hsod (assign r2) r1 r2 hconf h1 h2
  exact ⟨map_nodup_of_pairwise_ne roles (hpw.imp key), List.length_map assign⟩

/-! ### (e) Instance -/

/-- Actor `a` holds role `r` exactly when `a = r` (`Actor := Role := Fin 2`: actor `0`
    holds role `0`, actor `1` holds role `1`, and no actor holds both). -/
abbrev concreteHolds : Fin 2 → Fin 2 → Prop := fun a r => a = r

/-- Roles are conflicting exactly when distinct. -/
abbrev concreteConflicting : Fin 2 → Fin 2 → Prop := fun r1 r2 => r1 ≠ r2

/-- Completing a role's side of the action requires (and here, exactly coincides with)
    holding it. -/
abbrev concreteCompletes : Fin 2 → Fin 2 → Prop := concreteHolds

/-- The concrete instance genuinely satisfies `StaticSoD` — PROVED, not assumed, by a
    two-line equality chase. -/
theorem concreteStaticSoD : StaticSoD concreteHolds concreteConflicting := by
  intro a r1 r2 hconf h1 h2
  exact hconf (h1.symm.trans h2)

theorem concreteCompletesImpliesHolds :
    CompletesImpliesHolds concreteCompletes concreteHolds := fun _ _ h => h

/-- **(e) Instance, (a) applied concretely.** Actors `0` and `1` each complete one
    side of a dual-control action over the conflicting roles `0`/`1`, and are indeed
    distinct. -/
theorem concrete_two_distinct : (0 : Fin 2) ≠ (1 : Fin 2) :=
  two_distinct_actors concreteStaticSoD concreteCompletesImpliesHolds 0 1 0 1
    (by decide) (by decide) (by decide)

/-- **(e) Instance, (d) applied concretely.** Over the pairwise-conflicting role list
    `[0, 1]` with `assign := id`, the two distinct actors `0` and `1` are both involved. -/
theorem concrete_nrole :
    (([(0 : Fin 2), 1].map id) : List (Fin 2)).Nodup ∧
      (([(0 : Fin 2), 1].map id) : List (Fin 2)).length = 2 :=
  nrole_distinct_actors concreteStaticSoD concreteCompletesImpliesHolds id
    (fun r => show concreteCompletes r r from rfl) [0, 1]
    (by
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_singleton _ _⟩
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      decide)

end AutoproverCorpus.SeparationOfDuty
