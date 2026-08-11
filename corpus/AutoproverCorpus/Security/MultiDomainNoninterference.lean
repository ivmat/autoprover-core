/-
  AutoproverCorpus.Security.MultiDomainNoninterference

  Multi-domain noninterference: noninterference over an arbitrary set of security domains with
  an interference relation; per-observer unwinding conditions imply per-observer
  noninterference.

  Attribution: Classical (Goguen and Meseguer, 1982; unwinding in the style of Rushby, 1992).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.MultiDomainNoninterference

def run {I S : Type} (step : S → I → S) (s : S) (is : List I) : S :=
  is.foldl step s

@[simp] theorem run_nil {I S : Type} (step : S → I → S) (s : S) :
    run step s ([] : List I) = s := rfl

@[simp] theorem run_cons {I S : Type} (step : S → I → S) (s : S) (i : I) (is : List I) :
    run step s (i :: is) = run step (step s i) is := rfl

def purgeU {Dom I : Type} (dom : I → Dom) (flowsTo : Dom → Dom → Prop) (u : Dom)
    [DecidablePred fun i => flowsTo (dom i) u] (is : List I) : List I :=
  is.filter (fun i => decide (flowsTo (dom i) u))

def NoninterferenceU {Dom I S O : Type} (dom : I → Dom) (flowsTo : Dom → Dom → Prop) (u : Dom)
    [DecidablePred fun i => flowsTo (dom i) u] (step : S → I → S) (out : Dom → S → O) : Prop :=
  ∀ (s0 : S) (is : List I),
    out u (run step s0 is) = out u (run step s0 (purgeU dom flowsTo u is))

/-- (OC, per-observer) `eqv u`-equivalent states are indistinguishable to `u`. -/
def OutputConsistentU {Dom S O : Type} (u : Dom) (out : Dom → S → O) (eqv : Dom → S → S → Prop) :
    Prop :=
  ∀ s t, eqv u s t → out u s = out u t

/-- (SC, per-observer) an input whose domain flows to `u` preserves `eqv u`-equivalence
    of two runs. -/
def StepConsistentU {Dom I S : Type} (dom : I → Dom) (flowsTo : Dom → Dom → Prop) (u : Dom)
    (step : S → I → S) (eqv : Dom → S → S → Prop) : Prop :=
  ∀ (s t : S) (i : I), eqv u s t → flowsTo (dom i) u → eqv u (step s i) (step t i)

/-- (LR, per-observer) an input whose domain does NOT flow to `u` does not move a state
    out of its own `eqv u`-equivalence class. -/
def LocallyRespectsU {Dom I S : Type} (dom : I → Dom) (flowsTo : Dom → Dom → Prop) (u : Dom)
    (step : S → I → S) (eqv : Dom → S → S → Prop) : Prop :=
  ∀ (s : S) (i : I), ¬ flowsTo (dom i) u → eqv u s (step s i)

theorem unwinding_step_u {Dom I S : Type} (dom : I → Dom) (flowsTo : Dom → Dom → Prop) (u : Dom)
    [DecidablePred fun i => flowsTo (dom i) u] (step : S → I → S) (eqv : Dom → S → S → Prop)
    (heqv : Equivalence (eqv u)) (hSC : StepConsistentU dom flowsTo u step eqv)
    (hLR : LocallyRespectsU dom flowsTo u step eqv) :
    ∀ (is : List I) (s t : S), eqv u s t →
      eqv u (run step s is) (run step t (purgeU dom flowsTo u is)) := by
  intro is
  induction is with
  | nil => intro s t h; simpa [purgeU] using h
  | cons i is' ih =>
    intro s t h
    rcases Classical.em (flowsTo (dom i) u) with hf | hf
    · have hpurge : purgeU dom flowsTo u (i :: is') = i :: purgeU dom flowsTo u is' :=
        List.filter_cons_of_pos (decide_eq_true hf)
      rw [run_cons, hpurge, run_cons]
      exact ih (step s i) (step t i) (hSC s t i h hf)
    · have hpurge : purgeU dom flowsTo u (i :: is') = purgeU dom flowsTo u is' :=
        List.filter_cons_of_neg (by rw [decide_eq_false hf]; decide)
      rw [run_cons, hpurge]
      have h1 : eqv u (step s i) s := heqv.symm (hLR s i hf)
      have h2 : eqv u (step s i) t := heqv.trans h1 h
      exact ih (step s i) t h2

/-- **(a) Per-observer unwinding theorem.** OC(u) + SC(u) + LR(u) for an equivalence
    relation `eqv u` implies noninterference for observer `u`: `u`'s observation is
    invariant to purging the inputs whose domain does not flow to `u`. -/
theorem unwinding_theorem_u {Dom I S O : Type} (dom : I → Dom) (flowsTo : Dom → Dom → Prop)
    (u : Dom) [DecidablePred fun i => flowsTo (dom i) u] (step : S → I → S) (out : Dom → S → O)
    (eqv : Dom → S → S → Prop) (heqv : Equivalence (eqv u)) (hOC : OutputConsistentU u out eqv)
    (hSC : StepConsistentU dom flowsTo u step eqv) (hLR : LocallyRespectsU dom flowsTo u step eqv) :
    NoninterferenceU dom flowsTo u step out := by
  intro s0 is
  exact hOC _ _ (unwinding_step_u dom flowsTo u step eqv heqv hSC hLR is s0 s0 (heqv.refl s0))

/-- The classical two-domain flow relation over `Dom := Bool` (`false ~ Low`,
    `true ~ High`): "Low flows to everything, High flows only to High." `abbrev` (not
    `def`) so typeclass search can see through it to find `DecidableEq Bool`
    automatically — a plain `def` here would need a manual `Decidable` instance, since
    instance synthesis does not unfold plain `def`s. -/
abbrev lowHighFlowsTo (d e : Bool) : Prop := d = false ∨ e = true

theorem purgeU_lowHigh_eq {I : Type} (dom : I → Bool) (is : List I) :
    purgeU dom lowHighFlowsTo false is = is.filter (fun i => !dom i) := by
  unfold purgeU lowHighFlowsTo
  congr 1
  funext i
  simp

theorem two_domain_special_case {I S O : Type} (dom : I → Bool) (step : S → I → S)
    (out : Bool → S → O) (eqv : Bool → S → S → Prop) (heqv : Equivalence (eqv false))
    (hOC : OutputConsistentU false out eqv)
    (hSC : StepConsistentU dom lowHighFlowsTo false step eqv)
    (hLR : LocallyRespectsU dom lowHighFlowsTo false step eqv) :
    ∀ (s0 : S) (is : List I),
      out false (run step s0 is) = out false (run step s0 (is.filter (fun i => !dom i))) := by
  intro s0 is
  have h := unwinding_theorem_u dom lowHighFlowsTo false step out eqv heqv hOC hSC hLR s0 is
  rwa [purgeU_lowHigh_eq] at h

/-! ### (c) A 3-domain machine, satisfying and violating instances -/

/-- Three security domains: `pub` (the fixed observer below) and two mutually-unrelated
    "high" domains `secA`/`secB` — genuinely 3-domain, not a relabelled 2-domain lattice:
    `secA` does not flow to `secB` or vice versa. -/
inductive Dom3
  | pub | secA | secB
  deriving DecidableEq, Repr

/-- `Bool`-valued flow test: `pub` flows to everything; `secA`/`secB` flow only to
    themselves. -/
def dom3FlowsToB : Dom3 → Dom3 → Bool
  | Dom3.pub, _ => true
  | Dom3.secA, Dom3.secA => true
  | Dom3.secB, Dom3.secB => true
  | Dom3.secA, _ => false
  | Dom3.secB, _ => false

/-- `abbrev` (not `def`), for the same reason as `lowHighFlowsTo`: lets typeclass search
    see through to `DecidableEq Bool` for `dom3FlowsToB _ _ = true`. -/
abbrev dom3FlowsTo (d e : Dom3) : Prop := dom3FlowsToB d e = true

/-- The 3-domain machine's input type. -/
inductive Cmd3
  | incPub | incA | incB
  deriving DecidableEq, Repr

/-- Each command's domain. -/
def cmd3Dom : Cmd3 → Dom3
  | Cmd3.incPub => Dom3.pub
  | Cmd3.incA => Dom3.secA
  | Cmd3.incB => Dom3.secB

/-- The shared state: `(pub counter, secA counter, secB counter)`. `pub` only ever
    observes its own counter. -/
structure St3 where
  pubC : Nat
  aC : Nat
  bC : Nat
  deriving DecidableEq, Repr

/-- What `pub` sees of the state. -/
def obs3 (s : St3) : Nat := s.pubC

/-- `pub`-equivalence on states: agreement on the `pub`-visible counter. Reused as the
    (only-ever-queried-at-`Dom3.pub`) per-observer equivalence family. -/
def pubEq (_ : Dom3) (s t : St3) : Prop := s.pubC = t.pubC

theorem pubEq_equivalence : Equivalence (pubEq Dom3.pub) :=
  { refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2 }

/-- Honest machine: each command bumps only the counter matching its own domain. -/
def honestStep3 (s : St3) (i : Cmd3) : St3 :=
  match i with
  | Cmd3.incPub => { s with pubC := s.pubC + 1 }
  | Cmd3.incA => { s with aC := s.aC + 1 }
  | Cmd3.incB => { s with bC := s.bC + 1 }

theorem honest_OC3 : OutputConsistentU Dom3.pub (fun _ => obs3) pubEq :=
  fun _ _ h => h

theorem honest_SC3 : StepConsistentU cmd3Dom dom3FlowsTo Dom3.pub honestStep3 pubEq := by
  intro s t i h hf
  cases i with
  | incPub =>
    simp only [honestStep3, pubEq] at h ⊢
    omega
  | incA => exact absurd hf (by decide)
  | incB => exact absurd hf (by decide)

theorem honest_LR3 : LocallyRespectsU cmd3Dom dom3FlowsTo Dom3.pub honestStep3 pubEq := by
  intro s i hnf
  cases i with
  | incPub => exact absurd (show dom3FlowsTo (cmd3Dom Cmd3.incPub) Dom3.pub by decide) hnf
  | incA => simp [honestStep3, pubEq]
  | incB => simp [honestStep3, pubEq]

/-- The honest 3-domain machine satisfies noninterference for observer `pub`, directly
    via the general unwinding theorem. -/
theorem honest_noninterference3 :
    NoninterferenceU cmd3Dom dom3FlowsTo Dom3.pub honestStep3 (fun _ => obs3) :=
  unwinding_theorem_u cmd3Dom dom3FlowsTo Dom3.pub honestStep3 (fun _ => obs3) pubEq
    pubEq_equivalence honest_OC3 honest_SC3 honest_LR3

/-- Leaky machine: a `secA` input also bumps the `pub`-visible counter — an
    information leak from `secA` to `pub`. -/
def leakyStep3 (s : St3) (i : Cmd3) : St3 :=
  match i with
  | Cmd3.incPub => { s with pubC := s.pubC + 1 }
  | Cmd3.incA => { s with pubC := s.pubC + 1, aC := s.aC + 1 }
  | Cmd3.incB => { s with bC := s.bC + 1 }

/-- Concrete counterexample trace: a single `secA` input from the zero state. Running it
    moves `pub`'s observation from `0` to `1`; purging it (dropping the `secA` input,
    since `secA` does not flow to `pub`) leaves `pub`'s observation at `0`. -/
theorem leaky_witness_diverges3 :
    obs3 (run leakyStep3 (St3.mk 0 0 0) [Cmd3.incA]) ≠
      obs3 (run leakyStep3 (St3.mk 0 0 0) (purgeU cmd3Dom dom3FlowsTo Dom3.pub [Cmd3.incA])) := by
  decide

/-- Instance: the leaky machine violates noninterference for observer `pub` —
    showing that the unwinding theorem's OC/SC/LR hypotheses are satisfiable
    (the leaky machine cannot satisfy LR(pub): a `secA` step changes the `pub`-visible
    component even though `secA` does not flow to `pub`). -/
theorem leaky_not_noninterferent3 :
    ¬ NoninterferenceU cmd3Dom dom3FlowsTo Dom3.pub leakyStep3 (fun _ => obs3) := by
  intro h
  exact leaky_witness_diverges3 (h (St3.mk 0 0 0) [Cmd3.incA])

end AutoproverCorpus.MultiDomainNoninterference
