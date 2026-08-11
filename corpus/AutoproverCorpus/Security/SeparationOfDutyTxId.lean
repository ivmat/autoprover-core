/-
  AutoproverCorpus.Security.SeparationOfDutyTxId

  Separation of duty with transaction identity: the two approvals of a dual-control action on
  the SAME transaction must come from two distinct actors.

  Attribution: Classical (Clark and Wilson, 1987); transaction-identified form.

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.SeparationOfDutyTxId

variable {Actor TxId : Type}

/-! ### The model: an approval log with transaction identity -/

/-- Actor `a` approved transaction `t` — membership in the approval log. `abbrev` (not
    `def`) so `decide` can unfold it in the concrete examples below (per this repo's
    toolchain notes: `decide` needs its predicates reducible). -/
abbrev ApprovedOn (log : List (Actor × TxId)) (a : Actor) (t : TxId) : Prop :=
  (a, t) ∈ log

def DualControlled (log : List (Actor × TxId)) (t : TxId) : Prop :=
  ∃ a1 a2, a1 ≠ a2 ∧ ApprovedOn log a1 t ∧ ApprovedOn log a2 t

def TwoActorsInvolvedSomewhere (log : List (Actor × TxId)) : Prop :=
  ∃ a1 a2, a1 ≠ a2 ∧ (∃ t1, ApprovedOn log a1 t1) ∧ (∃ t2, ApprovedOn log a2 t2)

/-! ### (a) The decidable checker, sound + complete -/

section
variable [DecidableEq Actor] [DecidableEq TxId]

/-- The actors who approved transaction `t`, read off the log (duplicates allowed — we
    only ever ask whether two DISTINCT elements exist, so no dedup is needed). -/
def approversOf (log : List (Actor × TxId)) (t : TxId) : List Actor :=
  (log.filter (fun p => decide (p.2 = t))).map Prod.fst

/-- **The decidable checker.** Does the approvers list for `t` contain two distinct
    actors? -/
def checkDualControl (log : List (Actor × TxId)) (t : TxId) : Bool :=
  (approversOf log t).any (fun a1 => (approversOf log t).any (fun a2 => decide (a1 ≠ a2)))

omit [DecidableEq Actor] in
theorem mem_approversOf {log : List (Actor × TxId)} {t : TxId} {a : Actor} :
    a ∈ approversOf log t ↔ ApprovedOn log a t := by
  unfold approversOf ApprovedOn
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [List.mem_filter] at hp
    obtain ⟨hmem, hdec⟩ := hp
    have ht : p.2 = t := of_decide_eq_true hdec
    rw [← ht]
    exact hmem
  · intro h
    exact ⟨(a, t), List.mem_filter.mpr ⟨h, decide_eq_true rfl⟩, rfl⟩

/-- **(a) Checker soundness + completeness.** `checkDualControl` decides exactly the
    per-transaction property `DualControlled`, for every log and every transaction — no
    extra hypothesis needed (see the HYPOTHESIS NOTE above). -/
theorem checkDualControl_iff {log : List (Actor × TxId)} {t : TxId} :
    checkDualControl log t = true ↔ DualControlled log t := by
  unfold checkDualControl DualControlled
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a1, ha1, hany⟩
    rw [List.any_eq_true] at hany
    obtain ⟨a2, ha2, hdec⟩ := hany
    exact ⟨a1, a2, of_decide_eq_true hdec, mem_approversOf.mp ha1, mem_approversOf.mp ha2⟩
  · rintro ⟨a1, a2, hne, h1, h2⟩
    refine ⟨a1, mem_approversOf.mpr h1, ?_⟩
    rw [List.any_eq_true]
    exact ⟨a2, mem_approversOf.mpr h2, decide_eq_true hne⟩

end

/-! ### (b) A genuine positive instance -/

/-- **(b)** A concrete log where two distinct actors (`true`, `false`) both approved the
    SAME transaction (`true`) — the checker correctly ACCEPTS it. -/
theorem concrete_dual_controlled :
    checkDualControl ([(true, true), (false, true)] : List (Bool × Bool)) true = true := by
  decide

/-- **(b)** The same positive instance, as the `Prop`-level property, via (a). -/
theorem concrete_dual_controlled_prop :
    DualControlled ([(true, true), (false, true)] : List (Bool × Bool)) true :=
  checkDualControl_iff.mp concrete_dual_controlled

theorem vacuity_gap :
    ∃ log : List (Bool × Bool),
      TwoActorsInvolvedSomewhere log ∧
        (∀ t : Bool, ¬ DualControlled log t) ∧ (∀ t : Bool, checkDualControl log t = false) := by
  refine ⟨[(true, true), (false, false)],
    ⟨true, false, by decide, ⟨true, by decide⟩, ⟨false, by decide⟩⟩, ?_, ?_⟩
  · intro t hdc
    obtain ⟨a1, a2, hne, h1, h2⟩ := hdc
    unfold ApprovedOn at h1 h2
    cases a1 <;> cases a2 <;> cases t <;>
      first
        | exact absurd rfl hne
        | exact absurd h1 (by decide)
        | exact absurd h2 (by decide)
  · intro t
    cases t <;> decide

/-- **(d) The clean refutation.** It is NOT the case that `TwoActorsInvolvedSomewhere`
    implies `DualControlled` for every log and every transaction — the role/actor-level
    notion is genuinely insufficient to establish the per-transaction property.
    `vacuity_gap`'s witness is the counterexample. -/
theorem lifted_role_level_notion_not_sufficient :
    ¬ ∀ (log : List (Bool × Bool)) (t : Bool), TwoActorsInvolvedSomewhere log → DualControlled log t := by
  intro h
  obtain ⟨log, htwo, hnone, _⟩ := vacuity_gap
  exact hnone true (h log true htwo)

end AutoproverCorpus.SeparationOfDutyTxId
