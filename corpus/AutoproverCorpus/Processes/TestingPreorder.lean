/-
  AutoproverCorpus.Processes.TestingPreorder

  The De Nicola-Hennessy MAY-testing preorder is a preorder: reflexive and transitive, by
  test-set containment. `passes : Proc → Test → Prop` is an arbitrary (uninterpreted) relation
  here — no labelled transition system, observer composition, computations, or success states
  are formalized; the result holds of ANY pass relation over ANY `Proc`/`Test` types, so it does
  not by itself carry DNH's testing machinery.

  Attribution: Classical (De Nicola and Hennessy, 1984).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.TestingPreorder

variable {Proc Test : Type}

/-- The MAY-TESTING preorder: `Q` passes every test `P` passes. -/
def MayLe (passes : Proc → Test → Prop) (P Q : Proc) : Prop :=
  ∀ t, passes P t → passes Q t

variable {passes : Proc → Test → Prop}

/-! ### (a) `MayLe` is a preorder -/

theorem mayLe_refl (P : Proc) : MayLe passes P P :=
  fun _ h => h

theorem mayLe_trans {P Q R : Proc}
    (hPQ : MayLe passes P Q) (hQR : MayLe passes Q R) : MayLe passes P R :=
  fun t hPt => hQR t (hPQ t hPt)

/-! ### (c) The induced equivalence -/

/-- `MayEquiv P Q` — `P` and `Q` are may-testing EQUIVALENT: each passes every test the
    other passes (testing equivalence, the symmetrization of `MayLe`). -/
def MayEquiv (passes : Proc → Test → Prop) (P Q : Proc) : Prop :=
  MayLe passes P Q ∧ MayLe passes Q P

theorem mayEquiv_equivalence : Equivalence (MayEquiv (passes := passes)) :=
  ⟨fun P => ⟨mayLe_refl P, mayLe_refl P⟩,
   fun h => ⟨h.2, h.1⟩,
   fun hPQ hQR => ⟨mayLe_trans hPQ.1 hQR.1, mayLe_trans hQR.2 hPQ.2⟩⟩

/-! ### (b), (d) Instances: a concrete finite process/test setup -/

section Instances

/-- Three concrete processes: `P` and `Q` are testing-indistinguishable from each other;
    `R` is strictly better than both (passes everything they pass, plus more). -/
inductive Proc3 where
  | P | Q | R
deriving DecidableEq

/-- Two concrete tests. -/
inductive Test2 where
  | T1 | T2
deriving DecidableEq

/-- Concrete pass relation: `P` and `Q` both pass exactly `T1`; `R` passes both `T1` and
    `T2`. -/
abbrev passes3 : Proc3 → Test2 → Prop
  | .P, .T1 => True
  | .P, .T2 => False
  | .Q, .T1 => True
  | .Q, .T2 => False
  | .R, .T1 => True
  | .R, .T2 => True

/-- `P` and `Q` are distinct processes. -/
example : Proc3.P ≠ Proc3.Q := by decide

/-- `P` and `Q` have IDENTICAL test outcomes on every test. -/
theorem mayLe_PQ : MayLe passes3 Proc3.P Proc3.Q := by
  intro t _
  cases t <;> simp_all [passes3]

theorem mayLe_QP : MayLe passes3 Proc3.Q Proc3.P := by
  intro t _
  cases t <;> simp_all [passes3]

/-- **(b)** `MayLe` is NOT antisymmetric in general: `P` and `Q` satisfy `MayLe` both
    ways yet are distinct processes — testing equivalence genuinely identifies distinct
    processes, so `MayLe` is a preorder that is not a partial order. -/
theorem mayLe_not_antisymm :
    ∃ p q : Proc3, MayLe passes3 p q ∧ MayLe passes3 q p ∧ p ≠ q :=
  ⟨.P, .Q, mayLe_PQ, mayLe_QP, by decide⟩

/-- `R` passes every test `P` passes (`T1`), so `R` is at least as good as `P`. -/
theorem mayLe_PR : MayLe passes3 Proc3.P Proc3.R := by
  intro t _
  cases t <;> simp_all [passes3]

/-- `R` passes `T2`, which `P` does not — so `R` is NOT may-tested-below `P`: `MayLe`
    would require `P` to also pass every test `R` passes, and it does not. -/
theorem not_mayLe_RP : ¬ MayLe passes3 Proc3.R Proc3.P := by
  intro h
  have := h .T2 (by decide : passes3 Proc3.R Test2.T2)
  exact absurd this (by decide)

/-- **(d)** Instance: a strictly-better process. `R` may-refines `P`
    (`MayLe P R`) but not conversely (`¬ MayLe R P`) — `MayLe` is a genuine preorder with
    strict instances, not a degenerate always-equal relation. -/
example : MayLe passes3 Proc3.P Proc3.R ∧ ¬ MayLe passes3 Proc3.R Proc3.P :=
  ⟨mayLe_PR, not_mayLe_RP⟩

end Instances

end AutoproverCorpus.TestingPreorder
