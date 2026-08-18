/-
  AutoproverCorpus.Probability.PairwiseNotMutualIndependence

  Pairwise independence does not imply mutual (joint) independence: Bernstein's three-event
  counterexample, closed by `decide`. Over two fair coin flips, take `A` = "first flip is
  heads", `B` = "second flip is heads", `C` = "the two flips agree". Every PAIR of these events
  is independent, yet the triple is not: `P(A ∩ B ∩ C) = 1/4`, while `P(A)P(B)P(C) = 1/8`.

  All probabilities are stated in exact COUNTING form over a uniform finite sample space: for a
  sample space of size `n`, the two-event independence condition `P(A ∩ B) = P(A)·P(B)` is
  multiplied through by `n^2` to become `n·|A ∩ B| = |A|·|B|`, and the three-event condition
  by `n^3` to become `n^2·|A ∩ B ∩ C| = |A|·|B|·|C|`. Over a uniform space these are equivalent
  to the usual ratio statements and are exact `Nat` identities, which keeps the whole module
  inside `decide` (see the corpus's note on `Rat` literal arithmetic being irreducible).

  The module also exhibits a POSITIVE control — three genuinely mutually independent events
  over three fair coin flips — so that the mutual-independence condition being violated above
  is a fact about Bernstein's triple, not an unsatisfiable definition.

  Attribution: Classical (S. N. Bernstein's example, *Theory of Probability*, 1946; a standard
  textbook counterexample).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

namespace AutoproverCorpus.PairwiseNotMutualIndependence

/-! ### Events and the counting form of independence -/

/-- The number of sample points of `l` at which the event `e` occurs. Over a uniform space,
    `P(e) = card l e / l.length`. -/
def card {α : Type} (l : List α) (e : α → Bool) : Nat := l.countP e

/-- Intersection of two events. -/
abbrev inter {α : Type} (a b : α → Bool) : α → Bool := fun o => a o && b o

/-- **Two-event independence, counting form.** `P(A ∩ B) = P(A)·P(B)` over a uniform space of
    size `n = l.length`, multiplied through by `n^2`. -/
def Indep2 {α : Type} (l : List α) (a b : α → Bool) : Prop :=
  l.length * card l (inter a b) = card l a * card l b

/-- **Three-event joint condition, counting form.** `P(A ∩ B ∩ C) = P(A)·P(B)·P(C)` over a
    uniform space of size `n = l.length`, multiplied through by `n^3`. -/
def Joint3 {α : Type} (l : List α) (a b c : α → Bool) : Prop :=
  l.length * l.length * card l (inter (inter a b) c) = card l a * card l b * card l c

/-- **Mutual independence of three events** is the conjunction of all three pairwise conditions
    AND the triple condition — the triple condition alone does not follow from the pairwise
    ones, which is exactly what this module shows. -/
def MutuallyIndep3 {α : Type} (l : List α) (a b c : α → Bool) : Prop :=
  Indep2 l a b ∧ Indep2 l a c ∧ Indep2 l b c ∧ Joint3 l a b c

/-! ### Bernstein's counterexample: two fair coin flips -/

/-- The four equally likely outcomes of two fair coin flips. -/
inductive Flip2 where
  | hh | ht | th | tt
  deriving DecidableEq

open Flip2

/-- The uniform sample space: four outcomes, each of probability `1/4`. -/
abbrev omega2 : List Flip2 := [hh, ht, th, tt]

/-- `A`: the first flip is heads. -/
abbrev evA : Flip2 → Bool
  | .hh => true
  | .ht => true
  | _ => false

/-- `B`: the second flip is heads. -/
abbrev evB : Flip2 → Bool
  | .hh => true
  | .th => true
  | _ => false

/-- `C`: the two flips agree (both heads or both tails). -/
abbrev evC : Flip2 → Bool
  | .hh => true
  | .tt => true
  | _ => false

/-- Each event has probability `1/2`: two of the four outcomes. -/
theorem marginals : card omega2 evA = 2 ∧ card omega2 evB = 2 ∧ card omega2 evC = 2 := by
  decide

/-- Each pairwise intersection is the single outcome `hh` — probability `1/4`. -/
theorem pair_intersections :
    card omega2 (inter evA evB) = 1 ∧ card omega2 (inter evA evC) = 1 ∧
      card omega2 (inter evB evC) = 1 := by
  decide

/-- **(1) All three pairs are independent.** `4 · 1 = 2 · 2` in each case: `P(A ∩ B) = 1/4 =
    P(A)·P(B)`, and likewise for the other two pairs. -/
theorem pairwise_independent :
    Indep2 omega2 evA evB ∧ Indep2 omega2 evA evC ∧ Indep2 omega2 evB evC := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold Indep2 card inter; decide)

/-- The triple intersection is again the single outcome `hh`: knowing the first two flips are
    heads already forces them to agree, so `A ∩ B ⊆ C` and `P(A ∩ B ∩ C) = 1/4`, not `1/8`. -/
theorem triple_intersection : card omega2 (inter (inter evA evB) evC) = 1 := by decide

/-- **(2) The triple condition FAILS.** `16 · 1 = 16 ≠ 8 = 2 · 2 · 2`: in ratio form
    `P(A ∩ B ∩ C) = 1/4` while `P(A)·P(B)·P(C) = 1/8`. -/
theorem not_joint3 : ¬ Joint3 omega2 evA evB evC := by
  unfold Joint3 card inter
  decide

/-- **Bernstein's counterexample, packaged.** The three events are pairwise independent yet not
    mutually independent — so "pairwise independent" does NOT imply "mutually independent", and
    a proof that only checks pairs has not established joint independence. -/
theorem pairwise_not_mutual :
    (Indep2 omega2 evA evB ∧ Indep2 omega2 evA evC ∧ Indep2 omega2 evB evC) ∧
      ¬ MutuallyIndep3 omega2 evA evB evC :=
  ⟨pairwise_independent, fun h => not_joint3 h.2.2.2⟩

/-! ### Positive control: three genuinely mutually independent events -/

/-- Three fair coin flips, as the eight bit patterns `0..7`; flip `i` is heads iff bit `i` of
    the outcome is set. -/
abbrev omega3 : List (Fin 8) := List.finRange 8

/-- Flip `0` is heads. -/
abbrev bit0 (o : Fin 8) : Bool := o.val % 2 == 1

/-- Flip `1` is heads. -/
abbrev bit1 (o : Fin 8) : Bool := (o.val / 2) % 2 == 1

/-- Flip `2` is heads. -/
abbrev bit2 (o : Fin 8) : Bool := (o.val / 4) % 2 == 1

/-- **The definition is satisfiable.** Three independent fair coin flips ARE mutually
    independent in the sense above: every pair satisfies `8 · 2 = 4 · 4` and the triple
    satisfies `64 · 1 = 4 · 4 · 4`. This is the non-vacuity witness for `MutuallyIndep3` —
    Bernstein's triple fails a condition that other triples genuinely meet. -/
theorem three_flips_mutually_independent : MutuallyIndep3 omega3 bit0 bit1 bit2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Indep2 card inter; decide
  · unfold Indep2 card inter; decide
  · unfold Indep2 card inter; decide
  · unfold Joint3 card inter; decide

end AutoproverCorpus.PairwiseNotMutualIndependence
