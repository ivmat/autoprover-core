/-
  AutoproverCorpus.Order.TransitiveReduction

  Transitive reduction of a finite directed acyclic graph: it exists and is unique.

  Attribution: Classical (Aho, Garey and Ullman, 1972).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Order.TransitiveClosure
import AutoproverCorpus.Distributed.QuorumIntersection

namespace AutoproverCorpus.TransitiveReduction

open AutoproverCorpus.TransitiveClosure (TC tc_least tc_transitive)

variable {α : Type}

/-! ### The construction: `minus` (remove one edge) and `R` (the reduction) -/

/-- `r` with the single edge `(a, b)` removed. -/
def minus (r : α → α → Prop) (a b : α) : α → α → Prop :=
  fun x y => r x y ∧ ¬ (x = a ∧ y = b)

/-- The candidate transitive reduction: keep edge `(a, b)` iff there is no alternative
    path from `a` to `b` avoiding it. -/
def R (E : α → α → Prop) (a b : α) : Prop :=
  E a b ∧ ¬ TC (minus E a b) a b

/-- `R ⊆ E`. -/
theorem R_sub_E {E : α → α → Prop} {a b : α} (h : R E a b) : E a b := h.1

/-! ### General utilities on `TC` (no `E`/`R` specifics) -/

/-- Monotonicity of `TC`: a pointwise-included relation has pointwise-included closure. -/
theorem tc_mono {r s : α → α → Prop} (himp : ∀ a b, r a b → s a b) {a b : α}
    (h : TC r a b) : TC s a b :=
  tc_least (fun a b hab => TC.base (himp a b hab))
    (fun _ _ _ hab hbc => tc_transitive hab hbc) h

/-- Every `TC r a b` derivation has a first hop: an edge `a → c`, followed by either
    landing exactly on `b` or continuing on to `b`. -/
theorem tc_first_step {r : α → α → Prop} :
    ∀ {a b : α}, TC r a b → ∃ c, r a c ∧ (c = b ∨ TC r c b)
  | _, _, TC.base h => ⟨_, h, Or.inl rfl⟩
  | _, _, TC.trans hab hmb => by
      obtain ⟨c, hac, hc⟩ := tc_first_step hab
      rcases hc with hceq | hcm
      · subst hceq; exact ⟨c, hac, Or.inr hmb⟩
      · exact ⟨c, hac, Or.inr (TC.trans hcm hmb)⟩

/-- Every `TC r a b` derivation has a last hop: an edge `c → b`. -/
theorem tc_last_target {r : α → α → Prop} : ∀ {a b : α}, TC r a b → ∃ c, r c b
  | _, _, TC.base h => ⟨_, h⟩
  | _, _, TC.trans _ hbc => tc_last_target hbc

theorem length_lt_of_subset_of_nodup_of_mem_not_mem {S T : List α}
    (hSnodup : S.Nodup) (hsub : S ⊆ T) {y : α} (hyT : y ∈ T) (hyS : y ∉ S) :
    S.length < T.length := by
  obtain ⟨t1, t2, rfl⟩ := List.append_of_mem hyT
  have hsub' : S ⊆ t1 ++ t2 := by
    intro n hn
    have hnT : n ∈ t1 ++ y :: t2 := hsub hn
    rcases List.mem_append.mp hnT with h1 | h2
    · exact List.mem_append_left t2 h1
    · rcases List.mem_cons.mp h2 with hny | hnt2
      · exact absurd (hny ▸ hn) hyS
      · exact List.mem_append_right t1 hnt2
  have hle := AutoproverCorpus.QuorumIntersection.length_le_of_subset_of_nodup hSnodup hsub'
  simp only [List.length_append, List.length_cons] at hle ⊢
  omega

/-! ### `rank`: a classical Nat-valued reachable-set-size measure -/

noncomputable def rank (nodes : List α) (E : α → α → Prop) (x : α) : Nat :=
  (nodes.filter (fun n => @Decidable.decide (TC E x n) (Classical.propDecidable _))).length

theorem mem_rank_filter {nodes : List α} {E : α → α → Prop} {z n : α} :
    n ∈ nodes.filter (fun m => @Decidable.decide (TC E z m) (Classical.propDecidable _)) ↔
    n ∈ nodes ∧ TC E z n := by
  simp only [List.mem_filter, decide_eq_true_iff]

theorem rank_lt {nodes : List α} {E : α → α → Prop} (hnodesNodup : nodes.Nodup)
    (htgt : ∀ x y, E x y → y ∈ nodes) (hacyc : ∀ x, ¬ TC E x x) {x y : α} (h : TC E x y) :
    rank nodes E y < rank nodes E x := by
  unfold rank
  have hyNodes : y ∈ nodes := by
    obtain ⟨c, hc⟩ := tc_last_target h
    exact htgt c y hc
  have hsub :
      nodes.filter (fun n => @Decidable.decide (TC E y n) (Classical.propDecidable _)) ⊆
      nodes.filter (fun n => @Decidable.decide (TC E x n) (Classical.propDecidable _)) := by
    intro n hn
    have hn' := mem_rank_filter.mp hn
    exact mem_rank_filter.mpr ⟨hn'.1, tc_transitive h hn'.2⟩
  have hynotS :
      y ∉ nodes.filter (fun n => @Decidable.decide (TC E y n) (Classical.propDecidable _)) := by
    intro hmem
    exact hacyc y (mem_rank_filter.mp hmem).2
  have hyT :
      y ∈ nodes.filter (fun n => @Decidable.decide (TC E x n) (Classical.propDecidable _)) :=
    mem_rank_filter.mpr ⟨hyNodes, h⟩
  have hSnodup :
      (nodes.filter (fun n => @Decidable.decide (TC E y n) (Classical.propDecidable _))).Nodup :=
    List.filter_sublist.nodup hnodesNodup
  exact length_lt_of_subset_of_nodup_of_mem_not_mem hSnodup hsub hyT hynotS

/-! ### Existence: the "chase" — replace a redundant edge by its detour, recursively -/

/-- **EXISTENCE, the hard direction.** By strong induction on the Nat fuel bound
    `rank nodes E p - rank nodes E q`: given `TC E p q`, either the first hop already
    resolves as a genuine `R`-edge (no recursion needed), or it is redundant / the
    derivation genuinely detours, in which case the detour's bracketing edges
    `(p, c)`/`(c, q)` each have strictly smaller `rank`-difference (via `rank_lt`, using
    acyclicity) and are resolved by two smaller recursive calls, combined via `TC.trans`. -/
theorem chase (nodes : List α) (E : α → α → Prop) (hnodesNodup : nodes.Nodup)
    (htgt : ∀ x y, E x y → y ∈ nodes) (hacyc : ∀ x, ¬ TC E x x) :
    ∀ (n : Nat) (p q : α), rank nodes E p - rank nodes E q ≤ n → TC E p q → TC (R E) p q
  | 0, p, q, hn, hpq => by
      exfalso
      have hlt := rank_lt hnodesNodup htgt hacyc hpq
      omega
  | n + 1, p, q, hn, hpq => by
      obtain ⟨c, hpc, hc⟩ := tc_first_step hpq
      rcases hc with hceq | hcq
      · have hpcq : E p q := hceq ▸ hpc
        rcases Classical.em (R E p q) with hRpq | hnRpq
        · exact TC.base hRpq
        · have hred : TC (minus E p q) p q := by
            rcases Classical.em (TC (minus E p q) p q) with h | h
            · exact h
            · exact absurd (And.intro hpcq h) hnRpq
          obtain ⟨c', hpc', hc'⟩ := tc_first_step hred
          have hc'ne : c' ≠ q := by
            intro heq; exact hpc'.2 ⟨rfl, heq⟩
          have hEpc' : E p c' := hpc'.1
          have hc'q : TC E c' q := by
            rcases hc' with hc'eq | h
            · exact absurd hc'eq hc'ne
            · exact tc_mono (fun x y hxy => hxy.1) h
          have hrank1 := rank_lt hnodesNodup htgt hacyc (TC.base hEpc')
          have hrank2 := rank_lt hnodesNodup htgt hacyc hc'q
          have h1 : rank nodes E p - rank nodes E c' ≤ n := by omega
          have h2 : rank nodes E c' - rank nodes E q ≤ n := by omega
          exact TC.trans
            (chase nodes E hnodesNodup htgt hacyc n p c' h1 (TC.base hEpc'))
            (chase nodes E hnodesNodup htgt hacyc n c' q h2 hc'q)
      · have hcne : c ≠ q := by
          intro hce; exact hacyc q (hce ▸ hcq)
        have hrank1 := rank_lt hnodesNodup htgt hacyc (TC.base hpc)
        have hrank2 := rank_lt hnodesNodup htgt hacyc hcq
        have h1 : rank nodes E p - rank nodes E c ≤ n := by omega
        have h2 : rank nodes E c - rank nodes E q ≤ n := by omega
        exact TC.trans
          (chase nodes E hnodesNodup htgt hacyc n p c h1 (TC.base hpc))
          (chase nodes E hnodesNodup htgt hacyc n c q h2 hcq)

theorem tc_R_eq_tc_E (nodes : List α) (E : α → α → Prop) (hnodesNodup : nodes.Nodup)
    (htgt : ∀ x y, E x y → y ∈ nodes) (hacyc : ∀ x, ¬ TC E x x) (p q : α) :
    TC (R E) p q ↔ TC E p q := by
  constructor
  · intro h; exact tc_mono (fun a b hab => hab.1) h
  · intro h
    exact chase nodes E hnodesNodup htgt hacyc (rank nodes E p) p q (by omega) h

/-! ### (b) Minimality — no hypothesis beyond `R`'s own definition -/

/-- Every `R`-edge is irredundant even w.r.t. `R` itself (not just `E`): removing it from
    `R` breaks `a ↦ b` reachability within `R`. -/
theorem R_irredundant {E : α → α → Prop} {a b : α} (h : R E a b) :
    ¬ TC (minus (R E) a b) a b := by
  intro hcon
  exact h.2 (tc_mono (fun x y hxy => ⟨R_sub_E hxy.1, hxy.2⟩) hcon)

/-- **(b) MINIMALITY.** No proper subset of `R` (a relation `S` pointwise `⊆ R` that
    misses some `R`-edge `(a, b)`) preserves reachability: `TC (R E) a b` holds (via that
    very edge) while `TC S a b` does not. Needs no acyclicity/finiteness hypothesis. -/
theorem R_minimal (E : α → α → Prop) {S : α → α → Prop}
    (hSsub : ∀ x y, S x y → R E x y) (a b : α) (hRab : R E a b) (hSab : ¬ S a b) :
    TC (R E) a b ∧ ¬ TC S a b := by
  refine ⟨TC.base hRab, ?_⟩
  intro hSTC
  have hSminus : ∀ x y, S x y → minus (R E) a b x y := by
    intro x y hSxy
    refine ⟨hSsub x y hSxy, ?_⟩
    intro heq
    obtain ⟨hxa, hyb⟩ := heq
    subst hxa; subst hyb
    exact hSab hSxy
  exact R_irredundant hRab (tc_mono hSminus hSTC)

/-! ### (c) Uniqueness — needs only `Acyclic E`, no finiteness at all -/

/-- The three defining properties of "a transitive reduction of `E`": `⊆ E`, same
    reachability, and irredundancy w.r.t. the FULL `E` (not just the candidate relation
    `r` itself) — the last clause is what makes uniqueness provable. -/
def IsTransReduction (E r : α → α → Prop) : Prop :=
  (∀ a b, r a b → E a b) ∧ (∀ a b, TC r a b ↔ TC E a b) ∧
    (∀ a b, r a b → ¬ TC (minus E a b) a b)

theorem R_isTransReduction (nodes : List α) (E : α → α → Prop) (hnodesNodup : nodes.Nodup)
    (htgt : ∀ x y, E x y → y ∈ nodes) (hacyc : ∀ x, ¬ TC E x x) :
    IsTransReduction E (R E) :=
  ⟨fun _ _ h => R_sub_E h,
   fun a b => tc_R_eq_tc_E nodes E hnodesNodup htgt hacyc a b,
   fun _ _ h => h.2⟩

/-- A path out of `x` that can never get back to `a` cannot have used the edge `(a, b)`
    either — the engine of uniqueness. Plain structural induction on the `TC E x y`
    derivation; no well-founded machinery needed (unlike existence). -/
theorem avoid {E : α → α → Prop} {a b : α} :
    ∀ {p q : α}, TC E p q → p ≠ a → ¬ TC E p a → TC (minus E a b) p q := by
  intro p q h
  induction h with
  | @base p q hpq =>
      intro hpa _
      exact TC.base ⟨hpq, fun hcon => hpa hcon.1⟩
  | @trans p m q hpm hmq ihpm ihmq =>
      intro hpa hpTa
      have hma : m ≠ a := fun hme => hpTa (hme ▸ hpm)
      have hmTa : ¬ TC E m a := fun hmta => hpTa (TC.trans hpm hmta)
      exact TC.trans (ihpm hpa hpTa) (ihmq hma hmTa)

/-- **(c) UNIQUENESS.** For an `Acyclic` `E`, any two relations satisfying
    `IsTransReduction E` coincide pointwise. Proved by showing `⊆` both ways: given
    `s a b` (an `s`-edge, `s` a transition reduction), if the OTHER reduction `t` lacked
    it, `TC t a b` would still hold (same closure) via a genuine `≥ 2`-hop `t`-witness
    `a → c → … → b`; since `t ⊆ E` and `E` is acyclic, `c` cannot reach `a` back (else a
    cycle through the direct edge `a → c`), so `avoid` shows the `c → b` leg survives
    dropping edge `(a, b)`, and prepending the direct edge `(a, c)` (itself `≠ (a, b)`
    since `c ≠ b`, again by acyclicity) builds a full `TC (minus E a b) a b` witness —
    contradicting `s`'s own irredundancy clause. -/
theorem transReduction_unique {E : α → α → Prop} (hacyc : ∀ x, ¬ TC E x x)
    {r1 r2 : α → α → Prop} (h1 : IsTransReduction E r1) (h2 : IsTransReduction E r2) :
    ∀ a b, r1 a b ↔ r2 a b := by
  have side : ∀ (s t : α → α → Prop), IsTransReduction E s → IsTransReduction E t →
      ∀ a b, s a b → t a b := by
    intro s t hs ht a b hsab
    rcases Classical.em (t a b) with h | hnot
    · exact h
    · exfalso
      have htcE : TC E a b := (hs.2.1 a b).mp (TC.base hsab)
      have htcT : TC t a b := (ht.2.1 a b).mpr htcE
      obtain ⟨c, htac, hc⟩ := tc_first_step htcT
      rcases hc with hceq | hctb
      · exact hnot (hceq ▸ htac)
      · have hEac : E a c := ht.1 a c htac
        have hca : c ≠ a := by
          intro hce; exact hacyc a (TC.base (hce ▸ hEac))
        have hcNota : ¬ TC E c a := by
          intro hcta; exact hacyc a (TC.trans (TC.base hEac) hcta)
        have htcEcb : TC E c b := tc_mono ht.1 hctb
        have hcneb : c ≠ b := by
          intro hcb; exact hacyc b (hcb ▸ htcEcb)
        have h3 : TC (minus E a b) c b := avoid htcEcb hca hcNota
        have hminusac : minus E a b a c := ⟨hEac, fun hcon => hcneb hcon.2⟩
        have hbad : TC (minus E a b) a b := TC.trans (TC.base hminusac) h3
        exact hs.2.2 a b hsab hbad
  intro a b
  exact ⟨side r1 r2 h1 h2 a b, side r2 r1 h2 h1 a b⟩

/-! ### (d) Instances: a concrete 3-node DAG where the reduction drops a shortcut -/

section Instances

/-- `0 → 1`, `1 → 2`, and the shortcut `0 → 2`. -/
abbrev edgeRel : Fin 3 → Fin 3 → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 0, 2 => true
  | _, _ => false

abbrev sampleE (a b : Fin 3) : Prop := edgeRel a b = true

/-- The shortcut `0 → 2` is witnessed redundant by the two-hop detour `0 → 1 → 2`, both
    edges surviving `minus sampleE 0 2` (neither equals the pair `(0, 2)`). -/
theorem sample_path02 : TC (minus sampleE (0 : Fin 3) (2 : Fin 3)) 0 2 :=
  TC.trans
    (TC.base (show minus sampleE (0 : Fin 3) (2 : Fin 3) 0 1 from ⟨by decide, by decide⟩))
    (TC.base (show minus sampleE (0 : Fin 3) (2 : Fin 3) 1 2 from ⟨by decide, by decide⟩))

/-- **The shortcut is strictly removed.** -/
theorem sample_02_not_in_R : ¬ R sampleE (0 : Fin 3) (2 : Fin 3) :=
  fun h => h.2 sample_path02

/-- `2` is a sink: no outgoing `sampleE`-edge. -/
theorem sampleE_two_sink : ∀ (c : Fin 3), sampleE (2 : Fin 3) c → False
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | 2, h => absurd h (by decide)

/-- `0`'s only `sampleE`-successors are `1` and `2`. -/
theorem sampleE_zero_dest :
    ∀ (c : Fin 3), sampleE (0 : Fin 3) c → c ≠ (1 : Fin 3) → c = (2 : Fin 3)
  | 0, h, _ => absurd h (by decide)
  | 1, _, hne1 => absurd rfl hne1
  | 2, _, _ => rfl

/-- `1`'s only `sampleE`-successor is `2`. -/
theorem sampleE_one_dest : ∀ (c : Fin 3), sampleE (1 : Fin 3) c → c = (2 : Fin 3)
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | 2, _ => rfl

/-- **The "real" edge `0 → 1` is kept**: no alternative path from `0` to `1` avoiding it
    exists (any first hop out of `0` other than `1` must go to `2`, a sink). -/
theorem sample_01_in_R : R sampleE (0 : Fin 3) (1 : Fin 3) := by
  refine ⟨by decide, ?_⟩
  intro hcon
  obtain ⟨c, hc1, hc2⟩ := tc_first_step hcon
  have hcne1 : c ≠ (1 : Fin 3) := fun h => hc1.2 ⟨rfl, h⟩
  have hc2eq : c = (2 : Fin 3) := sampleE_zero_dest c hc1.1 hcne1
  subst hc2eq
  rcases hc2 with h | h
  · exact absurd h (by decide)
  · obtain ⟨d, hd1, _⟩ := tc_first_step h
    exact sampleE_two_sink d hd1.1

/-- **The "real" edge `1 → 2` is kept**: it is `1`'s only outgoing edge, so removing it
    leaves no alternative path at all. -/
theorem sample_12_in_R : R sampleE (1 : Fin 3) (2 : Fin 3) := by
  refine ⟨by decide, ?_⟩
  intro hcon
  obtain ⟨c, hc1, _⟩ := tc_first_step hcon
  have hcne2 : c ≠ (2 : Fin 3) := fun h => hc1.2 ⟨rfl, h⟩
  exact hcne2 (sampleE_one_dest c hc1.1)

/-- Reachability `0 ↦ 2` survives dropping the shortcut, via the two kept edges. -/
example : TC (R sampleE) (0 : Fin 3) (2 : Fin 3) :=
  TC.trans (TC.base sample_01_in_R) (TC.base sample_12_in_R)

end Instances

end AutoproverCorpus.TransitiveReduction
