/-
  AutoproverCorpus.Order.BoundedPath

  Path shortening in a directed graph: every reachability witness (walk) over a finite node list
  can be shortened, by splicing out repeated nodes, to a duplicate-free path of length at most
  the number of nodes. Includes the chain/walk machinery: existence of a walk for any
  transitive-closure fact, splicing lemmas, and the bounded duplicate-free path lemma.

  Attribution: Classical (graph-theory folklore: every walk contains a simple path).

  Machine-checked in Lean 4 (core language, no external libraries).
  The claim made is exactly the theorem statements below, as accepted
  by the Lean kernel; hypotheses named in the statements are assumed,
  not proved.
-/

import AutoproverCorpus.Order.TransitiveClosure
import AutoproverCorpus.Distributed.QuorumIntersection

namespace AutoproverCorpus.BoundedPath

open AutoproverCorpus.TransitiveClosure (TC)

/-! ### Layer 0: `Chain`, an accumulator-style path predicate -/

section GenericNode

variable {Node : Type} [DecidableEq Node]

/-- `Chain r prev l` : starting from `prev`, each element of `l` follows the previous one
    along `r`. Accumulator style (recursion on the single list argument `l`, `prev` carried
    along) rather than a 3-way match on list shape — chosen so induction/splicing proofs are
    plain structural recursion. -/
def Chain (r : Node → Node → Prop) : Node → List Node → Prop
  | _, [] => True
  | prev, a :: t => r prev a ∧ Chain r a t

/-! ### Layer 1: existence of SOME `Chain` witness for a `TC` pair -/

omit [DecidableEq Node] in
/-- Gluing two `Chain` witnesses that share a midpoint: `Chain r prev l1` reaching `mid`
    (`l1.getLast? = some mid`) followed by `Chain r mid l2` gives `Chain r prev (l1 ++ l2)`. -/
theorem chain_append {r : Node → Node → Prop} :
    ∀ {prev mid : Node} {l1 l2 : List Node}, Chain r prev l1 → l1.getLast? = some mid →
      Chain r mid l2 → Chain r prev (l1 ++ l2)
  | prev, mid, [], l2, _, hlast, _ => by simp at hlast
  | prev, mid, [x], l2, h1, hlast, h2 => by
      obtain ⟨hpx, -⟩ := h1
      have hx : x = mid := by simpa using hlast
      subst hx
      exact ⟨hpx, h2⟩
  | prev, mid, x :: y :: t, l2, h1, hlast, h2 => by
      obtain ⟨hpx, hrest⟩ := h1
      have hlast' : (y :: t).getLast? = some mid := by
        rw [List.getLast?_cons_cons] at hlast; exact hlast
      have hrec := chain_append hrest hlast' h2
      exact ⟨hpx, hrec⟩

omit [DecidableEq Node] in
/-- **Existence.** Every `TC r a b` pair has a `Chain` witness: a nonempty node sequence
    `rest` such that walking from `a` through `rest` along `r` reaches `b`. By induction on
    the `TC` derivation; the `trans` case glues the two sub-witnesses via `chain_append`. -/
theorem exists_chain {r : Node → Node → Prop} {a b : Node} (h : TC r a b) :
    ∃ rest : List Node, rest ≠ [] ∧ Chain r a rest ∧ (a :: rest).getLast? = some b := by
  induction h with
  | @base a b hab => exact ⟨[b], by simp, ⟨hab, trivial⟩, by simp⟩
  | @trans a b c hab hbc ihab ihbc =>
      obtain ⟨rest1, hne1, hc1, hl1⟩ := ihab
      obtain ⟨rest2, hne2, hc2, hl2⟩ := ihbc
      have hl1' : rest1.getLast? = some b := by
        rwa [List.getLast?_cons_of_ne_nil hne1] at hl1
      have hl2' : rest2.getLast? = some c := by
        rwa [List.getLast?_cons_of_ne_nil hne2] at hl2
      refine ⟨rest1 ++ rest2, ?_, ?_, ?_⟩
      · rcases rest1 with _ | ⟨x1, xs1⟩
        · exact absurd rfl hne1
        · simp
      · exact chain_append hc1 hl1' hc2
      · rw [List.getLast?_cons_of_ne_nil (by
          rcases rest1 with _ | ⟨x1, xs1⟩
          · exact absurd rfl hne1
          · simp),
          List.getLast?_append, hl2']
        rfl

/-! ### Layer 2: shortening — splice out a repeated node -/

omit [DecidableEq Node] in
/-- If a `Chain` witness starting at `prev` passes through `l2` and returns to `x`
    (`prev, ..., x, l3`), the tail from `x` through `l3` is already a valid `Chain` witness
    on its own — the loop `l2` back to `x` can be skipped entirely. -/
theorem chain_shortcut {r : Node → Node → Prop} :
    ∀ {prev x : Node} (l2 l3 : List Node), Chain r prev (l2 ++ x :: l3) → Chain r x l3
  | _prev, _x, [], _l3, h => h.2
  | _prev, _x, _c :: l2', l3, h => chain_shortcut l2' l3 h.2

omit [DecidableEq Node] in
/-- **Splicing.** A repeated node `x` in a `Chain` witness (occurring once in `l1 ++ x :: …`
    and again after `l2`) can be dropped along with everything between the two occurrences,
    yielding a shorter valid `Chain` witness with the same start. -/
theorem chain_splice {r : Node → Node → Prop} {x : Node} :
    ∀ {prev : Node} (l1 l2 l3 : List Node),
      Chain r prev (l1 ++ x :: l2 ++ x :: l3) → Chain r prev (l1 ++ x :: l3)
  | _prev, [], l2, l3, h => ⟨h.1, chain_shortcut l2 l3 h.2⟩
  | _prev, _y :: l1', l2, l3, h => ⟨h.1, chain_splice l1' l2 l3 h.2⟩

theorem exists_dup_split {α : Type} [DecidableEq α] :
    ∀ (l : List α), ¬ l.Nodup → ∃ (x : α) (l1 l2 l3 : List α), l = l1 ++ x :: l2 ++ x :: l3
  | [], h => absurd List.nodup_nil h
  | a :: t, h => by
      by_cases hat : a ∈ t
      · obtain ⟨s, u, hsu⟩ := List.append_of_mem hat
        exact ⟨a, [], s, u, by simp [hsu]⟩
      · have ht : ¬ t.Nodup := fun htnodup => h (List.nodup_cons.mpr ⟨hat, htnodup⟩)
        obtain ⟨x, l1, l2, l3, hl⟩ := exists_dup_split t ht
        exact ⟨x, a :: l1, l2, l3, by simp [hl]⟩

omit [DecidableEq Node] in
theorem getLast?_append_nonempty_right {l2 : List Node} (h : l2 ≠ []) :
    ∀ (l1 : List Node), (l1 ++ l2).getLast? = l2.getLast?
  | [] => by simp
  | c :: t => by
      have hne : t ++ l2 ≠ [] := by
        intro he
        apply h
        simpa using (List.append_eq_nil_iff.mp he).2
      rw [List.cons_append, List.getLast?_cons_of_ne_nil hne,
        getLast?_append_nonempty_right h t]

omit [DecidableEq Node] in
/-- Splicing out a duplicate does not change the overall `getLast?` — both the original and
    spliced lists end at the same tail `x :: l3`. -/
theorem getLast?_dup_splice {l1 l2 l3 : List Node} {x : Node} :
    (l1 ++ x :: l2 ++ x :: l3).getLast? = (l1 ++ x :: l3).getLast? := by
  have hne : (x :: l3 : List Node) ≠ [] := by simp
  rw [getLast?_append_nonempty_right hne (l1 ++ x :: l2), getLast?_append_nonempty_right hne l1]

/-! ### Layer 3: iterate splicing to a `Nodup` witness -/

theorem shorten {r : Node → Node → Prop} :
    ∀ (n : Nat) {a b : Node} {rest : List Node}, rest.length ≤ n → rest ≠ [] →
      Chain r a rest → (a :: rest).getLast? = some b →
      ∃ rest' : List Node, rest' ≠ [] ∧ Chain r a rest' ∧
        (a :: rest').getLast? = some b ∧ rest'.Nodup
  | 0, a, b, rest, hn, hne, _hc, _hl =>
      absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)) hne
  | n + 1, a, b, rest, hn, hne, hc, hl => by
      by_cases hnodup : rest.Nodup
      · exact ⟨rest, hne, hc, hl, hnodup⟩
      · obtain ⟨x, l1, l2, l3, hsplit⟩ := exists_dup_split rest hnodup
        have hc' : Chain r a (l1 ++ x :: l3) := by
          rw [hsplit] at hc; exact chain_splice l1 l2 l3 hc
        have hl' : (a :: (l1 ++ x :: l3)).getLast? = some b := by
          have heq : (a :: rest).getLast? = (a :: (l1 ++ x :: l3)).getLast? := by
            rw [hsplit,
              show a :: (l1 ++ x :: l2 ++ x :: l3) = (a :: l1) ++ x :: l2 ++ x :: l3 from rfl,
              show a :: (l1 ++ x :: l3) = (a :: l1) ++ x :: l3 from rfl]
            exact getLast?_dup_splice
          rw [← heq]; exact hl
        have hlen : (l1 ++ x :: l3).length < rest.length := by
          rw [hsplit]; simp only [List.length_append, List.length_cons]; omega
        have hne' : l1 ++ x :: l3 ≠ [] := by simp
        exact shorten n (by omega) hne' hc' hl'

/-! ### Layer 4: membership in a finite node list, and the length bound -/

omit [DecidableEq Node] in
/-- Every node in a `Chain` witness lies in `nodes`, given that every EDGE SOURCE lies in
    `nodes` (`hsrc`) and the true endpoint `b` lies in `nodes` (`hb`, supplied separately —
    `b` need not itself be a source of anything). -/
theorem chain_mem {r : Node → Node → Prop} {nodes : List Node}
    (hsrc : ∀ x y, r x y → x ∈ nodes) {b : Node} (hb : b ∈ nodes) :
    ∀ {prev : Node} {l : List Node}, Chain r prev l → prev ∈ nodes →
      (prev :: l).getLast? = some b → ∀ n ∈ prev :: l, n ∈ nodes
  | prev, [], _hchain, hprev, _hlast => by
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      subst hn; exact hprev
  | prev, a :: t, hchain, hprev, hlast => by
      have hlast' : (a :: t).getLast? = some b := by
        rw [List.getLast?_cons_of_ne_nil (show (a :: t) ≠ [] by simp)] at hlast
        exact hlast
      have ha : a ∈ nodes := by
        cases t with
        | nil =>
            have hb' : a = b := by simpa using hlast'
            rw [hb']; exact hb
        | cons c t' => exact hsrc a c hchain.2.1
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn'
      · exact hprev
      · exact chain_mem hsrc hb hchain.2 ha hlast' n hn'

omit [DecidableEq Node] in
/-- A genuine `TC r a b` derivation always starts with an honest `r`-edge out of `a`. -/
theorem tc_first_source {r : Node → Node → Prop} : ∀ {a b : Node}, TC r a b → ∃ c, r a c
  | _, _, TC.base h => ⟨_, h⟩
  | _, _, TC.trans hab _ => tc_first_source hab

theorem exists_bounded_nodup_path {r : Node → Node → Prop} {nodes : List Node}
    (hsrc : ∀ x y, r x y → x ∈ nodes) {a b : Node} (hb : b ∈ nodes) (h : TC r a b) :
    ∃ rest : List Node, rest ≠ [] ∧ Chain r a rest ∧ (a :: rest).getLast? = some b ∧
      rest.Nodup ∧ rest.length ≤ nodes.length := by
  obtain ⟨rest0, hne0, hc0, hl0⟩ := exists_chain h
  obtain ⟨rest, hne, hc, hl, hnodup⟩ := shorten rest0.length (Nat.le_refl _) hne0 hc0 hl0
  obtain ⟨c, hac⟩ := tc_first_source h
  have ha : a ∈ nodes := hsrc a c hac
  have hmem := chain_mem hsrc hb hc ha hl
  have hsub : rest ⊆ nodes := fun n hn => hmem n (List.mem_cons_of_mem a hn)
  have hlen := AutoproverCorpus.QuorumIntersection.length_le_of_subset_of_nodup hnodup hsub
  exact ⟨rest, hne, hc, hl, hnodup, hlen⟩

end GenericNode

end AutoproverCorpus.BoundedPath
