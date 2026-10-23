import SourceResolve
import SourceLabelledForest
import G5CalendarRoutes

/-!
# Actual switching pruning and unary suppression, as a rooted tree evaluator
Contributor: dot / OpenAI, 2026-10-03.
Matches G5-NONPLANAR-CALENDAR-QUARTETS.md section 7: unsampled original tips
and dead twigs are discarded; one nonempty child is retained without a unary
vertex; two nonempty children are grafted. A unary root follows the SAME rule.
Only actual original retained outgoing edge occurrences supply children.
No cluster/quartet preservation conclusion is a field of the evaluation.
-/
namespace GProgram.G5.Normalization
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

noncomputable def outgoing (N : RootedBinary V E X) (S : N.Switching) (v : V) : Finset S.Edge :=
  Finset.univ.filter (fun e => S.graph.source e = v)

noncomputable def sampledDescendants (N : RootedBinary V E X) (S : N.Switching)
    (A : Finset X) (v : V) : Finset X := A.filter (fun x => S.graph.DReach v (N.leaf x))

/-- Actual empty-twig deletion / unary suppression / binary join rules.
Original children and their exact edge-set equality are the only local data. -/
inductive PrunedAt (N : RootedBinary V E X) (S : N.Switching) (A : Finset X) :
    V → Option (Genealogy X) → Prop
  | taxon (x : X) : PrunedAt N S A (N.leaf x) (if x ∈ A then some (.leaf x) else none)
  | dead (v : V) (hn : ∀ x, N.leaf x ≠ v) (hout : outgoing N S v = ∅) : PrunedAt N S A v none
  | unary (v : V) (hn : ∀ x, N.leaf x ≠ v) (e : S.Edge) (hout : outgoing N S v = {e})
      {a : Option (Genealogy X)} (child : PrunedAt N S A (S.graph.target e) a) : PrunedAt N S A v a
  | binary (v : V) (hn : ∀ x, N.leaf x ≠ v) (e f : S.Edge) (hef : e ≠ f)
      (hout : outgoing N S v = {e,f}) {a b : Option (Genealogy X)}
      (left : PrunedAt N S A (S.graph.target e) a) (right : PrunedAt N S A (S.graph.target f) b) :
      PrunedAt N S A v (Genealogy.joinPruned a b)

noncomputable def youngerRank {G : EdgeGraph V E} (C : Calendar G) (v : V) : Nat :=
  (Finset.univ.filter (fun w : V => C.age w < C.age v)).card

lemma youngerRank_edge_decreases {G : EdgeGraph V E} (C : Calendar G) (e : E) :
    youngerRank C (G.target e) < youngerRank C (G.source e) := by
  unfold youngerRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_,?_⟩
  · intro w hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    exact hw.trans (C.edge_older e)
  · intro heq
    have hm : G.target e ∈ Finset.univ.filter (fun w : V => C.age w < C.age (G.source e)) := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact C.edge_older e
    rw [←heq] at hm
    simpa using hm

/-- Actual normalization exists for EVERY original vertex of EVERY original
switching. No assumed displayed-tree evaluation is used. -/
theorem original_switching_pruning_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (S : N.Switching) (A : Finset X) (v : V) : ∃ T, PrunedAt N S A v T := by
  have aux : ∀ k : Nat, ∀ v : V, youngerRank C v = k → ∃ T, PrunedAt N S A v T := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hk
      by_cases hx : ∃ x : X, N.leaf x = v
      · obtain ⟨x,rfl⟩ := hx
        exact ⟨_,PrunedAt.taxon x⟩
      · have hn : ∀ x, N.leaf x ≠ v := fun x he => hx ⟨x,he⟩
        have hc : (outgoing N S v).card ≤ 2 := (S.selected_outdegree_le v).trans (N.outDegree_le_two v)
        have hchild (e : S.Edge) (he : e ∈ outgoing N S v) : ∃ T, PrunedAt N S A (S.graph.target e) T := by
          have hs := (Finset.mem_filter.mp he).2
          have hl : youngerRank C (S.graph.target e) < k := by
            have hh := youngerRank_edge_decreases C e.val
            rw [show N.graph.source e.val = v from hs,hk] at hh
            exact hh
          exact ih _ hl _ rfl
        by_cases hzero : (outgoing N S v).card = 0
        · exact ⟨none,PrunedAt.dead v hn (Finset.card_eq_zero.mp hzero)⟩
        · by_cases hone : (outgoing N S v).card = 1
          · obtain ⟨e,heq⟩ := Finset.card_eq_one.mp hone
            obtain ⟨a,ha⟩ := hchild e (by rw [heq]; simp)
            exact ⟨a,PrunedAt.unary v hn e heq ha⟩
          · have htwo : (outgoing N S v).card = 2 := by omega
            obtain ⟨e,f,hef,heq⟩ := Finset.card_eq_two.mp htwo
            obtain ⟨a,ha⟩ := hchild e (by rw [heq]; simp)
            obtain ⟨b,hb⟩ := hchild f (by rw [heq]; simp)
            exact ⟨Genealogy.joinPruned a b,PrunedAt.binary v hn e f hef heq ha hb⟩
  exact aux (youngerRank C v) v rfl

lemma sampledDescendants_children (N : RootedBinary V E X) (S : N.Switching) (A : Finset X)
    (v : V) (hn : ∀ x, N.leaf x ≠ v) :
    sampledDescendants N S A v = (outgoing N S v).biUnion (fun e => sampledDescendants N S A (S.graph.target e)) := by
  ext x
  simp only [sampledDescendants,Finset.mem_filter,Finset.mem_biUnion]
  constructor
  · rintro ⟨hx,hd⟩
    rcases Relation.ReflTransGen.cases_head hd with heq | ⟨w,he,hw⟩
    · exact False.elim (hn x heq.symm)
    · obtain ⟨e,hs,ht⟩ := he
      exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,hx,ht.symm ▸ hw⟩
  · rintro ⟨e,he,hx,hd⟩
    have hs := (Finset.mem_filter.mp he).2
    exact ⟨hx,(Relation.ReflTransGen.single ⟨e,hs,rfl⟩).trans hd⟩

lemma sampledDescendants_taxon (N : RootedBinary V E X) (S : N.Switching) (A : Finset X) (x : X) :
    sampledDescendants N S A (N.leaf x) = if x ∈ A then {x} else ∅ := by
  ext y
  have hreach : S.graph.DReach (N.leaf x) (N.leaf y) ↔ x = y := by
    constructor
    · intro h
      exact N.leaf.injective (S.graph.dreach_eq_of_outdegree_zero (S.selected_leaf_degrees x).2 h)
    · rintro rfl; exact .refl
  simp only [sampledDescendants,Finset.mem_filter,hreach]
  by_cases hx : x ∈ A <;> simp [hx] <;> aesop

/-- Pruning deletes precisely unsampled labels and dead twigs; unary suppression
preserves the complete selected descendant label set, including a unary root. -/
theorem prunedAt_exact_leaves (N : RootedBinary V E X) (S : N.Switching) (A : Finset X)
    {v : V} {T : Option (Genealogy X)} (eval : PrunedAt N S A v T) :
    Genealogy.optionLeaves T = sampledDescendants N S A v := by
  induction eval with
  | taxon x =>
    rw [sampledDescendants_taxon]
    split_ifs <;> rfl
  | dead v hn hout =>
    rw [sampledDescendants_children N S A v hn,hout]
    simp [Genealogy.optionLeaves]
  | unary v hn e hout child ih =>
    rw [sampledDescendants_children N S A v hn,hout]
    simpa using ih
  | binary v hn e f hef hout left right ihl ihr =>
    rw [Genealogy.joinPruned_leaves,ihl,ihr,sampledDescendants_children N S A v hn,hout]
    simp

#print axioms original_switching_pruning_exists
#print axioms prunedAt_exact_leaves
end GProgram.G5.Normalization
