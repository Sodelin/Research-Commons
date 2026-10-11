import NanuqActualOpenedTipMultiplicity

/-! Full binary degrees and exact tip admission for the actual opened tree.
The original root is retained as the sole degree-two undirected root; no
unlabelled dangling leaf is introduced by the opening. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

noncomputable def openedInEquiv (v : N.SkeletonVertex) :
    {e : E // N.graph.target e = v.val} ≃
      {f : N.OpenedHybridEdge // (N.openedHybridGraph hleaf).target f = Sum.inl v} where
  toFun e := ⟨Sum.inl ⟨e.val,N.skeleton_predicate_parent hleaf e.val
    (by rw [e.property];exact v.property),(by rw [e.property];exact v.property)⟩,
    congrArg Sum.inl (Subtype.ext e.property)⟩
  invFun f := by
    rcases f with ⟨e | e,hf⟩
    · exact ⟨e.val,congrArg Subtype.val (Sum.inl.inj hf)⟩
    · cases hf
  left_inv e := rfl
  right_inv f := by
    rcases f with ⟨e | e,hf⟩
    · rfl
    · cases hf

theorem opened_inner_indegree (v : N.SkeletonVertex) :
    (N.openedHybridGraph hleaf).inDegree (Sum.inl v) = N.graph.inDegree v.val := by
  classical
  unfold EdgeGraph.inDegree
  rw [← Fintype.card_subtype,← Fintype.card_subtype]
  exact (Fintype.card_congr (N.openedInEquiv hleaf v)).symm

theorem opened_root_degrees :
    (N.openedHybridGraph hleaf).inDegree (Sum.inl N.rootSkeletonRoot) = 0 ∧
      (N.openedHybridGraph hleaf).outDegree (Sum.inl N.rootSkeletonRoot) = 2 := by
  rw [N.opened_inner_indegree,N.opened_inner_outdegree]
  exact N.root_degrees

theorem opened_tip_degrees (t : N.OpenedTip) :
    (N.openedHybridGraph hleaf).inDegree (N.openedTipVertex t) = 1 ∧
      (N.openedHybridGraph hleaf).outDegree (N.openedTipVertex t) = 0 := by
  rcases t with x | e
  · change (N.openedHybridGraph hleaf).inDegree (Sum.inl ⟨N.leaf x.val,x.property⟩) = 1 ∧
      (N.openedHybridGraph hleaf).outDegree (Sum.inl ⟨N.leaf x.val,x.property⟩) = 0
    rw [N.opened_inner_indegree,N.opened_inner_outdegree]
    exact N.leaf_degrees x.val
  · exact N.opened_new_tip_degrees hleaf e

theorem opened_tip_ne_root (t : N.OpenedTip) :
    N.openedTipVertex t ≠ Sum.inl N.rootSkeletonRoot := by
  rcases t with x | e
  · intro he
    exact N.leaf_ne_root x.val (congrArg Subtype.val (Sum.inl.inj he))
  · intro he;cases he

theorem opened_internal_degrees (v : N.OpenedHybridVertex)
    (hr : v ≠ Sum.inl N.rootSkeletonRoot) (hl : ∀ t : N.OpenedTip, N.openedTipVertex t ≠ v) :
    (N.openedHybridGraph hleaf).inDegree v = 1 ∧ (N.openedHybridGraph hleaf).outDegree v = 2 := by
  rcases v with a | e
  · have har : a.val ≠ N.root := by
      intro h
      exact hr (congrArg Sum.inl (Subtype.ext h))
    have hal : ∀ x, N.leaf x ≠ a.val := by
      intro x hx
      have hs : N.SkeletonVertexPredicate (N.leaf x) := by rw [hx];exact a.property
      exact hl (Sum.inl ⟨x,hs⟩) (congrArg Sum.inl (Subtype.ext hx))
    have hd := (N.internal_degrees a.val har hal).resolve_right a.property.1
    rw [N.opened_inner_indegree,N.opened_inner_outdegree]
    exact hd
  · exact False.elim (hl (Sum.inr e) rfl)

theorem opened_tip_label_surjective : Function.Surjective (N.openedTipLabel hleaf) := by
  intro x
  have h := N.actual_opened_tip_multiplicity hleaf x
  have hp : 0 < (Finset.univ.filter (fun t : N.OpenedTip => N.openedTipLabel hleaf t = x)).card := by
    rw [h]
    split_ifs <;> decide
  obtain ⟨t,ht⟩ := Finset.card_pos.mp hp
  exact ⟨t,(Finset.mem_filter.mp ht).2⟩

include hleaf in
theorem opened_at_least_two_tips : 2 ≤ Fintype.card N.OpenedTip :=
  Nat.le_trans N.at_least_two_taxa (Fintype.card_le_of_surjective _ (N.opened_tip_label_surjective hleaf))
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.opened_internal_degrees
#print axioms Nanuq.Source.RootedBinary.opened_at_least_two_tips
