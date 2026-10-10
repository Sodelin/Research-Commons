import NanuqActualOpenedHybridTree

/-! Original outgoing edge occurrences are preserved by hybrid opening.
The new tips each have exactly one incoming edge and no outgoing edge. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

theorem skeleton_edge_nonhybrid_target (e : E)
    (hs : N.SkeletonVertexPredicate (N.graph.source e))
    (ht : ¬ N.graph.IsHybrid (N.graph.target e)) : N.SkeletonVertexPredicate (N.graph.target e) := by
  refine ⟨ht,?_⟩
  intro f hf hh
  obtain ⟨g,hg,hu⟩ := N.incoming_unique_of_indegree_one
    (N.indegree_one_of_nonroot_nonhybrid (N.edge_target_ne_root e) ht)
  have heq : f = e := (hu f hf).trans (hu e rfl).symm
  exact hs.1 (by rw [← heq];exact hh)

noncomputable def openedOutEdge (e : E) (hs : N.SkeletonVertexPredicate (N.graph.source e)) :
    N.OpenedHybridEdge :=
  if ht : N.graph.IsHybrid (N.graph.target e) then Sum.inr ⟨e,ht⟩
  else Sum.inl ⟨e,hs,N.skeleton_edge_nonhybrid_target e hs ht⟩

def openedOriginalEdge : N.OpenedHybridEdge → E := Sum.elim Subtype.val Subtype.val

theorem openedOutEdge_source (e : E) (hs : N.SkeletonVertexPredicate (N.graph.source e)) :
    (N.openedHybridGraph hleaf).source (N.openedOutEdge e hs) = Sum.inl ⟨N.graph.source e,hs⟩ := by
  unfold openedOutEdge
  split <;> rfl

theorem openedOutEdge_original (e : E) (hs : N.SkeletonVertexPredicate (N.graph.source e)) :
    N.openedOriginalEdge (N.openedOutEdge e hs) = e := by
  unfold openedOutEdge
  split <;> rfl

theorem openedOriginalEdge_source (f : N.OpenedHybridEdge) (v : N.SkeletonVertex)
    (hf : (N.openedHybridGraph hleaf).source f = Sum.inl v) :
    N.graph.source (N.openedOriginalEdge f) = v.val := by
  rcases f with e | e <;> exact congrArg Subtype.val (Sum.inl.inj hf)

theorem openedOutEdge_roundtrip (f : N.OpenedHybridEdge) (v : N.SkeletonVertex)
    (hf : (N.openedHybridGraph hleaf).source f = Sum.inl v) :
    N.openedOutEdge (N.openedOriginalEdge f)
      (by rw [N.openedOriginalEdge_source hleaf f v hf];exact v.property) = f := by
  rcases f with e | e
  · simp [openedOriginalEdge,openedOutEdge,e.property.2.1]
  · simp [openedOriginalEdge,openedOutEdge,e.property]

noncomputable def openedOutEquiv (v : N.SkeletonVertex) :
    {e : E // N.graph.source e = v.val} ≃
      {f : N.OpenedHybridEdge // (N.openedHybridGraph hleaf).source f = Sum.inl v} where
  toFun e := ⟨N.openedOutEdge e.val (by rw [e.property];exact v.property),
    (N.openedOutEdge_source hleaf e.val _).trans (congrArg Sum.inl (Subtype.ext e.property))⟩
  invFun f := ⟨N.openedOriginalEdge f.val,N.openedOriginalEdge_source hleaf f.val v f.property⟩
  left_inv e := Subtype.ext (N.openedOutEdge_original e.val (by rw [e.property];exact v.property))
  right_inv f := Subtype.ext (N.openedOutEdge_roundtrip hleaf f.val v f.property)

theorem opened_inner_outdegree (v : N.SkeletonVertex) :
    (N.openedHybridGraph hleaf).outDegree (Sum.inl v) = N.graph.outDegree v.val := by
  classical
  unfold EdgeGraph.outDegree
  rw [← Fintype.card_subtype,← Fintype.card_subtype]
  exact (Fintype.card_congr (N.openedOutEquiv hleaf v)).symm

theorem opened_new_tip_degrees (e : N.HybridParentOccurrence) :
    (N.openedHybridGraph hleaf).inDegree (Sum.inr e) = 1 ∧
      (N.openedHybridGraph hleaf).outDegree (Sum.inr e) = 0 := by
  classical
  constructor
  · apply Finset.card_eq_one_iff_existsUnique.mpr
    refine ⟨Sum.inr e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,?_⟩
    intro f hf
    have ht := (Finset.mem_filter.mp hf).2
    rcases f with f | f
    · cases ht
    · exact congrArg Sum.inr (Sum.inr.inj ht)
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hs := (Finset.mem_filter.mp hf).2
    rcases f with f | f <;> cases hs
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.opened_inner_outdegree
#print axioms Nanuq.Source.RootedBinary.opened_new_tip_degrees
