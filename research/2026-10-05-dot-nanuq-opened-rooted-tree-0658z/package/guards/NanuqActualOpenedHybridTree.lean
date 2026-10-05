import guards.NanuqActualRootSkeleton

set_option debug.skipKernelTC false

/-! Literal opening of each hybrid parent occurrence into a distinct new
pendant tip. The connected acyclic graph is derived from the actual original
source; no tip order, planarity certificate, or desired quartet law is input. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

abbrev HybridParentOccurrence := {e : E // N.graph.IsHybrid (N.graph.target e)}
abbrev OpenedHybridVertex := Sum N.SkeletonVertex N.HybridParentOccurrence
abbrev OpenedHybridEdge := Sum N.SkeletonEdge N.HybridParentOccurrence

noncomputable instance openedHybridVertexFintype : Fintype N.OpenedHybridVertex := by
  classical
  unfold OpenedHybridVertex HybridParentOccurrence
  infer_instance
noncomputable instance openedHybridEdgeFintype : Fintype N.OpenedHybridEdge := by
  classical
  unfold OpenedHybridEdge HybridParentOccurrence
  infer_instance
noncomputable instance openedHybridVertexDecidableEq : DecidableEq N.OpenedHybridVertex := Classical.decEq _

theorem hybrid_parent_source_skeleton
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)
    (e : N.HybridParentOccurrence) : N.SkeletonVertexPredicate (N.graph.source e.val) := by
  constructor
  · intro hh
    obtain ⟨x,hx⟩ := hleaf e.val hh
    have h1 := (N.leaf_degrees x).1
    have h2 := e.property.1
    rw [hx] at h2
    omega
  · intro f hf hh
    obtain ⟨x,hx⟩ := hleaf f hh
    exact N.graph.no_edge_source_of_outdegree_zero (N.leaf_degrees x).2 e.val (hf.symm.trans hx)

def openedHybridGraph
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x) :
    EdgeGraph N.OpenedHybridVertex N.OpenedHybridEdge where
  source := Sum.elim (fun e => Sum.inl (N.rootSkeletonGraph.source e))
    (fun e => Sum.inl ⟨N.graph.source e.val,N.hybrid_parent_source_skeleton hleaf e⟩)
  target := Sum.elim (fun e => Sum.inl (N.rootSkeletonGraph.target e)) Sum.inr

def openedHybridOriginalVertex : N.OpenedHybridVertex → V :=
  Sum.elim Subtype.val (fun e => N.graph.target e.val)

theorem opened_hybrid_acyclic
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x) :
    (N.openedHybridGraph hleaf).Acyclic := by
  intro v h
  apply N.acyclic (N.openedHybridOriginalVertex v)
  apply Relation.TransGen.lift N.openedHybridOriginalVertex _ v v h
  intro a b hab
  obtain ⟨e,hs,ht⟩ := hab
  rcases e with e | e
  · exact ⟨e.val,congrArg N.openedHybridOriginalVertex hs,congrArg N.openedHybridOriginalVertex ht⟩
  · exact ⟨e.val,congrArg N.openedHybridOriginalVertex hs,congrArg N.openedHybridOriginalVertex ht⟩

theorem opened_hybrid_uniqueIncoming
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x) :
    (N.openedHybridGraph hleaf).UniqueIncoming := by
  intro e f heq
  rcases e with e | e <;> rcases f with f | f
  · exact congrArg Sum.inl (N.root_skeleton_uniqueIncoming e f (Sum.inl.inj heq))
  · cases heq
  · cases heq
  · exact congrArg Sum.inr (Sum.inr.inj heq)

theorem skeleton_path_lifts_to_opened
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)
    {a b : N.SkeletonVertex} (h : N.rootSkeletonGraph.DReach a b) :
    (N.openedHybridGraph hleaf).DReach (Sum.inl a) (Sum.inl b) := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    obtain ⟨e,he,ht⟩ := hs
    exact ih.tail ⟨Sum.inl e,congrArg Sum.inl he,congrArg Sum.inl ht⟩

theorem opened_hybrid_rooted
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)
    (v : N.OpenedHybridVertex) :
    (N.openedHybridGraph hleaf).DReach (Sum.inl N.rootSkeletonRoot) v := by
  rcases v with a | e
  · exact N.skeleton_path_lifts_to_opened hleaf
      (N.root_skeleton_dreach_lift hleaf (N.rooted a.val) a.property)
  · let a : N.SkeletonVertex := ⟨N.graph.source e.val,N.hybrid_parent_source_skeleton hleaf e⟩
    have h := N.skeleton_path_lifts_to_opened hleaf
      (N.root_skeleton_dreach_lift hleaf (N.rooted a.val) a.property)
    exact h.tail ⟨Sum.inr e,rfl,rfl⟩

theorem actual_opened_hybrid_graph_is_tree
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x) :
    (N.openedHybridGraph hleaf).IsTree := by
  refine ⟨⟨Sum.inl N.rootSkeletonRoot⟩,?_,?_⟩
  · intro a b
    exact ((N.openedHybridGraph hleaf).ureach_symm
      ((N.openedHybridGraph hleaf).dreach_ureach (N.opened_hybrid_rooted hleaf a))).trans
        ((N.openedHybridGraph hleaf).dreach_ureach (N.opened_hybrid_rooted hleaf b))
  · exact (N.openedHybridGraph hleaf).uniqueIncoming_all_bridges
      (N.opened_hybrid_uniqueIncoming hleaf) (N.opened_hybrid_acyclic hleaf)

theorem actual_galled_cap_opens_to_tree (hg : N.graph.GalledDetour)
    (b : N.graph.Blob) (hb : N.NonleafBlob b) :
    ((N.actualEveryNonleafRootedCapSource b hb).openedHybridGraph
      (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb)).IsTree :=
  (N.actualEveryNonleafRootedCapSource b hb).actual_opened_hybrid_graph_is_tree _
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_galled_cap_opens_to_tree
