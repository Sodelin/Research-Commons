import guards.NanuqActualCappedHybridTips

set_option debug.skipKernelTC false

/-! The unreduced root skeleton of a source with pendant hybrid children is
an actual edge-indexed tree. It may have unlabeled leaves; no tree-child
hypothesis or desired skeleton certificate is assumed. The final theorem
instantiates the predicate on the literal capped original galled source. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

def SkeletonVertexPredicate (v : V) : Prop :=
  ¬ N.graph.IsHybrid v ∧ ∀ e, N.graph.target e = v → ¬ N.graph.IsHybrid (N.graph.source e)

abbrev SkeletonVertex := {v : V // N.SkeletonVertexPredicate v}
abbrev SkeletonEdge := {e : E // N.SkeletonVertexPredicate (N.graph.source e) ∧
  N.SkeletonVertexPredicate (N.graph.target e)}

noncomputable instance skeletonVertexFintype : Fintype N.SkeletonVertex := by
  classical
  unfold SkeletonVertex
  infer_instance
noncomputable instance skeletonEdgeFintype : Fintype N.SkeletonEdge := by
  classical
  unfold SkeletonEdge
  infer_instance
noncomputable instance skeletonVertexDecidableEq : DecidableEq N.SkeletonVertex := Classical.decEq _

def rootSkeletonGraph : EdgeGraph N.SkeletonVertex N.SkeletonEdge where
  source e := ⟨N.graph.source e.val,e.property.1⟩
  target e := ⟨N.graph.target e.val,e.property.2⟩

theorem root_skeleton_root_predicate : N.SkeletonVertexPredicate N.root := by
  constructor
  · intro hh
    have hd := N.root_degrees.1
    have h2 := hh.1
    omega
  · intro e he
    exact False.elim (N.edge_target_ne_root e he)

def rootSkeletonRoot : N.SkeletonVertex := ⟨N.root,N.root_skeleton_root_predicate⟩

theorem skeleton_predicate_parent
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)
    (e : E) (ht : N.SkeletonVertexPredicate (N.graph.target e)) :
    N.SkeletonVertexPredicate (N.graph.source e) := by
  refine ⟨ht.2 e rfl,?_⟩
  intro f hf hh
  obtain ⟨x,hx⟩ := hleaf f hh
  exact N.graph.no_edge_source_of_outdegree_zero (N.leaf_degrees x).2 e (hf.symm.trans hx)

theorem root_skeleton_dreach_lift
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)
    {v : V} (h : N.graph.DReach N.root v) :
    ∀ hv : N.SkeletonVertexPredicate v,
      N.rootSkeletonGraph.DReach N.rootSkeletonRoot ⟨v,hv⟩ := by
  induction h with
  | refl => intro _;exact .refl
  | @tail u w hp hs ih =>
    intro hw
    obtain ⟨e,hes,het⟩ := hs
    have ht : N.SkeletonVertexPredicate (N.graph.target e) := by rw [het];exact hw
    have hs0 := N.skeleton_predicate_parent hleaf e ht
    have hu : N.SkeletonVertexPredicate u := by rw [← hes];exact hs0
    exact (ih hu).tail ⟨⟨e,hs0,ht⟩,Subtype.ext hes,Subtype.ext het⟩

theorem root_skeleton_acyclic : N.rootSkeletonGraph.Acyclic := by
  intro v h
  have hd : Relation.TransGen N.graph.DStep v.val v.val := by
    apply Relation.TransGen.lift (fun a : N.SkeletonVertex => a.val) _ v v h
    intro a b hab
    obtain ⟨e,he,ht⟩ := hab
    exact ⟨e.val,congrArg Subtype.val he,congrArg Subtype.val ht⟩
  exact N.acyclic v.val hd

theorem root_skeleton_uniqueIncoming : N.rootSkeletonGraph.UniqueIncoming := by
  intro e f ht
  have heq : N.graph.target e.val = N.graph.target f.val := congrArg Subtype.val ht
  obtain ⟨g,hg,hu⟩ := N.incoming_unique_of_indegree_one
    (N.indegree_one_of_nonroot_nonhybrid (N.edge_target_ne_root e.val) e.property.2.1)
  exact Subtype.ext ((hu e.val rfl).trans (hu f.val heq.symm).symm)

theorem actual_root_skeleton_is_tree
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x) :
    N.rootSkeletonGraph.IsTree := by
  have hr (v : N.SkeletonVertex) : N.rootSkeletonGraph.DReach N.rootSkeletonRoot v :=
    N.root_skeleton_dreach_lift hleaf (N.rooted v.val) v.property
  refine ⟨⟨N.rootSkeletonRoot⟩,?_,?_⟩
  · intro a b
    exact (N.rootSkeletonGraph.ureach_symm (N.rootSkeletonGraph.dreach_ureach (hr a))).trans
      (N.rootSkeletonGraph.dreach_ureach (hr b))
  · exact N.rootSkeletonGraph.uniqueIncoming_all_bridges N.root_skeleton_uniqueIncoming N.root_skeleton_acyclic

theorem actual_galled_cap_root_skeleton_is_tree (hg : N.graph.GalledDetour)
    (b : N.graph.Blob) (hb : N.NonleafBlob b) :
    (N.actualEveryNonleafRootedCapSource b hb).rootSkeletonGraph.IsTree :=
  (N.actualEveryNonleafRootedCapSource b hb).actual_root_skeleton_is_tree
    (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb)
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_galled_cap_root_skeleton_is_tree
