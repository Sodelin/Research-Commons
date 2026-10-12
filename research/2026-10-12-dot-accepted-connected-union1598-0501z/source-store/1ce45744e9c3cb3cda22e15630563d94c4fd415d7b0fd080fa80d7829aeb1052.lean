import G1ExtractedComponentProgram

/-!
# Exact original edge footprint of an extracted nonroot two-port blob

Contributor: dot, 2026-10-03. No other original edge enters or leaves its two
vertices. Both original external interfaces and both parallel arms are kept
distinct. These derived facts provide the graph-splice and causal-separator
input, rather than inserting the desired reduced graph as a source premise.
-/
namespace G1BigonFootprint
open Nanuq.Source G1CutChildPorts G1BlobDegreeBalance G1ActualTwoPortBlob G1ExtractedComponentProgram
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

theorem actual_upper_tree_degrees (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) :
    N.graph.inDegree A.fragment.upper = 1 ∧ N.graph.outDegree A.fragment.upper = 2 := by
  have hnotleaf : ∀ x : X, N.leaf x ≠ A.fragment.upper := by
    intro x hx
    exact N.no_edge_source_leaf x A.fragment.parents.parent0
      ((A.fragment.arm_sources false).trans hx.symm)
  rcases N.internal_degrees A.fragment.upper A.fragment.upper_nonroot hnotleaf with ht | hh
  · exact ht
  · have hcut : N.graph.IsBridge A.fragment.parents.parent0 := by
      apply hc
      rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false]
      exact hh
    exact False.elim (actual_hybrid_parent_nonbridge N A.fragment.parents.parent0
      (A.fragment.parents.target0 ▸ A.fragment.parents.isHybrid) hcut)

theorem actual_entry_unique (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : E)
    (ht : N.graph.target e = A.fragment.upper) : e = A.entry := by
  obtain ⟨f,_,hf⟩ := N.incoming_unique_of_indegree_one (actual_upper_tree_degrees N hc b A).1
  exact (hf e ht).trans (hf A.entry A.entry_target).symm

theorem actual_child_unique (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (e : E) (hs : N.graph.source e = A.fragment.parents.hybrid) : e = A.child := by
  obtain ⟨f,_,hf⟩ := hybrid_child_exists_unique N _ A.fragment.parents.isHybrid
  exact (hf e hs).trans (hf A.child A.child_source).symm

theorem actual_hybrid_parents_exhaustive (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (e : E) (ht : N.graph.target e = A.fragment.parents.hybrid) :
    e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
  let parents := Finset.univ.filter (fun f : E => N.graph.target f = A.fragment.parents.hybrid)
  apply edge_pair_exhaustive parents _ _ A.fragment.parents.different
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,A.fragment.parents.target0⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,A.fragment.parents.target1⟩)
    A.fragment.parents.isHybrid.1 e
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩

theorem actual_upper_children_exhaustive (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : E) (hs : N.graph.source e = A.fragment.upper) :
    e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
  let children := Finset.univ.filter (fun f : E => N.graph.source f = A.fragment.upper)
  apply edge_pair_exhaustive children _ _ A.fragment.parents.different
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,A.fragment.arm_sources false⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,A.fragment.arm_sources true⟩)
    (actual_upper_tree_degrees N hc b A).2 e
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩

noncomputable def removedEdges (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : Finset E :=
  {A.entry,A.child,A.fragment.parents.parent0,A.fragment.parents.parent1}

/-- Every retained original edge has both endpoints outside the two removed
vertices. This is derived from actual source degrees and extracted interfaces. -/
theorem actual_retained_edge_endpoints (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : E) (he : e ∉ removedEdges N b A) :
    (N.graph.source e ≠ A.fragment.upper ∧ N.graph.source e ≠ A.fragment.parents.hybrid) ∧
    (N.graph.target e ≠ A.fragment.upper ∧ N.graph.target e ≠ A.fragment.parents.hybrid) := by
  have hmembers : e ≠ A.entry ∧ e ≠ A.child ∧ e ≠ A.fragment.parents.parent0 ∧ e ≠ A.fragment.parents.parent1 := by
    simpa only [removedEdges,Finset.mem_insert,Finset.mem_singleton,not_or] using he
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro hs
    exact (actual_upper_children_exhaustive N hc b A e hs).elim hmembers.2.2.1 hmembers.2.2.2
  · intro hs
    exact hmembers.2.1 (actual_child_unique N b A e hs)
  · intro ht
    exact hmembers.1 (actual_entry_unique N hc b A e ht)
  · intro ht
    exact (actual_hybrid_parents_exhaustive N b A e ht).elim hmembers.2.2.1 hmembers.2.2.2

theorem actual_upper_hybrid_distinct (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : A.fragment.upper ≠ A.fragment.parents.hybrid := by
  intro h
  apply N.graph.acyclic_no_loop N.acyclic A.fragment.parents.parent0
  rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false,
    A.fragment.parents.target0,h]

theorem actual_external_interface_vertices (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) :
    (N.graph.source A.entry ≠ A.fragment.upper ∧ N.graph.source A.entry ≠ A.fragment.parents.hybrid) ∧
    (N.graph.target A.child ≠ A.fragment.upper ∧ N.graph.target A.child ≠ A.fragment.parents.hybrid) := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro h; exact A.entry_source_outside ((congrArg N.graph.blobOf h).trans A.upper_in_blob)
  · intro h; exact A.entry_source_outside ((congrArg N.graph.blobOf h).trans A.hybrid_in_blob)
  · intro h; exact A.child_target_outside ((congrArg N.graph.blobOf h).trans A.upper_in_blob)
  · intro h; exact A.child_target_outside ((congrArg N.graph.blobOf h).trans A.hybrid_in_blob)

theorem actual_root_vertex_retained (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    N.root ≠ A.fragment.upper ∧ N.root ≠ A.fragment.parents.hybrid := by
  refine ⟨?_,?_⟩
  · intro h; exact hb (A.upper_in_blob.symm.trans (congrArg N.graph.blobOf h).symm)
  · intro h; exact hb (A.hybrid_in_blob.symm.trans (congrArg N.graph.blobOf h).symm)

theorem actual_taxon_vertices_retained (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (x : X) :
    N.leaf x ≠ A.fragment.upper ∧ N.leaf x ≠ A.fragment.parents.hybrid := by
  refine ⟨?_,?_⟩
  · intro h; exact N.no_edge_source_leaf x A.fragment.parents.parent0
      ((A.fragment.arm_sources false).trans h.symm)
  · intro h; exact N.no_edge_source_leaf x A.child (A.child_source.trans h.symm)

theorem actual_entry_child_distinct (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : A.entry ≠ A.child := by
  intro h
  have hs : N.graph.source A.entry = A.fragment.parents.hybrid :=
    (congrArg N.graph.source h).trans A.child_source
  exact A.entry_source_outside ((congrArg N.graph.blobOf hs).trans A.hybrid_in_blob)

theorem actual_entry_parent0_distinct (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : A.entry ≠ A.fragment.parents.parent0 := by
  intro h
  exact actual_hybrid_parent_nonbridge N _ (A.fragment.parents.target0 ▸ A.fragment.parents.isHybrid)
    (h ▸ A.entry_bridge)

theorem actual_entry_parent1_distinct (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : A.entry ≠ A.fragment.parents.parent1 := by
  intro h
  exact actual_hybrid_parent_nonbridge N _ (A.fragment.parents.target1 ▸ A.fragment.parents.isHybrid)
    (h ▸ A.entry_bridge)

theorem actual_child_parent0_distinct (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : A.child ≠ A.fragment.parents.parent0 := by
  intro h
  exact actual_hybrid_parent_nonbridge N _ (A.fragment.parents.target0 ▸ A.fragment.parents.isHybrid)
    (h ▸ A.child_bridge)

theorem actual_child_parent1_distinct (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : A.child ≠ A.fragment.parents.parent1 := by
  intro h
  exact actual_hybrid_parent_nonbridge N _ (A.fragment.parents.target1 ▸ A.fragment.parents.isHybrid)
    (h ▸ A.child_bridge)

theorem actual_four_removed_edges (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : (removedEdges N b A).card = 4 := by
  simp [removedEdges,actual_entry_child_distinct N b A,actual_entry_parent0_distinct N b A,
    actual_entry_parent1_distinct N b A,actual_child_parent0_distinct N b A,
    actual_child_parent1_distinct N b A,A.fragment.parents.different]

end G1BigonFootprint
