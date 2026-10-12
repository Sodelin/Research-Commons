import G1BigonFootprint

/-!
# Constructed original graph splice for an extracted nonroot bigon

Contributor: dot, 2026-10-03. Removes its two actual internal vertices and four
actual incident edge IDs, inserting one new rootward-to-descendant edge. Every
retained vertex/edge and original taxon/root is preserved. Rooted reachability
and acyclicity are DERIVED by explicit original-path collapse/expansion.
Binary-degree, LSA, cut-child, root-blob, displayed-target and source-kernel
assembly are subsequent proofs, not fields smuggled into this construction.
-/
namespace G1BigonSpliceGraph
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1CutChildPorts G1BlobDegreeBalance G1ActualTwoPortBlob G1BigonFootprint
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

abbrev SplicedVertex (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b) :=
  {v : V // v ≠ A.fragment.upper ∧ v ≠ A.fragment.parents.hybrid}

abbrev RetainedEdge (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b) :=
  {e : E // e ∉ removedEdges N b A}

abbrev SplicedEdge (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b) :=
  RetainedEdge N b A ⊕ Unit

noncomputable instance splicedVertexFintype (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : Fintype (SplicedVertex N b A) := by
  unfold SplicedVertex; infer_instance

noncomputable instance retainedEdgeFintype (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : Fintype (RetainedEdge N b A) := by
  unfold RetainedEdge; infer_instance

noncomputable def rootwardInterface (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : SplicedVertex N b A :=
  ⟨N.graph.source A.entry,(actual_external_interface_vertices N b A).1⟩

noncomputable def descendantInterface (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : SplicedVertex N b A :=
  ⟨N.graph.target A.child,(actual_external_interface_vertices N b A).2⟩

noncomputable def retainedSource (N : RootedBinary V E X) (hc : CutChild N) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (e : RetainedEdge N b A) : SplicedVertex N b A :=
  ⟨N.graph.source e.val,(actual_retained_edge_endpoints N hc b A e.val e.property).1⟩

noncomputable def retainedTarget (N : RootedBinary V E X) (hc : CutChild N) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (e : RetainedEdge N b A) : SplicedVertex N b A :=
  ⟨N.graph.target e.val,(actual_retained_edge_endpoints N hc b A e.val e.property).2⟩

noncomputable def spliceGraph (N : RootedBinary V E X) (hc : CutChild N) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : EdgeGraph (SplicedVertex N b A) (SplicedEdge N b A) where
  source
    | .inl e => retainedSource N hc b A e
    | .inr _ => rootwardInterface N b A
  target
    | .inl e => retainedTarget N hc b A e
    | .inr _ => descendantInterface N b A

noncomputable def retainedRoot (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) : SplicedVertex N b A :=
  ⟨N.root,actual_root_vertex_retained N b hb A⟩

noncomputable def retainedTaxa (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : X ↪ SplicedVertex N b A where
  toFun x := ⟨N.leaf x,actual_taxon_vertices_retained N b A x⟩
  inj' x y h := N.leaf.injective (congrArg Subtype.val h)

/-- Removed internal vertices collapse to their original rootward exterior
endpoint. Original retained vertices, including all taxa/root, stay themselves. -/
noncomputable def collapseVertex (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (v : V) : SplicedVertex N b A :=
  if h : v = A.fragment.upper ∨ v = A.fragment.parents.hybrid then rootwardInterface N b A
  else ⟨v,not_or.mp h⟩

lemma collapse_kept (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (v : SplicedVertex N b A) : collapseVertex N b A v.val = v := by
  rw [collapseVertex,dif_neg (not_or.mpr v.property)]

lemma collapse_removed (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (v : V) (hv : v = A.fragment.upper ∨ v = A.fragment.parents.hybrid) :
    collapseVertex N b A v = rootwardInterface N b A := by
  rw [collapseVertex,dif_pos hv]

theorem actual_original_edge_collapse (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : E) :
    (spliceGraph N hc b A).DReach (collapseVertex N b A (N.graph.source e))
      (collapseVertex N b A (N.graph.target e)) := by
  by_cases he : e ∈ removedEdges N b A
  · have he : e = A.entry ∨ e = A.child ∨ e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
      simpa only [removedEdges,Finset.mem_insert,Finset.mem_singleton] using he
    rcases he with rfl | rfl | rfl | rfl
    · rw [A.entry_target,collapse_removed N b A _ (Or.inl rfl)]
      have hs := collapse_kept N b A (rootwardInterface N b A)
      change collapseVertex N b A (N.graph.source A.entry) = rootwardInterface N b A at hs
      rw [hs]
      exact .refl
    · rw [A.child_source,collapse_removed N b A _ (Or.inr rfl)]
      have ht := collapse_kept N b A (descendantInterface N b A)
      change collapseVertex N b A (N.graph.target A.child) = descendantInterface N b A at ht
      rw [ht]
      exact Relation.ReflTransGen.single ⟨Sum.inr (),rfl,rfl⟩
    · rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false,
        A.fragment.parents.target0,collapse_removed N b A _ (Or.inl rfl),collapse_removed N b A _ (Or.inr rfl)]
      exact .refl
    · rw [show N.graph.source A.fragment.parents.parent1 = A.fragment.upper from A.fragment.arm_sources true,
        A.fragment.parents.target1,collapse_removed N b A _ (Or.inl rfl),collapse_removed N b A _ (Or.inr rfl)]
      exact .refl
  · let e' : RetainedEdge N b A := ⟨e,he⟩
    have hs := collapse_kept N b A (retainedSource N hc b A e')
    have ht := collapse_kept N b A (retainedTarget N hc b A e')
    change collapseVertex N b A (N.graph.source e) = retainedSource N hc b A e' at hs
    change collapseVertex N b A (N.graph.target e) = retainedTarget N hc b A e' at ht
    rw [hs,ht]
    exact Relation.ReflTransGen.single ⟨Sum.inl e',rfl,rfl⟩

theorem actual_original_reach_collapse (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) {v w : V} (h : N.graph.DReach v w) :
    (spliceGraph N hc b A).DReach (collapseVertex N b A v) (collapseVertex N b A w) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      obtain ⟨e,hes,het⟩ := hstep
      have h := actual_original_edge_collapse N hc b A e
      rw [hes,het] at h
      exact ih.trans h

/-- Actual source-root reachability survives the constructed splice. -/
theorem actual_splice_rooted (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (v : SplicedVertex N b A) :
    (spliceGraph N hc b A).DReach (retainedRoot N b hb A) v := by
  have h := actual_original_reach_collapse N hc b A (N.rooted v.val)
  have hr := collapse_kept N b A (retainedRoot N b hb A)
  change collapseVertex N b A N.root = retainedRoot N b hb A at hr
  rw [hr,collapse_kept] at h
  exact h

theorem actual_spliced_edge_expansion (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : SplicedEdge N b A) :
    Relation.TransGen N.graph.DStep ((spliceGraph N hc b A).source e).val
      ((spliceGraph N hc b A).target e).val := by
  cases e with
  | inl e => exact Relation.TransGen.single ⟨e.val,rfl,rfl⟩
  | inr u =>
      have hentry : N.graph.DStep (N.graph.source A.entry) A.fragment.upper := ⟨A.entry,rfl,A.entry_target⟩
      have hparent : N.graph.DStep A.fragment.upper A.fragment.parents.hybrid :=
        ⟨A.fragment.parents.parent0,A.fragment.arm_sources false,A.fragment.parents.target0⟩
      have hchild : N.graph.DStep A.fragment.parents.hybrid (N.graph.target A.child) := ⟨A.child,A.child_source,rfl⟩
      exact (Relation.TransGen.single hentry).trans
        ((Relation.TransGen.single hparent).trans (Relation.TransGen.single hchild))

theorem actual_spliced_strict_reach_expansion (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) {v w : SplicedVertex N b A}
    (h : Relation.TransGen (spliceGraph N hc b A).DStep v w) :
    Relation.TransGen N.graph.DStep v.val w.val := by
  have edge : ∀ {v w : SplicedVertex N b A}, (spliceGraph N hc b A).DStep v w →
      Relation.TransGen N.graph.DStep v.val w.val := by
    intro v w hw
    obtain ⟨e,hes,het⟩ := hw
    have h := actual_spliced_edge_expansion N hc b A e
    rw [hes,het] at h
    exact h
  induction h with
  | single hstep => exact edge hstep
  | tail _ hstep ih => exact ih.trans (edge hstep)

/-- No cycle can be introduced: the new edge expands to a nonempty original
entry-parent-child directed path, and every old edge keeps its original ID. -/
theorem actual_splice_acyclic (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) : (spliceGraph N hc b A).Acyclic := by
  intro v hcycle
  exact N.acyclic v.val (actual_spliced_strict_reach_expansion N hc b A hcycle)

end G1BigonSpliceGraph
