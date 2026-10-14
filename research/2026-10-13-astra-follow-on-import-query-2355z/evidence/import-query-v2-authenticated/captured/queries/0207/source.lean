import G1SpliceCutTransport

/-!
# Exact original root-containing blob preservation under the graph splice

Contributor: dot, 2026-10-03. Actual bridge-deletion connectivity is equivalent
on all retained vertices. Every original root-blob vertex and internal edge
survives with its original ID; no synthetic edge enters that blob. This proves
the entire graph-blob retention previously left beyond the no-.root-operation
word statement. Stochastic exterior/interpreter binding remains separate.
-/
namespace G1SpliceRootBlob
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph G1SpliceCutTransport
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_original_nonbridge_collapse (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (f : E) (hf : ¬ N.graph.IsBridge f) :
    (spliceGraph N hc b A).SameBlob (collapseVertex N b A (N.graph.source f))
      (collapseVertex N b A (N.graph.target f)) := by
  by_cases hkeep : f ∉ removedEdges N b A
  · let f' : RetainedEdge N b A := ⟨f,hkeep⟩
    have hcore : ¬ (spliceGraph N hc b A).IsBridge (.inl f') := by
      intro h
      exact hf ((actual_retained_bridge_iff N hc b A f').mp h)
    have hs := collapse_kept N b A (retainedSource N hc b A f')
    have ht := collapse_kept N b A (retainedTarget N hc b A f')
    change collapseVertex N b A (N.graph.source f) = retainedSource N hc b A f' at hs
    change collapseVertex N b A (N.graph.target f) = retainedTarget N hc b A f' at ht
    rw [hs,ht]
    exact (spliceGraph N hc b A).nonbridge_sameBlob hcore
  · have hm : f ∈ removedEdges N b A := not_not.mp hkeep
    have hm : f = A.entry ∨ f = A.child ∨ f = A.fragment.parents.parent0 ∨ f = A.fragment.parents.parent1 := by
      simpa only [removedEdges,Finset.mem_insert,Finset.mem_singleton] using hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact False.elim (hf A.entry_bridge)
    · exact False.elim (hf A.child_bridge)
    · rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false,
        A.fragment.parents.target0,collapse_removed N b A _ (Or.inl rfl),collapse_removed N b A _ (Or.inr rfl)]
      exact .refl
    · rw [show N.graph.source A.fragment.parents.parent1 = A.fragment.upper from A.fragment.arm_sources true,
        A.fragment.parents.target1,collapse_removed N b A _ (Or.inl rfl),collapse_removed N b A _ (Or.inr rfl)]
      exact .refl

theorem actual_original_sameBlob_collapse (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) {v w : V} (h : N.graph.SameBlob v w) :
    (spliceGraph N hc b A).SameBlob (collapseVertex N b A v) (collapseVertex N b A w) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      obtain ⟨f,hf,hinc⟩ := hstep
      have h := actual_original_nonbridge_collapse N hc b A f hf
      rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · rw [hs,ht] at h; exact ih.trans h
      · rw [hs,ht] at h; exact ih.trans ((spliceGraph N hc b A).sameBlob_symm h)

theorem actual_core_sameBlob_expansion (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) {v w : SplicedVertex N b A}
    (h : (spliceGraph N hc b A).SameBlob v w) : N.graph.SameBlob v.val w.val := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      obtain ⟨f,hf,hinc⟩ := hstep
      cases f with
      | inr u => cases u; exact False.elim (hf (actual_new_edge_bridge N hc b A))
      | inl f =>
          have hold : ¬ N.graph.IsBridge f.val := by
            intro h; exact hf ((actual_retained_bridge_iff N hc b A f).mpr h)
          rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
          · exact ih.tail ⟨f.val,hold,Or.inl ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩⟩
          · exact ih.tail ⟨f.val,hold,Or.inr ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩⟩

/-- Exact original/core blob membership on every retained vertex pair. -/
theorem actual_kept_sameBlob_iff (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v w : SplicedVertex N b A) :
    (spliceGraph N hc b A).SameBlob v w ↔ N.graph.SameBlob v.val w.val := by
  constructor
  · exact actual_core_sameBlob_expansion N hc b A
  · intro h
    have h := actual_original_sameBlob_collapse N hc b A h
    rw [collapse_kept,collapse_kept] at h
    exact h

theorem actual_original_root_blob_vertex_kept (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) (v : V)
    (hv : N.graph.SameBlob N.root v) : v ≠ A.fragment.upper ∧ v ≠ A.fragment.parents.hybrid := by
  have hvb : N.graph.blobOf N.root = N.graph.blobOf v := Quotient.sound hv
  refine ⟨?_,?_⟩
  · intro h; exact hb (hvb.trans ((congrArg N.graph.blobOf h).trans A.upper_in_blob)).symm
  · intro h; exact hb (hvb.trans ((congrArg N.graph.blobOf h).trans A.hybrid_in_blob)).symm

/-- An actual vertex-by-vertex equivalence of the whole original root blob,
including nonroot vertices that belong to that blob. No root-vertex shortcut. -/
noncomputable def actualRootBlobVertexEquiv (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    {v : V // N.graph.SameBlob N.root v} ≃
      {v : SplicedVertex N b A // (spliceGraph N hc b A).SameBlob (retainedRoot N b hb A) v} where
  toFun v := by
    let w : SplicedVertex N b A := ⟨v.val,actual_original_root_blob_vertex_kept N b hb A v.val v.property⟩
    exact ⟨w,(actual_kept_sameBlob_iff N hc b A _ w).mpr v.property⟩
  invFun v := ⟨v.val.val,(actual_kept_sameBlob_iff N hc b A _ v.val).mp v.property⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Every original internal root-blob edge is retained with the SAME original
edge ID. Both endpoint memberships and both original bridge exclusions matter. -/
theorem actual_original_root_blob_edge_kept (N : RootedBinary V E X) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) (e : E)
    (hs : N.graph.SameBlob N.root (N.graph.source e))
    (ht : N.graph.SameBlob N.root (N.graph.target e)) : e ∉ removedEdges N b A := by
  intro hm
  have hm : e = A.entry ∨ e = A.child ∨ e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
    simpa only [removedEdges,Finset.mem_insert,Finset.mem_singleton] using hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact N.graph.bridge_not_sameBlob A.entry_bridge ((N.graph.sameBlob_symm hs).trans ht)
  · exact N.graph.bridge_not_sameBlob A.child_bridge ((N.graph.sameBlob_symm hs).trans ht)
  · have hkeep := actual_original_root_blob_vertex_kept N b hb A _ hs
    exact hkeep.1 (A.fragment.arm_sources false)
  · have hkeep := actual_original_root_blob_vertex_kept N b hb A _ hs
    exact hkeep.1 (A.fragment.arm_sources true)

/-- No newly introduced edge is internal to the preserved root blob. -/
theorem actual_new_edge_not_in_root_blob (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    ¬ ((spliceGraph N hc b A).SameBlob (retainedRoot N b hb A) (rootwardInterface N b A) ∧
       (spliceGraph N hc b A).SameBlob (retainedRoot N b hb A) (descendantInterface N b A)) := by
  rintro ⟨hs,ht⟩
  exact (spliceGraph N hc b A).bridge_not_sameBlob (actual_new_edge_bridge N hc b A)
    (((spliceGraph N hc b A).sameBlob_symm hs).trans ht)

end G1SpliceRootBlob
