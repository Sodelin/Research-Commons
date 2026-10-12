import G1BigonSpliceGraph

/-!
# Actual bridge transport through the constructed G1 splice

Contributor: dot, 2026-10-03. Every retained original edge keeps exactly its
bridge status; the new decorated interface edge is derived to be a bridge.
Original/core detours are explicitly collapsed/lifted without the forbidden
original edge. No core cut/decomposition assertion is supplied as a field.
-/
namespace G1SpliceCutTransport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma retained_not_removed (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (e : RetainedEdge N b A) (f : E) (hf : f ∈ removedEdges N b A) : f ≠ e.val := by
  intro h
  exact e.property (h ▸ hf)

theorem actual_original_edge_without_collapse (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : RetainedEdge N b A)
    (f : E) (hf : f ≠ e.val) :
    (spliceGraph N hc b A).ReachWithout (.inl e) (collapseVertex N b A (N.graph.source f))
      (collapseVertex N b A (N.graph.target f)) := by
  by_cases hkeep : f ∉ removedEdges N b A
  · let f' : RetainedEdge N b A := ⟨f,hkeep⟩
    have hs := collapse_kept N b A (retainedSource N hc b A f')
    have ht := collapse_kept N b A (retainedTarget N hc b A f')
    change collapseVertex N b A (N.graph.source f) = retainedSource N hc b A f' at hs
    change collapseVertex N b A (N.graph.target f) = retainedTarget N hc b A f' at ht
    rw [hs,ht]
    refine (spliceGraph N hc b A).ureach_single ⟨Sum.inl f',?_,Or.inl ⟨rfl,rfl⟩⟩
    intro h
    exact hf (congrArg Subtype.val (Sum.inl.inj h))
  · have hm : f ∈ removedEdges N b A := not_not.mp hkeep
    have hm : f = A.entry ∨ f = A.child ∨ f = A.fragment.parents.parent0 ∨ f = A.fragment.parents.parent1 := by
      simpa only [removedEdges,Finset.mem_insert,Finset.mem_singleton] using hm
    rcases hm with rfl | rfl | rfl | rfl
    · rw [A.entry_target,collapse_removed N b A _ (Or.inl rfl)]
      have hs := collapse_kept N b A (rootwardInterface N b A)
      change collapseVertex N b A (N.graph.source A.entry) = rootwardInterface N b A at hs
      rw [hs]; exact .refl
    · rw [A.child_source,collapse_removed N b A _ (Or.inr rfl)]
      have ht := collapse_kept N b A (descendantInterface N b A)
      change collapseVertex N b A (N.graph.target A.child) = descendantInterface N b A at ht
      rw [ht]
      refine (spliceGraph N hc b A).ureach_single ⟨Sum.inr (),?_⟩
      constructor
      · intro h; cases h
      · exact Or.inl ⟨rfl,rfl⟩
    · rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false,
        A.fragment.parents.target0,collapse_removed N b A _ (Or.inl rfl),collapse_removed N b A _ (Or.inr rfl)]
      exact .refl
    · rw [show N.graph.source A.fragment.parents.parent1 = A.fragment.upper from A.fragment.arm_sources true,
        A.fragment.parents.target1,collapse_removed N b A _ (Or.inl rfl),collapse_removed N b A _ (Or.inr rfl)]
      exact .refl

theorem actual_original_without_collapse (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : RetainedEdge N b A) {v w : V}
    (h : N.graph.ReachWithout e.val v w) :
    (spliceGraph N hc b A).ReachWithout (.inl e) (collapseVertex N b A v) (collapseVertex N b A w) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      obtain ⟨f,hf,hinc⟩ := hstep
      have h := actual_original_edge_without_collapse N hc b A e f hf
      rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · rw [hs,ht] at h; exact ih.trans h
      · rw [hs,ht] at h; exact ih.trans ((spliceGraph N hc b A).ureach_symm h)

theorem actual_core_edge_without_expansion (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : RetainedEdge N b A)
    (f : SplicedEdge N b A) (hf : f ≠ .inl e) :
    N.graph.ReachWithout e.val ((spliceGraph N hc b A).source f).val
      ((spliceGraph N hc b A).target f).val := by
  cases f with
  | inl f =>
      refine N.graph.ureach_single ⟨f.val,?_,N.graph.inc_source_target f.val⟩
      intro h
      exact hf (congrArg Sum.inl (Subtype.ext h))
  | inr u =>
      have he : A.entry ≠ e.val := retained_not_removed N b A e A.entry (by simp [removedEdges])
      have hp : A.fragment.parents.parent0 ≠ e.val := retained_not_removed N b A e _ (by simp [removedEdges])
      have hd : A.child ≠ e.val := retained_not_removed N b A e A.child (by simp [removedEdges])
      have epath : N.graph.ReachWithout e.val (N.graph.source A.entry) A.fragment.upper :=
        N.graph.ureach_single ⟨A.entry,he,Or.inl ⟨rfl,A.entry_target⟩⟩
      have ppath : N.graph.ReachWithout e.val A.fragment.upper A.fragment.parents.hybrid :=
        N.graph.ureach_single ⟨A.fragment.parents.parent0,hp,
          Or.inl ⟨A.fragment.arm_sources false,A.fragment.parents.target0⟩⟩
      have dpath : N.graph.ReachWithout e.val A.fragment.parents.hybrid (N.graph.target A.child) :=
        N.graph.ureach_single ⟨A.child,hd,Or.inl ⟨A.child_source,rfl⟩⟩
      exact epath.trans (ppath.trans dpath)

theorem actual_core_without_expansion (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : RetainedEdge N b A)
    {v w : SplicedVertex N b A} (h : (spliceGraph N hc b A).ReachWithout (.inl e) v w) :
    N.graph.ReachWithout e.val v.val w.val := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      obtain ⟨f,hf,hinc⟩ := hstep
      have h := actual_core_edge_without_expansion N hc b A e f hf
      rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · rw [hs,ht] at h; exact ih.trans h
      · rw [hs,ht] at h; exact ih.trans (N.graph.ureach_symm h)

/-- Every retained original arc preserves its actual cut status exactly. -/
theorem actual_retained_bridge_iff (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : RetainedEdge N b A) :
    (spliceGraph N hc b A).IsBridge (.inl e) ↔ N.graph.IsBridge e.val := by
  constructor
  · intro hcore hold
    have h := actual_original_without_collapse N hc b A e hold
    have hs := collapse_kept N b A (retainedSource N hc b A e)
    have ht := collapse_kept N b A (retainedTarget N hc b A e)
    change collapseVertex N b A (N.graph.source e.val) = retainedSource N hc b A e at hs
    change collapseVertex N b A (N.graph.target e.val) = retainedTarget N hc b A e at ht
    rw [hs,ht] at h
    exact hcore h
  · intro hold hcore
    exact hold (actual_core_without_expansion N hc b A e hcore)

lemma actual_core_without_new_lift (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) {v w : SplicedVertex N b A}
    (h : (spliceGraph N hc b A).ReachWithout (.inr ()) v w) : N.graph.ReachWithout A.entry v.val w.val := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      obtain ⟨f,hf,hinc⟩ := hstep
      cases f with
      | inr u => cases u; exact False.elim (hf rfl)
      | inl f =>
          have hfe : f.val ≠ A.entry := Ne.symm (retained_not_removed N b A f A.entry (by simp [removedEdges]))
          rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
          · exact ih.tail ⟨f.val,hfe,Or.inl ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩⟩
          · exact ih.tail ⟨f.val,hfe,Or.inr ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩⟩

/-- The new decorated interface edge is an actual cut edge, derived from the
original entering cut and the exact isolated component footprint. -/
theorem actual_new_edge_bridge (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) : (spliceGraph N hc b A).IsBridge (.inr ()) := by
  intro hdetour
  have h := actual_core_without_new_lift N hc b A hdetour
  have hcpath : N.graph.ReachWithout A.entry (N.graph.target A.child) A.fragment.parents.hybrid :=
    N.graph.ureach_single ⟨A.child,(actual_entry_child_distinct N b A).symm,Or.inr ⟨A.child_source,rfl⟩⟩
  have hppath : N.graph.ReachWithout A.entry A.fragment.parents.hybrid A.fragment.upper :=
    N.graph.ureach_single ⟨A.fragment.parents.parent0,(actual_entry_parent0_distinct N b A).symm,
      Or.inr ⟨A.fragment.arm_sources false,A.fragment.parents.target0⟩⟩
  apply A.entry_bridge
  rw [A.entry_target]
  exact h.trans (hcpath.trans hppath)

end G1SpliceCutTransport
