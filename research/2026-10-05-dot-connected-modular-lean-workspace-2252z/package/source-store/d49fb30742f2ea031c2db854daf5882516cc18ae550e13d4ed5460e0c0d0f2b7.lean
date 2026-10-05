import G1SplicedOriginalSwitching

/-! Actual selected directed paths collapse/expand through the original
two-port splice. Every retained taxon descendant relation is preserved. -/
namespace G1SwitchingDescendantTransport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph
open G1SpliceDegrees G1SplicedSourceAdmission G1SplicedOriginalSwitching
open G1CutChildPorts
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

theorem actual_selected_edge_collapse (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (S : N.Switching) (e : S.Edge) :
    (restrictSwitching N hc b hb A S).graph.DReach
      (collapseVertex N b A (S.graph.source e)) (collapseVertex N b A (S.graph.target e)) := by
  by_cases he : e.val ∈ removedEdges N b A
  · have hm : e.val = A.entry ∨ e.val = A.child ∨ e.val = A.fragment.parents.parent0 ∨
        e.val = A.fragment.parents.parent1 := by
      simpa only [removedEdges,Finset.mem_insert,Finset.mem_singleton] using he
    change (restrictSwitching N hc b hb A S).graph.DReach
      (collapseVertex N b A (N.graph.source e.val)) (collapseVertex N b A (N.graph.target e.val))
    rcases hm with h | h | h | h
    · rw [h,A.entry_target,collapse_removed N b A _ (Or.inl rfl)]
      rw [show collapseVertex N b A (N.graph.source A.entry) = rootwardInterface N b A from
        collapse_kept N b A (rootwardInterface N b A)]
      exact .refl
    · rw [h,A.child_source,collapse_removed N b A _ (Or.inr rfl)]
      rw [show collapseVertex N b A (N.graph.target A.child) = descendantInterface N b A from
        collapse_kept N b A (descendantInterface N b A)]
      exact Relation.ReflTransGen.single ⟨⟨.inr (),True.intro⟩,rfl,rfl⟩
    · rw [h,A.fragment.parents.target0,
        show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false,
        collapse_removed N b A _ (Or.inl rfl),collapse_removed N b A _ (Or.inr rfl)]
      exact .refl
    · rw [h,A.fragment.parents.target1,
        show N.graph.source A.fragment.parents.parent1 = A.fragment.upper from A.fragment.arm_sources true,
        collapse_removed N b A _ (Or.inl rfl),collapse_removed N b A _ (Or.inr rfl)]
      exact .refl
  · let f : RetainedEdge N b A := ⟨e.val,he⟩
    change (restrictSwitching N hc b hb A S).graph.DReach
      (collapseVertex N b A (N.graph.source e.val)) (collapseVertex N b A (N.graph.target e.val))
    rw [show collapseVertex N b A (N.graph.source e.val) = retainedSource N hc b A f from
      collapse_kept N b A (retainedSource N hc b A f)]
    rw [show collapseVertex N b A (N.graph.target e.val) = retainedTarget N hc b A f from
      collapse_kept N b A (retainedTarget N hc b A f)]
    exact Relation.ReflTransGen.single ⟨⟨.inl f,e.property⟩,rfl,rfl⟩

theorem actual_selected_reach_collapse (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (S : N.Switching) {v w : V} (h : S.graph.DReach v w) :
    (restrictSwitching N hc b hb A S).graph.DReach (collapseVertex N b A v) (collapseVertex N b A w) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih =>
    obtain ⟨e,hs,ht⟩ := step
    have h := actual_selected_edge_collapse N hc b hb A S e
    rw [hs,ht] at h
    exact ih.trans h

lemma entry_kept (N : RootedBinary V E X) (hc : CutChild N) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (S : N.Switching) : S.keep A.entry := by
  apply S.ordinary
  intro hh
  have hin := (actual_upper_tree_degrees N hc b A).1
  have hhy := hh.1
  rw [A.entry_target,hin] at hhy
  omega

lemma child_kept (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (S : N.Switching) : S.keep A.child :=
  S.ordinary A.child (actual_child_target_not_hybrid N b A)

theorem actual_selected_spliced_edge_expansion (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (S : N.Switching) (e : (restrictSwitching N hc b hb A S).Edge) :
    S.graph.DReach ((restrictSwitching N hc b hb A S).graph.source e).val
      ((restrictSwitching N hc b hb A S).graph.target e).val := by
  rcases e with ⟨e,hkeep⟩
  cases e with
  | inl f => exact Relation.ReflTransGen.single ⟨⟨f.val,hkeep⟩,rfl,rfl⟩
  | inr u =>
    obtain ⟨p,ht,hp,_⟩ := S.hybrid_unique A.fragment.parents.hybrid A.fragment.parents.isHybrid
    have hs : N.graph.source p = A.fragment.upper := by
      rcases actual_hybrid_parents_exhaustive N b A p ht with he | he
      · rw [he]; exact A.fragment.arm_sources false
      · rw [he]; exact A.fragment.arm_sources true
    have hentry : S.graph.DStep (N.graph.source A.entry) A.fragment.upper :=
      ⟨⟨A.entry,entry_kept N hc b A S⟩,rfl,A.entry_target⟩
    have hparent : S.graph.DStep A.fragment.upper A.fragment.parents.hybrid := ⟨⟨p,hp⟩,hs,ht⟩
    have hchild : S.graph.DStep A.fragment.parents.hybrid (N.graph.target A.child) :=
      ⟨⟨A.child,child_kept N b A S⟩,A.child_source,rfl⟩
    exact (Relation.ReflTransGen.single hentry).trans
      ((Relation.ReflTransGen.single hparent).trans (Relation.ReflTransGen.single hchild))

theorem actual_selected_spliced_reach_expansion (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (S : N.Switching) {v w : SplicedVertex N b A}
    (h : (restrictSwitching N hc b hb A S).graph.DReach v w) : S.graph.DReach v.val w.val := by
  induction h with
  | refl => exact .refl
  | tail _ step ih =>
    obtain ⟨e,hs,ht⟩ := step
    have h := actual_selected_spliced_edge_expansion N hc b hb A S e
    rw [hs,ht] at h
    exact ih.trans h

theorem actual_retained_selected_descendants_iff (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (S : N.Switching) (v w : SplicedVertex N b A) :
    (restrictSwitching N hc b hb A S).graph.DReach v w ↔ S.graph.DReach v.val w.val := by
  constructor
  · exact actual_selected_spliced_reach_expansion N hc b hb A S
  · intro h
    have h := actual_selected_reach_collapse N hc b hb A S h
    rw [collapse_kept,collapse_kept] at h
    exact h

#print axioms actual_retained_selected_descendants_iff
end G1SwitchingDescendantTransport
