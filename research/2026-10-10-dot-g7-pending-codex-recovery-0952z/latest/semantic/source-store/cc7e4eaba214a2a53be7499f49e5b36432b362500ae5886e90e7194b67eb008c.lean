import G1SpliceRootBlob

/-!
# Actual binary-degree preservation at every retained splice vertex

Contributor: dot, 2026-10-03. Original incident edge IDs are bijected to the
constructed core incident edges. Only the entering edge at its original source
and the child edge at its original target are renamed to the synthetic edge.
All other incident IDs remain unchanged. Degree preservation is derived.
-/
namespace G1SpliceDegrees
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph G1SpliceCutTransport
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_out_edge_kept_of_ne_entry (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A)
    (e : E) (hs : N.graph.source e = v.val) (hne : e ≠ A.entry) : e ∉ removedEdges N b A := by
  intro hm
  have hm : e = A.entry ∨ e = A.child ∨ e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
    simpa only [removedEdges,Finset.mem_insert,Finset.mem_singleton] using hm
  rcases hm with h | rfl | rfl | rfl
  · exact hne h
  · exact v.property.2 (hs.symm.trans A.child_source)
  · exact v.property.1 (hs.symm.trans (A.fragment.arm_sources false))
  · exact v.property.1 (hs.symm.trans (A.fragment.arm_sources true))

lemma actual_in_edge_kept_of_ne_child (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A)
    (e : E) (ht : N.graph.target e = v.val) (hne : e ≠ A.child) : e ∉ removedEdges N b A := by
  intro hm
  have hm : e = A.entry ∨ e = A.child ∨ e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
    simpa only [removedEdges,Finset.mem_insert,Finset.mem_singleton] using hm
  rcases hm with rfl | h | rfl | rfl
  · exact v.property.1 (ht.symm.trans A.entry_target)
  · exact hne h
  · exact v.property.2 (ht.symm.trans A.fragment.parents.target0)
  · exact v.property.2 (ht.symm.trans A.fragment.parents.target1)

noncomputable def outDestination (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A)
    (e : {e : E // N.graph.source e = v.val}) : SplicedEdge N b A :=
  if he : e.val = A.entry then .inr () else
    .inl ⟨e.val,actual_out_edge_kept_of_ne_entry N hc b A v e.val e.property he⟩

lemma outDestination_source (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A)
    (e : {e : E // N.graph.source e = v.val}) : (spliceGraph N hc b A).source (outDestination N hc b A v e) = v := by
  unfold outDestination
  split_ifs with he
  · apply Subtype.ext
    change N.graph.source A.entry = v.val
    have hs := e.property
    rw [he] at hs
    exact hs
  · apply Subtype.ext
    exact e.property

noncomputable def outEdgeMap (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    {e : E // N.graph.source e = v.val} → {e : SplicedEdge N b A // (spliceGraph N hc b A).source e = v} :=
  fun e => ⟨outDestination N hc b A v e,outDestination_source N hc b A v e⟩

theorem actual_out_map_injective (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    Function.Injective (outEdgeMap N hc b A v) := by
  intro e f h
  have h := congrArg Subtype.val h
  change outDestination N hc b A v e = outDestination N hc b A v f at h
  by_cases he : e.val = A.entry <;> by_cases hf : f.val = A.entry
  · exact Subtype.ext (he.trans hf.symm)
  · simp only [outDestination,dif_pos he,dif_neg hf] at h
    cases h
  · simp only [outDestination,dif_neg he,dif_pos hf] at h
    cases h
  · simp only [outDestination,dif_neg he,dif_neg hf] at h
    have hh : e.val = f.val := congrArg (fun g : RetainedEdge N b A => g.val) (Sum.inl.inj h)
    exact Subtype.ext hh

theorem actual_out_map_surjective (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    Function.Surjective (outEdgeMap N hc b A v) := by
  rintro ⟨e,hs⟩
  cases e with
  | inl e =>
      have hsrc : N.graph.source e.val = v.val := congrArg Subtype.val hs
      let f : {e : E // N.graph.source e = v.val} := ⟨e.val,hsrc⟩
      have hne : e.val ≠ A.entry := (retained_not_removed N b A e A.entry (by simp [removedEdges])).symm
      refine ⟨f,?_⟩
      apply Subtype.ext
      dsimp only [outEdgeMap]
      rw [outDestination,dif_neg hne]
  | inr u =>
      cases u
      have hsrc : N.graph.source A.entry = v.val := congrArg Subtype.val hs
      refine ⟨⟨A.entry,hsrc⟩,?_⟩
      apply Subtype.ext
      simp [outEdgeMap,outDestination]

noncomputable def actualOutEdgeEquiv (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    {e : E // N.graph.source e = v.val} ≃ {e : SplicedEdge N b A // (spliceGraph N hc b A).source e = v} :=
  Equiv.ofBijective (outEdgeMap N hc b A v) ⟨actual_out_map_injective N hc b A v,actual_out_map_surjective N hc b A v⟩

theorem actual_splice_outdegree (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    (spliceGraph N hc b A).outDegree v = N.graph.outDegree v.val := by
  have h := Fintype.card_congr (actualOutEdgeEquiv N hc b A v)
  simpa only [Fintype.card_subtype,EdgeGraph.outDegree] using h.symm

noncomputable def inDestination (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A)
    (e : {e : E // N.graph.target e = v.val}) : SplicedEdge N b A :=
  if he : e.val = A.child then .inr () else
    .inl ⟨e.val,actual_in_edge_kept_of_ne_child N hc b A v e.val e.property he⟩

lemma inDestination_target (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A)
    (e : {e : E // N.graph.target e = v.val}) : (spliceGraph N hc b A).target (inDestination N hc b A v e) = v := by
  unfold inDestination
  split_ifs with he
  · apply Subtype.ext
    change N.graph.target A.child = v.val
    have ht := e.property
    rw [he] at ht
    exact ht
  · apply Subtype.ext
    exact e.property

noncomputable def inEdgeMap (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    {e : E // N.graph.target e = v.val} → {e : SplicedEdge N b A // (spliceGraph N hc b A).target e = v} :=
  fun e => ⟨inDestination N hc b A v e,inDestination_target N hc b A v e⟩

theorem actual_in_map_injective (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    Function.Injective (inEdgeMap N hc b A v) := by
  intro e f h
  have h := congrArg Subtype.val h
  change inDestination N hc b A v e = inDestination N hc b A v f at h
  by_cases he : e.val = A.child <;> by_cases hf : f.val = A.child
  · exact Subtype.ext (he.trans hf.symm)
  · simp only [inDestination,dif_pos he,dif_neg hf] at h
    cases h
  · simp only [inDestination,dif_neg he,dif_pos hf] at h
    cases h
  · simp only [inDestination,dif_neg he,dif_neg hf] at h
    have hh : e.val = f.val := congrArg (fun g : RetainedEdge N b A => g.val) (Sum.inl.inj h)
    exact Subtype.ext hh

theorem actual_in_map_surjective (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    Function.Surjective (inEdgeMap N hc b A v) := by
  rintro ⟨e,ht⟩
  cases e with
  | inl e =>
      have htarget : N.graph.target e.val = v.val := congrArg Subtype.val ht
      let f : {e : E // N.graph.target e = v.val} := ⟨e.val,htarget⟩
      have hne : e.val ≠ A.child := (retained_not_removed N b A e A.child (by simp [removedEdges])).symm
      refine ⟨f,?_⟩
      apply Subtype.ext
      dsimp only [inEdgeMap]
      rw [inDestination,dif_neg hne]
  | inr u =>
      cases u
      have htarget : N.graph.target A.child = v.val := congrArg Subtype.val ht
      refine ⟨⟨A.child,htarget⟩,?_⟩
      apply Subtype.ext
      simp [inEdgeMap,inDestination]

noncomputable def actualInEdgeEquiv (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    {e : E // N.graph.target e = v.val} ≃ {e : SplicedEdge N b A // (spliceGraph N hc b A).target e = v} :=
  Equiv.ofBijective (inEdgeMap N hc b A v) ⟨actual_in_map_injective N hc b A v,actual_in_map_surjective N hc b A v⟩

theorem actual_splice_indegree (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    (spliceGraph N hc b A).inDegree v = N.graph.inDegree v.val := by
  have h := Fintype.card_congr (actualInEdgeEquiv N hc b A v)
  simpa only [Fintype.card_subtype,EdgeGraph.inDegree] using h.symm

theorem actual_splice_hybrid_iff (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : SplicedVertex N b A) :
    (spliceGraph N hc b A).IsHybrid v ↔ N.graph.IsHybrid v.val := by
  simp only [EdgeGraph.IsHybrid,actual_splice_indegree,actual_splice_outdegree]

end G1SpliceDegrees
