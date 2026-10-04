import G1ReducedQuotientGeometry

/-! Derived reduced quotient/internal/hybrid budgets. Contributor: dot,
2026-10-03. All counts use actual original taxa, blob and bridge carriers. -/
namespace G1ReducedCoreCounts
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1CutChildPorts G1ReducedQuotientGeometry
open scoped Classical BigOperators
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

noncomputable def leafBlobs (N : RootedBinary V E X) : Finset N.graph.Blob :=
  Finset.univ.image N.blobLeaf
noncomputable def internalBlobs (N : RootedBinary V E X) : Finset N.graph.Blob :=
  Finset.univ.filter (fun b => b ≠ N.graph.blobOf N.root ∧ N.NonleafBlob b)
noncomputable def hybrids (N : RootedBinary V E X) : Finset V :=
  Finset.univ.filter N.graph.IsHybrid

lemma actual_leaf_blob_count (N : RootedBinary V E X) :
    (leafBlobs N).card = Fintype.card X := by
  rw [leafBlobs,Finset.card_image_of_injective _ N.blobLeaf.injective,Finset.card_univ]

lemma root_not_leaf_blob (N : RootedBinary V E X) :
    N.graph.blobOf N.root ∉ leafBlobs N := by
  intro h
  obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
  exact N.blob_leaf_ne_root x hx

lemma actual_blob_partition (N : RootedBinary V E X) :
    (Finset.univ : Finset N.graph.Blob) =
      {N.graph.blobOf N.root} ∪ leafBlobs N ∪ internalBlobs N := by
  ext b
  by_cases hr : b = N.graph.blobOf N.root
  · simp [hr]
  · by_cases hl : ∃ x : X, N.blobLeaf x = b
    · obtain ⟨x,hx⟩ := hl
      simp [leafBlobs,Finset.mem_image,← hx]
    · have hn : N.NonleafBlob b := fun x hx => hl ⟨x,hx⟩
      simp [internalBlobs,hr,hn]

lemma actual_blob_partition_disjoint (N : RootedBinary V E X) :
    Disjoint ({N.graph.blobOf N.root} ∪ leafBlobs N) (internalBlobs N) := by
  apply Finset.disjoint_left.mpr
  intro b hb hi
  have hi := (Finset.mem_filter.mp hi).2
  rcases Finset.mem_union.mp hb with hr | hl
  · exact hi.1 (Finset.mem_singleton.mp hr)
  · obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hl
    exact hi.2 x hx

lemma actual_total_blob_census (N : RootedBinary V E X) :
    Fintype.card N.graph.Blob = 1 + Fintype.card X + (internalBlobs N).card := by
  have hroot : Disjoint {N.graph.blobOf N.root} (leafBlobs N) := by
    simpa only [Finset.disjoint_singleton_left] using root_not_leaf_blob N
  have h := congrArg Finset.card (actual_blob_partition N)
  rwa [Finset.card_univ,Finset.card_union_of_disjoint (actual_blob_partition_disjoint N),
    Finset.card_union_of_disjoint hroot,Finset.card_singleton,actual_leaf_blob_count] at h

noncomputable def outPortEquiv (N : RootedBinary V E X) (b : N.graph.Blob) :
    (outPorts N b) ≃ {e : N.graph.BridgeEdge // N.graph.bridgeQuotient.source e = b} where
  toFun e := ⟨⟨e.val,(Finset.mem_filter.mp e.property).2.1⟩,(Finset.mem_filter.mp e.property).2.2⟩
  invFun e := ⟨e.val.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val.property,e.property⟩⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; apply Subtype.ext; rfl

lemma actual_outport_quotient_degree (N : RootedBinary V E X) (b : N.graph.Blob) :
    (outPorts N b).card = N.graph.bridgeQuotient.outDegree b := by
  simpa [Fintype.card_coe,Fintype.card_subtype,EdgeGraph.outDegree] using
    Fintype.card_congr (outPortEquiv N b)

lemma actual_total_outport_census (N : RootedBinary V E X) :
    (∑ b : N.graph.Blob, (outPorts N b).card) = Fintype.card N.graph.BridgeEdge := by
  simp_rw [actual_outport_quotient_degree]
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset N.graph.BridgeEdge)
    (Finset.univ : Finset N.graph.Blob) N.graph.bridgeQuotient.source
  simpa [EdgeGraph.outDegree] using h

/-- The quotient internal-count budget is forced by root branching and all
nonroot internal outdegree>=2 after literal two-port elimination. -/
theorem actual_reduced_internal_blob_budget (N : RootedBinary V E X)
    (hr : ∀ b : N.graph.Blob, b ≠ N.graph.blobOf N.root → Fintype.card (N.BlobPort b) ≠ 2) :
    (internalBlobs N).card + 2 ≤ Fintype.card X := by
  have hsum : 2 + 2 * (internalBlobs N).card ≤
      ∑ b : N.graph.Blob, (outPorts N b).card := by
    have hroot := actual_root_blob_outports_two N
    have hi : 2 * (internalBlobs N).card ≤ ∑ b ∈ internalBlobs N, (outPorts N b).card := by
      have h := Finset.sum_le_sum (s := internalBlobs N) (f := fun _ => 2)
        (g := fun b => (outPorts N b).card) (fun b hb =>
          let hp := (Finset.mem_filter.mp hb).2
          actual_reduced_nonroot_branching N hr b hp.1 hp.2)
      simpa [Nat.mul_comm] using h
    have hs : {N.graph.blobOf N.root} ∪ internalBlobs N ⊆ (Finset.univ : Finset N.graph.Blob) :=
      Finset.subset_univ _
    have hd : Disjoint {N.graph.blobOf N.root} (internalBlobs N) := by
      apply Finset.disjoint_left.mpr
      intro b hb hi
      exact (Finset.mem_filter.mp hi).2.1 (Finset.mem_singleton.mp hb)
    have hc := Finset.sum_le_sum_of_subset_of_nonneg (f := fun b => (outPorts N b).card) hs (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_union hd,Finset.sum_singleton] at hc
    exact (Nat.add_le_add hroot hi).trans hc
  have hc := actual_bridge_blob_census N
  have hb := actual_total_blob_census N
  rw [actual_total_outport_census] at hsum
  omega

noncomputable def hybridBridge (N : RootedBinary V E X) (hc : CutChild N) :
    hybrids N → N.graph.BridgeEdge := fun h =>
  let hh := (Finset.mem_filter.mp h.property).2
  ⟨hybridChild N h.val hh,hc _ (by rw [hybridChild_source]; exact hh)⟩

lemma actual_hybrid_bridge_injective (N : RootedBinary V E X) (hc : CutChild N) :
    Function.Injective (hybridBridge N hc) := by
  intro h k he
  apply Subtype.ext
  have hs := congrArg (fun e : N.graph.BridgeEdge => N.graph.source e.val) he
  simpa only [hybridBridge,hybridChild_source] using hs

/-- Global hybrid bound for the ACTUAL reduced cut-child source graph. -/
theorem actual_reduced_hybrid_budget (N : RootedBinary V E X) (hc : CutChild N)
    (hr : ∀ b : N.graph.Blob, b ≠ N.graph.blobOf N.root → Fintype.card (N.BlobPort b) ≠ 2) :
    (hybrids N).card + 2 ≤ 2 * Fintype.card X := by
  have hh := Fintype.card_le_of_injective (hybridBridge N hc) (actual_hybrid_bridge_injective N hc)
  simp only [Fintype.card_coe] at hh
  have hi := actual_reduced_internal_blob_budget N hr
  have hb := actual_total_blob_census N
  have he := actual_bridge_blob_census N
  omega

end G1ReducedCoreCounts
