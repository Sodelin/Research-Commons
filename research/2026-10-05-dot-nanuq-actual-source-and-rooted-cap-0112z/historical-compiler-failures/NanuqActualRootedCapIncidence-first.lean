import NanuqActualRootedCapBoundary

/-! Exact incoming/outgoing occurrence transport for the literal raw cap.
These maps replace crossing bridge occurrences, rather than identifying
parallel original arcs or supplying a capped-source degree certificate. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem original_arc_leaving_blob_bridge (b : N.graph.Blob) (e : E)
    (hs : N.graph.blobOf (N.graph.source e) = b)
    (ht : N.graph.blobOf (N.graph.target e) ≠ b) : N.graph.IsBridge e := by
  by_contra he
  exact ht ((Quotient.sound (N.graph.nonbridge_sameBlob he)).symm.trans hs)

theorem original_arc_entering_blob_bridge (b : N.graph.Blob) (e : E)
    (ht : N.graph.blobOf (N.graph.target e) = b)
    (hs : N.graph.blobOf (N.graph.source e) ≠ b) : N.graph.IsBridge e := by
  by_contra he
  exact hs ((Quotient.sound (N.graph.nonbridge_sameBlob he)).trans ht)

theorem original_arc_entering_blob_nonroot (b : N.graph.Blob) (e : E)
    (ht : N.graph.blobOf (N.graph.target e) = b)
    (hs : N.graph.blobOf (N.graph.source e) ≠ b) : b ≠ N.graph.blobOf N.root := by
  intro h
  exact N.original_root_blob_has_no_incoming_port
    ⟨e,N.original_arc_entering_blob_bridge b e ht hs⟩ (ht.trans h)

theorem original_arc_entering_blob_identity (b : N.graph.Blob) (e : E)
    (ht : N.graph.blobOf (N.graph.target e) = b)
    (hs : N.graph.blobOf (N.graph.source e) ≠ b)
    (hn : b ≠ N.graph.blobOf N.root) :
    e = (N.originalIncomingBlobPort b hn).val.val := by
  have he := N.original_arc_entering_blob_bridge b e ht hs
  let p : N.BlobPort b := ⟨⟨e,he⟩,Or.inr ht⟩
  exact congrArg (fun p : N.BlobPort b => p.val.val)
    (N.original_incoming_port_unique b p (N.originalIncomingBlobPort b hn)
      ht (N.originalIncomingBlobPort_target b hn))

noncomputable def actualRootedCapOutArc (b : N.graph.Blob) (e : E)
    (hs : N.graph.blobOf (N.graph.source e) = b) : N.RootedCapArc b :=
  if ht : N.graph.blobOf (N.graph.target e) = b then Sum.inl ⟨e,hs,ht⟩
  else Sum.inr (Sum.inl ⟨⟨e,N.original_arc_leaving_blob_bridge b e hs ht⟩,Or.inl hs⟩)

noncomputable def actualRootedCapInArc (b : N.graph.Blob) (e : E)
    (ht : N.graph.blobOf (N.graph.target e) = b) : N.RootedCapArc b :=
  if hs : N.graph.blobOf (N.graph.source e) = b then Sum.inl ⟨e,hs,ht⟩
  else Sum.inr (Sum.inr ⟨(),N.original_arc_entering_blob_nonroot b e ht hs⟩)

noncomputable def actualRootedCapOriginalArc (b : N.graph.Blob) : N.RootedCapArc b → E :=
  Sum.elim Subtype.val (Sum.elim (fun p => p.val.val)
    (fun t => (N.originalIncomingBlobPort b t.property).val.val))

theorem actualRootedCapOutArc_source (b : N.graph.Blob) (e : E)
    (hs : N.graph.blobOf (N.graph.source e) = b) :
    (N.actualRootedCapGraph b).source (N.actualRootedCapOutArc b e hs) =
      Sum.inl ⟨N.graph.source e,hs⟩ := by
  unfold actualRootedCapOutArc
  split
  · rfl
  · simp only [actualRootedCapGraph,Sum.elim_inr,Sum.elim_inl,hs,if_pos]
    apply congrArg Sum.inl
    apply Subtype.ext
    exact N.originalPortInner_value_outgoing b _ hs

theorem actualRootedCapInArc_target (b : N.graph.Blob) (e : E)
    (ht : N.graph.blobOf (N.graph.target e) = b) :
    (N.actualRootedCapGraph b).target (N.actualRootedCapInArc b e ht) =
      Sum.inl ⟨N.graph.target e,ht⟩ := by
  unfold actualRootedCapInArc
  split
  · rfl
  · apply congrArg Sum.inl
    apply Subtype.ext
    rw [N.originalRootedCapEntry_nonroot_value b]
    exact congrArg N.graph.target
      (N.original_arc_entering_blob_identity b e ht (by assumption) (by assumption)).symm

theorem actualRootedCapOutArc_original (b : N.graph.Blob) (e : E)
    (hs : N.graph.blobOf (N.graph.source e) = b) :
    N.actualRootedCapOriginalArc b (N.actualRootedCapOutArc b e hs) = e := by
  unfold actualRootedCapOutArc
  split <;> rfl

theorem actualRootedCapInArc_original (b : N.graph.Blob) (e : E)
    (ht : N.graph.blobOf (N.graph.target e) = b) :
    N.actualRootedCapOriginalArc b (N.actualRootedCapInArc b e ht) = e := by
  unfold actualRootedCapInArc
  split
  · rfl
  · exact (N.original_arc_entering_blob_identity b e ht (by assumption)
      (N.original_arc_entering_blob_nonroot b e ht (by assumption))).symm

theorem actualRootedCapRoot_inner_implies_root_blob (b : N.graph.Blob)
    (v : N.OriginalBlobVertex b) (h : N.actualRootedCapRoot b = Sum.inl v) :
    b = N.graph.blobOf N.root := by
  unfold actualRootedCapRoot at h
  split at h
  · assumption
  · cases h

theorem actualRootedCapOriginalArc_source (b : N.graph.Blob)
    (f : N.RootedCapArc b) (v : N.OriginalBlobVertex b)
    (hs : (N.actualRootedCapGraph b).source f = Sum.inl v) :
    N.graph.source (N.actualRootedCapOriginalArc b f) = v.val := by
  rcases f with e | (p | t)
  · exact congrArg Subtype.val (Sum.inl.inj hs)
  · by_cases hp : N.graph.bridgeQuotient.source p.val = b
    · have hi : N.originalPortInner b p = v := by
        simpa only [actualRootedCapGraph,Sum.elim_inr,Sum.elim_inl,hp,if_pos,Sum.inl.injEq] using hs
      exact (N.originalPortInner_value_outgoing b p hp).symm.trans
        (congrArg Subtype.val hi)
    · have hr : b = N.graph.blobOf N.root := N.actualRootedCapRoot_inner_implies_root_blob b v
        (by simpa only [actualRootedCapGraph,Sum.elim_inr,Sum.elim_inl,hp,if_neg] using hs)
      exact False.elim (N.original_root_blob_has_no_incoming_port p.val
        ((p.property.resolve_left hp).trans hr))
  · exact False.elim (t.property (N.actualRootedCapRoot_inner_implies_root_blob b v hs))

theorem actualRootedCapOriginalArc_target (b : N.graph.Blob)
    (f : N.RootedCapArc b) (v : N.OriginalBlobVertex b)
    (ht : (N.actualRootedCapGraph b).target f = Sum.inl v) :
    N.graph.target (N.actualRootedCapOriginalArc b f) = v.val := by
  rcases f with e | (p | t)
  · exact congrArg Subtype.val (Sum.inl.inj ht)
  · cases ht
  · have hi : N.originalRootedCapEntry b = v := Sum.inl.inj ht
    exact (N.originalRootedCapEntry_nonroot_value b t.property).symm.trans
      (congrArg Subtype.val hi)

theorem actualRootedCapOutArc_roundtrip (b : N.graph.Blob)
    (f : N.RootedCapArc b) (v : N.OriginalBlobVertex b)
    (hs : (N.actualRootedCapGraph b).source f = Sum.inl v) :
    N.actualRootedCapOutArc b (N.actualRootedCapOriginalArc b f)
      (by rw [N.actualRootedCapOriginalArc_source b f v hs];exact v.property) = f := by
  rcases f with e | (p | t)
  · simp only [actualRootedCapOriginalArc,Sum.elim_inl,actualRootedCapOutArc,dif_pos e.property.2]
  · by_cases hp : N.graph.bridgeQuotient.source p.val = b
    · have hnot : N.graph.blobOf (N.graph.target p.val.val) ≠ b := by
        intro h
        exact (N.graph.bridgeQuotient.bridge_endpoints_ne (N.graph.quotient_edge_is_bridge p.val))
          (hp.trans h.symm)
      simp only [actualRootedCapOriginalArc,Sum.elim_inr,Sum.elim_inl,actualRootedCapOutArc,dif_neg hnot]
    · exact False.elim (N.original_root_blob_has_no_incoming_port p.val
        ((p.property.resolve_left hp).trans (N.actualRootedCapRoot_inner_implies_root_blob b v
          (by simpa only [actualRootedCapGraph,Sum.elim_inr,Sum.elim_inl,hp,if_neg] using hs))))
  · exact False.elim (t.property (N.actualRootedCapRoot_inner_implies_root_blob b v hs))

theorem actualRootedCapInArc_roundtrip (b : N.graph.Blob)
    (f : N.RootedCapArc b) (v : N.OriginalBlobVertex b)
    (ht : (N.actualRootedCapGraph b).target f = Sum.inl v) :
    N.actualRootedCapInArc b (N.actualRootedCapOriginalArc b f)
      (by rw [N.actualRootedCapOriginalArc_target b f v ht];exact v.property) = f := by
  rcases f with e | (p | t)
  · simp only [actualRootedCapOriginalArc,Sum.elim_inl,actualRootedCapInArc,dif_pos e.property.1]
  · cases ht
  · have hnot := N.originalRootedCapIncoming_outside_source b t.property
    simp only [actualRootedCapOriginalArc,Sum.elim_inr,actualRootedCapInArc,dif_neg hnot]
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actualRootedCapOutArc_roundtrip
#print axioms Nanuq.Source.RootedBinary.actualRootedCapInArc_roundtrip
