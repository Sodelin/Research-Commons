import NanuqActualBlobSwitchingRestriction

/-! Literal port-tip capping of the original selected blob, retaining every
internal edge ID. The port-tip attachment and its physical source cut-side
meaning are proved here. Complete capped quartet/rooted-source admission is
not asserted by these definitions. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

noncomputable def originalPortInner (b : N.graph.Blob) (p : N.BlobPort b) :
    N.OriginalBlobVertex b :=
  if hs : N.graph.bridgeQuotient.source p.val = b then
    ⟨N.graph.source p.val.val,hs⟩
  else ⟨N.graph.target p.val.val,p.property.resolve_left hs⟩

theorem originalPortInner_value_outgoing (b : N.graph.Blob) (p : N.BlobPort b)
    (hp : N.graph.bridgeQuotient.source p.val = b) :
    (N.originalPortInner b p).val = N.graph.source p.val.val := by
  simp only [originalPortInner,dif_pos hp]

theorem originalPortInner_value_incoming (b : N.graph.Blob) (p : N.BlobPort b)
    (hp : N.graph.bridgeQuotient.target p.val = b) :
    (N.originalPortInner b p).val = N.graph.target p.val.val := by
  have hs : ¬ N.graph.bridgeQuotient.source p.val = b := by
    intro h
    exact (N.graph.bridgeQuotient.bridge_endpoints_ne
      (N.graph.quotient_edge_is_bridge p.val)) (h.trans hp.symm)
  simp only [originalPortInner,dif_neg hs]

abbrev CappedBlobVertex (b : N.graph.Blob) :=
  Sum (N.OriginalBlobVertex b) (N.BlobPort b)

namespace Switching
variable {N} (S : N.Switching)

abbrev CappedBlobEdge (b : N.graph.Blob) :=
  Sum (S.InternalBlobEdge b) (N.BlobPort b)

noncomputable def actualCappedBlobGraph (b : N.graph.Blob) :
    EdgeGraph (N.CappedBlobVertex b) (S.CappedBlobEdge b) where
  source := Sum.elim (fun f => Sum.inl ((S.internalBlobGraph b).source f))
    (fun p => Sum.inl (N.originalPortInner b p))
  target := Sum.elim (fun f => Sum.inl ((S.internalBlobGraph b).target f)) Sum.inr

def actualCappedHybridMark (b : N.graph.Blob) : S.CappedBlobEdge b → Prop :=
  Sum.elim (fun f => N.graph.IsHybrid (N.graph.target f.val.val)) (fun _ => False)

theorem original_port_attachment_connected_to_taxon_without_internal_cut
    (b : N.graph.Blob) (hb : N.NonleafBlob b) (f : S.InternalBlobEdge b)
    (p : N.BlobPort b) (x : X) (hx : N.blobProjection b hb x = p) :
    S.graph.ReachWithout f.val (N.originalPortInner b p).val (N.leaf x) := by
  let e := p.val.val
  have he : N.graph.IsBridge e := p.val.property
  let g := S.retainedBridge e he
  have hne : e ≠ f.val.val := by
    intro h
    have h0 : N.graph.blobOf (N.graph.source e) = N.graph.blobOf (N.graph.target e) := by
      rw [h]
      exact f.property.1.trans f.property.2.symm
    exact N.graph.bridge_blob_ne he h0
  have hgf : g ≠ f.val := fun h => hne (congrArg Subtype.val h)
  have hg := S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic g
  rcases p.property with hp | hp
  · rw [N.originalPortInner_value_outgoing b p hp]
    have hx0 := (N.blobProjection_eq_iff_target_side b hb x p hp).mp hx
    have hxg := (S.original_bridge_target_side_iff e he _).mpr hx0
    have hs := (S.original_bridge_source_side_iff e he _).mpr
      (N.graph.sameBlob_avoids_bridge he (Quotient.exact (hp.trans f.property.1.symm)))
    have ht := (S.original_bridge_source_side_iff e he _).mpr
      (N.graph.sameBlob_avoids_bridge he (Quotient.exact (hp.trans f.property.2.symm)))
    have hw := S.graph.target_side_walk_avoids_opposite_edge hg (.refl) hs ht hxg
    exact (S.graph.ureach_single ⟨g,hgf,S.graph.inc_source_target g⟩).trans hw
  · rw [N.originalPortInner_value_incoming b p hp]
    have hx0 := (N.blobProjection_eq_iff_source_side b hb x p hp).mp hx
    have hxg := (S.original_bridge_source_side_iff e he _).mpr hx0
    have hs := (S.original_bridge_target_side_iff e he _).mpr
      (N.graph.sameBlob_avoids_bridge he (Quotient.exact (hp.trans f.property.1.symm)))
    have ht := (S.original_bridge_target_side_iff e he _).mpr
      (N.graph.sameBlob_avoids_bridge he (Quotient.exact (hp.trans f.property.2.symm)))
    have hw := S.graph.source_side_walk_avoids_opposite_edge hg (.refl) hs ht hxg
    exact (S.graph.ureach_single ⟨g,hgf,S.graph.inc_symm (S.graph.inc_source_target g)⟩).trans hw
end Switching
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.Switching.original_port_attachment_connected_to_taxon_without_internal_cut
