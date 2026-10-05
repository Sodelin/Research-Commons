import NanuqActualPortLeafCap

/-! Physical cut-side readout on literal capped port tips. Collapsing a cap
leaf edge keeps its inner attachment, while every internal original edge ID
is preserved. This is the cut binding needed for the quartet readout gate. -/
namespace Nanuq.Source.RootedBinary.Switching
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X} (S : N.Switching)

noncomputable def cappedBlobCollapse (b : N.graph.Blob) :
    N.CappedBlobVertex b → N.OriginalBlobVertex b := Sum.elim id (N.originalPortInner b)

theorem capped_walk_collapses_to_internal (b : N.graph.Blob)
    (keep : S.CappedBlobEdge b → Prop) (allowed : S.InternalBlobEdge b → Prop)
    (hkeep : ∀ f, keep (Sum.inl f) → allowed f)
    {a c : N.CappedBlobVertex b} (h : (S.actualCappedBlobGraph b).UReach keep a c) :
    (S.internalBlobGraph b).UReach allowed (S.cappedBlobCollapse b a) (S.cappedBlobCollapse b c) := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hstep ih =>
    obtain ⟨g, hg, hinc⟩ := hstep
    cases g with
    | inl f =>
      apply ih.tail
      refine ⟨f,hkeep f hg,?_⟩
      rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact Or.inl ⟨congrArg (S.cappedBlobCollapse b) hs,congrArg (S.cappedBlobCollapse b) ht⟩
      · exact Or.inr ⟨congrArg (S.cappedBlobCollapse b) hs,congrArg (S.cappedBlobCollapse b) ht⟩
    | inr p =>
      have hvw : S.cappedBlobCollapse b v = S.cappedBlobCollapse b w := by
        rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
        · exact (congrArg (S.cappedBlobCollapse b) hs).symm.trans
            (congrArg (S.cappedBlobCollapse b) ht)
        · exact (congrArg (S.cappedBlobCollapse b) ht).symm.trans
            (congrArg (S.cappedBlobCollapse b) hs)
      simpa only [← hvw] using ih

theorem internal_cut_walk_lifts_to_cap (b : N.graph.Blob) (f : S.InternalBlobEdge b)
    {a c : N.OriginalBlobVertex b} (h : (S.internalBlobGraph b).ReachWithout f a c) :
    (S.actualCappedBlobGraph b).ReachWithout (Sum.inl f) (Sum.inl a) (Sum.inl c) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨g,hgf,hinc⟩ := hstep
    apply ih.tail
    refine ⟨Sum.inl g,fun heq => hgf (Sum.inl.inj heq),?_⟩
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg Sum.inl hs,congrArg Sum.inl ht⟩
    · exact Or.inr ⟨congrArg Sum.inl hs,congrArg Sum.inl ht⟩

theorem capped_internal_edge_is_bridge (b : N.graph.Blob) (f : S.InternalBlobEdge b) :
    (S.actualCappedBlobGraph b).IsBridge (Sum.inl f) := by
  intro h
  exact S.internal_blob_edge_is_bridge b f
    (S.capped_walk_collapses_to_internal b (fun g => g ≠ Sum.inl f)
      (fun g => g ≠ f) (fun g hg heq => hg (congrArg Sum.inl heq)) h)

theorem capped_internal_cut_source_port_side_iff (b : N.graph.Blob)
    (f : S.InternalBlobEdge b) (p : N.BlobPort b) :
    (S.actualCappedBlobGraph b).ReachWithout (Sum.inl f)
      ((S.actualCappedBlobGraph b).source (Sum.inl f)) (Sum.inr p) ↔
      (S.internalBlobGraph b).ReachWithout f ((S.internalBlobGraph b).source f)
        (N.originalPortInner b p) := by
  constructor
  · exact S.capped_walk_collapses_to_internal b (fun g => g ≠ Sum.inl f)
      (fun g => g ≠ f) (fun g hg heq => hg (congrArg Sum.inl heq))
  · intro h
    exact (S.internal_cut_walk_lifts_to_cap b f h).tail
      ⟨Sum.inr p,(by intro heq; cases heq),Or.inl ⟨rfl,rfl⟩⟩

theorem capped_internal_cut_target_port_side_iff (b : N.graph.Blob)
    (f : S.InternalBlobEdge b) (p : N.BlobPort b) :
    (S.actualCappedBlobGraph b).ReachWithout (Sum.inl f)
      ((S.actualCappedBlobGraph b).target (Sum.inl f)) (Sum.inr p) ↔
      (S.internalBlobGraph b).ReachWithout f ((S.internalBlobGraph b).target f)
        (N.originalPortInner b p) := by
  constructor
  · exact S.capped_walk_collapses_to_internal b (fun g => g ≠ Sum.inl f)
      (fun g => g ≠ f) (fun g hg heq => hg (congrArg Sum.inl heq))
  · intro h
    exact (S.internal_cut_walk_lifts_to_cap b f h).tail
      ⟨Sum.inr p,(by intro heq; cases heq),Or.inl ⟨rfl,rfl⟩⟩

theorem actual_capped_cut_source_taxon_side_iff (b : N.graph.Blob)
    (hb : N.NonleafBlob b) (f : S.InternalBlobEdge b)
    (p : N.BlobPort b) (x : X) (hx : N.blobProjection b hb x = p) :
    (S.actualCappedBlobGraph b).ReachWithout (Sum.inl f)
      ((S.actualCappedBlobGraph b).source (Sum.inl f)) (Sum.inr p) ↔
      S.graph.ReachWithout f.val (S.graph.source f.val) (N.leaf x) := by
  rw [S.capped_internal_cut_source_port_side_iff,
    S.internal_blob_cut_source_side_iff]
  have h := S.original_port_attachment_connected_to_taxon_without_internal_cut b hb f p x hx
  exact ⟨fun hi => hi.trans h,fun hx => hx.trans (S.graph.ureach_symm h)⟩

theorem actual_capped_cut_target_taxon_side_iff (b : N.graph.Blob)
    (hb : N.NonleafBlob b) (f : S.InternalBlobEdge b)
    (p : N.BlobPort b) (x : X) (hx : N.blobProjection b hb x = p) :
    (S.actualCappedBlobGraph b).ReachWithout (Sum.inl f)
      ((S.actualCappedBlobGraph b).target (Sum.inl f)) (Sum.inr p) ↔
      S.graph.ReachWithout f.val (S.graph.target f.val) (N.leaf x) := by
  rw [S.capped_internal_cut_target_port_side_iff,
    S.internal_blob_cut_target_side_iff]
  have h := S.original_port_attachment_connected_to_taxon_without_internal_cut b hb f p x hx
  exact ⟨fun hi => hi.trans h,fun hx => hx.trans (S.graph.ureach_symm h)⟩
end Nanuq.Source.RootedBinary.Switching

#print axioms Nanuq.Source.RootedBinary.Switching.actual_capped_cut_source_taxon_side_iff
#print axioms Nanuq.Source.RootedBinary.Switching.actual_capped_cut_target_taxon_side_iff
