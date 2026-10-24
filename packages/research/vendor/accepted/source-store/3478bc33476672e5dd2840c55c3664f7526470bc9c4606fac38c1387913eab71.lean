import NanuqCutWalkLocality
import RawSourceAnchorLocalization
import GraphPortFibers

/-! Original port fibres stay connected when deleting a selected edge internal
to the original blob. This is a physical cut-path statement used for quartet
restriction; it assumes neither a local quartet law nor circularity. -/
namespace Nanuq.Source.RootedBinary.Switching

open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X} (S : N.Switching)

theorem original_port_fibre_connected_without_internal_cut
    (b : N.graph.Blob) (hb : N.NonleafBlob b) (f : S.Edge)
    (hfs : N.graph.blobOf (N.graph.source f.val) = b)
    (hft : N.graph.blobOf (N.graph.target f.val) = b)
    (x y : X) (hxy : N.blobProjection b hb x = N.blobProjection b hb y) :
    S.graph.ReachWithout f (N.leaf x) (N.leaf y) := by
  let p := N.blobProjection b hb x
  let e := p.val.val
  have he : N.graph.IsBridge e := p.val.property
  let g := S.retainedBridge e he
  have hg := S.graph.uniqueIncoming_all_bridges
    S.selected_uniqueIncoming S.selected_acyclic g
  have hx : N.blobProjection b hb x = p := rfl
  have hy : N.blobProjection b hb y = p := hxy.symm
  rcases p.property with hs | ht
  · have hx0 := (N.blobProjection_eq_iff_target_side b hb x p hs).mp hx
    have hy0 := (N.blobProjection_eq_iff_target_side b hb y p hs).mp hy
    have hsource : N.graph.SameBlob (N.graph.source e) (N.graph.source f.val) :=
      Quotient.exact (hs.trans hfs.symm)
    have htarget : N.graph.SameBlob (N.graph.source e) (N.graph.target f.val) :=
      Quotient.exact (hs.trans hft.symm)
    have hsf := (S.original_bridge_source_side_iff e he _).mpr
      (N.graph.sameBlob_avoids_bridge he hsource)
    have htf := (S.original_bridge_source_side_iff e he _).mpr
      (N.graph.sameBlob_avoids_bridge he htarget)
    have hxg := (S.original_bridge_target_side_iff e he _).mpr hx0
    have hyg := (S.original_bridge_target_side_iff e he _).mpr hy0
    exact S.graph.target_side_walk_avoids_opposite_edge hg hxg hsf htf
      ((S.graph.ureach_symm hxg).trans hyg)
  · have hx0 := (N.blobProjection_eq_iff_source_side b hb x p ht).mp hx
    have hy0 := (N.blobProjection_eq_iff_source_side b hb y p ht).mp hy
    have hsource : N.graph.SameBlob (N.graph.target e) (N.graph.source f.val) :=
      Quotient.exact (ht.trans hfs.symm)
    have htarget : N.graph.SameBlob (N.graph.target e) (N.graph.target f.val) :=
      Quotient.exact (ht.trans hft.symm)
    have hsf := (S.original_bridge_target_side_iff e he _).mpr
      (N.graph.sameBlob_avoids_bridge he hsource)
    have htf := (S.original_bridge_target_side_iff e he _).mpr
      (N.graph.sameBlob_avoids_bridge he htarget)
    have hxg := (S.original_bridge_source_side_iff e he _).mpr hx0
    have hyg := (S.original_bridge_source_side_iff e he _).mpr hy0
    exact S.graph.source_side_walk_avoids_opposite_edge hg hxg hsf htf
      ((S.graph.ureach_symm hxg).trans hyg)

theorem original_port_internal_cut_source_side_iff
    (b : N.graph.Blob) (hb : N.NonleafBlob b) (f : S.Edge)
    (hfs : N.graph.blobOf (N.graph.source f.val) = b)
    (hft : N.graph.blobOf (N.graph.target f.val) = b)
    (x y : X) (hxy : N.blobProjection b hb x = N.blobProjection b hb y) :
    S.graph.ReachWithout f (S.graph.source f) (N.leaf x) ↔
      S.graph.ReachWithout f (S.graph.source f) (N.leaf y) := by
  have h := S.original_port_fibre_connected_without_internal_cut b hb f hfs hft x y hxy
  exact ⟨fun hx => hx.trans h, fun hy => hy.trans (S.graph.ureach_symm h)⟩

theorem original_port_internal_cut_target_side_iff
    (b : N.graph.Blob) (hb : N.NonleafBlob b) (f : S.Edge)
    (hfs : N.graph.blobOf (N.graph.source f.val) = b)
    (hft : N.graph.blobOf (N.graph.target f.val) = b)
    (x y : X) (hxy : N.blobProjection b hb x = N.blobProjection b hb y) :
    S.graph.ReachWithout f (S.graph.target f) (N.leaf x) ↔
      S.graph.ReachWithout f (S.graph.target f) (N.leaf y) := by
  have h := S.original_port_fibre_connected_without_internal_cut b hb f hfs hft x y hxy
  exact ⟨fun hx => hx.trans h, fun hy => hy.trans (S.graph.ureach_symm h)⟩

end Nanuq.Source.RootedBinary.Switching

#print axioms Nanuq.Source.RootedBinary.Switching.original_port_fibre_connected_without_internal_cut
#print axioms Nanuq.Source.RootedBinary.Switching.original_port_internal_cut_source_side_iff
#print axioms Nanuq.Source.RootedBinary.Switching.original_port_internal_cut_target_side_iff
