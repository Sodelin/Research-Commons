import NanuqActualPortCutFibre
import GraphQuartetExistence

/-! A selected 2+2 cut cannot lie beyond an original port carrying at most one
of four distinctly projected taxa. This is a physical source admission step. -/
namespace Nanuq.Source.RootedBinary.Switching

open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X} (S : N.Switching)

theorem three_on_source_side_forbid_opposite_quartet_cut
    (q : Fin 4 ↪ X) (g f : S.Edge)
    (hbig : 3 ≤ (S.quartetSide q g (S.graph.source g)).card)
    (hfs : S.graph.ReachWithout g (S.graph.target g) (S.graph.source f))
    (hft : S.graph.ReachWithout g (S.graph.target g) (S.graph.target f))
    (hcut : (S.quartetSide q f (S.graph.target f)).card = 2) : False := by
  have hsum := S.quartetSide_card_sum q f
  have hsource : (S.quartetSide q f (S.graph.source f)).card = 2 := by omega
  have hg := S.graph.uniqueIncoming_all_bridges
    S.selected_uniqueIncoming S.selected_acyclic g
  have hwalk (i : Fin 4) (hi : i ∈ S.quartetSide q g (S.graph.source g)) :
      S.graph.ReachWithout f (S.graph.source g) (N.leaf (q i)) :=
    S.graph.source_side_walk_avoids_opposite_edge hg (.refl) hfs hft
      ((S.mem_quartetSide q g _ i).mp hi)
  rcases S.graph.edge_side_cover f (S.selected_connected _ _) with hs | ht
  · have hsub : S.quartetSide q g (S.graph.source g) ⊆
        S.quartetSide q f (S.graph.source f) := by
      intro i hi
      exact (S.mem_quartetSide q f _ i).mpr (hs.trans (hwalk i hi))
    have hle := Finset.card_le_card hsub
    omega
  · have hsub : S.quartetSide q g (S.graph.source g) ⊆
        S.quartetSide q f (S.graph.target f) := by
      intro i hi
      exact (S.mem_quartetSide q f _ i).mpr (ht.trans (hwalk i hi))
    have hle := Finset.card_le_card hsub
    omega

theorem outgoing_port_forbids_exterior_quartet_cut
    (q : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (p : N.BlobPort b) (hp : N.graph.bridgeQuotient.source p.val = b)
    (f : S.Edge)
    (hfs : S.graph.ReachWithout (S.retainedBridge p.val.val p.val.property)
      (N.graph.target p.val.val) (S.graph.source f))
    (hft : S.graph.ReachWithout (S.retainedBridge p.val.val p.val.property)
      (N.graph.target p.val.val) (S.graph.target f)) :
    (S.quartetSide q f (S.graph.target f)).card ≠ 2 := by
  let g := S.retainedBridge p.val.val p.val.property
  have hsmall : (S.quartetSide q g (S.graph.target g)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi0 := (S.original_bridge_target_side_iff p.val.val p.val.property _).mp
      ((S.mem_quartetSide q g _ i).mp hi)
    have hj0 := (S.original_bridge_target_side_iff p.val.val p.val.property _).mp
      ((S.mem_quartetSide q g _ j).mp hj)
    have hip := (N.blobProjection_eq_iff_target_side b hb (q i) p hp).mpr hi0
    have hjp := (N.blobProjection_eq_iff_target_side b hb (q j) p hp).mpr hj0
    exact hinj (hip.trans hjp.symm)
  have hsum := S.quartetSide_card_sum q g
  have hbig : 3 ≤ (S.quartetSide q g (S.graph.source g)).card := by omega
  intro hcut
  exact S.three_on_source_side_forbid_opposite_quartet_cut q g f hbig hfs hft hcut

end Nanuq.Source.RootedBinary.Switching

#print axioms Nanuq.Source.RootedBinary.Switching.outgoing_port_forbids_exterior_quartet_cut
