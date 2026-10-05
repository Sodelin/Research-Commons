import guards.NanuqActualQuartetCutLocality

set_option debug.skipKernelTC false

/-! Every actual selected quartet 2+2 cut for four distinct original ports lies
inside that original blob. The original source and port maps supply all sides. -/
namespace Nanuq.Source.EdgeGraph
variable {V E : Type*} (G : EdgeGraph V E)

theorem edge_endpoints_reachable_without_other_edge
    {e f : E} (hne : f ≠ e) {a v : V}
    (hv : v = G.source f ∨ v = G.target f)
    (h : G.ReachWithout e a v) :
    G.ReachWithout e a (G.source f) ∧ G.ReachWithout e a (G.target f) := by
  rcases hv with rfl | rfl
  · exact ⟨h, h.tail ⟨f, hne, G.inc_source_target f⟩⟩
  · exact ⟨h.tail ⟨f, hne, G.inc_symm (G.inc_source_target f)⟩, h⟩
end Nanuq.Source.EdgeGraph

namespace Nanuq.Source.RootedBinary.Switching
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X} (S : N.Switching)

theorem outgoing_port_quartet_target_card_le_one
    (q : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (p : N.BlobPort b) (hp : N.graph.bridgeQuotient.source p.val = b) :
    (S.quartetSide q (S.retainedBridge p.val.val p.val.property)
      (N.graph.target p.val.val)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi0 := (S.original_bridge_target_side_iff p.val.val p.val.property _).mp
    ((S.mem_quartetSide q _ _ i).mp hi)
  have hj0 := (S.original_bridge_target_side_iff p.val.val p.val.property _).mp
    ((S.mem_quartetSide q _ _ j).mp hj)
  have hip := (N.blobProjection_eq_iff_target_side b hb (q i) p hp).mpr hi0
  have hjp := (N.blobProjection_eq_iff_target_side b hb (q j) p hp).mpr hj0
  exact hinj (hip.trans hjp.symm)

theorem incoming_port_quartet_source_card_le_one
    (q : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (p : N.BlobPort b) (hp : N.graph.bridgeQuotient.target p.val = b) :
    (S.quartetSide q (S.retainedBridge p.val.val p.val.property)
      (N.graph.source p.val.val)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi0 := (S.original_bridge_source_side_iff p.val.val p.val.property _).mp
    ((S.mem_quartetSide q _ _ i).mp hi)
  have hj0 := (S.original_bridge_source_side_iff p.val.val p.val.property _).mp
    ((S.mem_quartetSide q _ _ j).mp hj)
  have hip := (N.blobProjection_eq_iff_source_side b hb (q i) p hp).mpr hi0
  have hjp := (N.blobProjection_eq_iff_source_side b hb (q j) p hp).mpr hj0
  exact hinj (hip.trans hjp.symm)

theorem original_two_two_cut_endpoint_in_blob
    (q : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (f : S.Edge) (hcut : (S.quartetSide q f (S.graph.target f)).card = 2)
    (v : V) (hv : v = N.graph.source f.val ∨ v = N.graph.target f.val) :
    N.graph.blobOf v = b := by
  by_contra hne
  obtain ⟨e, he⟩ := N.graph.bridgeQuotient.port_exists N.blob_quotient_uniqueIncoming
    N.blob_quotient_acyclic (N.graph.blobOf N.root) N.blob_quotient_rooted
    b (N.graph.blobOf v) hne
  let p : N.BlobPort b := ⟨e, he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
  let g := S.retainedBridge e.val e.property
  rcases he with ⟨hes, hev⟩ | ⟨het, hev⟩
  · by_cases hfe : f.val = e.val
    · have hfg : f = g := Subtype.ext hfe
      have hsmall := S.outgoing_port_quartet_target_card_le_one q b hb hinj p hes
      have hsmall' : (S.quartetSide q f (S.graph.target f)).card ≤ 1 := by
        change (S.quartetSide q g (S.graph.target g)).card ≤ 1 at hsmall
        simpa only [hfg] using hsmall
      omega
    · have h0 : N.graph.ReachWithout e.val (N.graph.target e.val) v :=
        N.graph.quotient_reach_lifts_without e hev rfl rfl
      have hends := N.graph.edge_endpoints_reachable_without_other_edge hfe hv h0
      exact S.outgoing_port_forbids_exterior_quartet_cut q b hb hinj p hes f
        ((S.original_bridge_target_side_iff e.val e.property _).mpr hends.1)
        ((S.original_bridge_target_side_iff e.val e.property _).mpr hends.2) hcut
  · by_cases hfe : f.val = e.val
    · have hfg : f = g := Subtype.ext hfe
      have hsmall := S.incoming_port_quartet_source_card_le_one q b hb hinj p het
      have hsmall' : (S.quartetSide q f (S.graph.source f)).card ≤ 1 := by
        change (S.quartetSide q g (S.graph.source g)).card ≤ 1 at hsmall
        simpa only [hfg] using hsmall
      have hsum := S.quartetSide_card_sum q f
      omega
    · have h0 : N.graph.ReachWithout e.val (N.graph.source e.val) v :=
        N.graph.quotient_reach_lifts_without e hev rfl rfl
      have hends := N.graph.edge_endpoints_reachable_without_other_edge hfe hv h0
      exact S.incoming_port_forbids_exterior_quartet_cut q b hb hinj p het f
        ((S.original_bridge_source_side_iff e.val e.property _).mpr hends.1)
        ((S.original_bridge_source_side_iff e.val e.property _).mpr hends.2) hcut

theorem original_two_two_cut_internal_to_blob
    (q : Fin 4 ↪ X) (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (f : S.Edge) (hcut : (S.quartetSide q f (S.graph.target f)).card = 2) :
    N.graph.blobOf (N.graph.source f.val) = b ∧
      N.graph.blobOf (N.graph.target f.val) = b :=
  ⟨S.original_two_two_cut_endpoint_in_blob q b hb hinj f hcut _ (Or.inl rfl),
   S.original_two_two_cut_endpoint_in_blob q b hb hinj f hcut _ (Or.inr rfl)⟩
end Nanuq.Source.RootedBinary.Switching

#print axioms Nanuq.Source.RootedBinary.Switching.original_two_two_cut_internal_to_blob
