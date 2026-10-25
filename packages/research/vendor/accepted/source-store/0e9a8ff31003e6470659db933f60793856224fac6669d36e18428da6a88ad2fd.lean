import NanuqActualRootedCapAdmission

/-! Every actual nonleaf blob has at least two actual ports. Thus the rooted
cap's taxon-count field is derived for all nonleaf blobs, not only a selected
four-distinct-port row. No extra port-degree/admission premise is supplied. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem actual_nonleaf_blob_has_two_ports (b : N.graph.Blob) (hb : N.NonleafBlob b) :
    2 ≤ Fintype.card (N.BlobPort b) := by
  classical
  by_contra hcard
  have hsingle : ∀ p q : N.BlobPort b, p = q :=
    Fintype.card_le_one_iff.mp (Nat.le_of_lt_succ (Nat.lt_of_not_ge hcard))
  by_cases hr : b = N.graph.blobOf N.root
  · haveI : Nonempty X := Fintype.card_pos_iff.mp
      (Nat.lt_of_lt_of_le (by decide : 0 < 2) N.at_least_two_taxa)
    let p := N.blobProjection b hb (Classical.choice inferInstance)
    have hnt : N.graph.bridgeQuotient.target p.val ≠ b := by
      intro h
      exact N.original_root_blob_has_no_incoming_port p.val (h.trans hr)
    have hp : N.graph.bridgeQuotient.source p.val = b := p.property.resolve_right hnt
    have hdom : ∀ x, N.graph.Dominates N.root (N.graph.target p.val.val) (N.leaf x) := by
      intro x hav
      have hx : N.graph.ReachWithout p.val.val (N.graph.target p.val.val) (N.leaf x) :=
        (N.blobProjection_eq_iff_target_side b hb x p hp).mp (hsingle _ _)
      exact p.val.property ((N.root_on_source_side p.val.val).trans
        ((N.graph.avoid_target_reach_without p.val.val hav).trans (N.graph.ureach_symm hx)))
    exact N.edge_target_ne_root p.val.val (N.least_stable _ hdom)
  · let p := N.originalIncomingBlobPort b hr
    obtain ⟨x,hx⟩ := N.bridge_target_side_contains_taxon p.val.property
    have hs : N.graph.ReachWithout p.val.val (N.graph.source p.val.val) (N.leaf x) :=
      (N.blobProjection_eq_iff_source_side b hb x p (N.originalIncomingBlobPort_target b hr)).mp
        (hsingle _ _)
    exact N.graph.bridge_sides_disjoint p.val.property hs hx

noncomputable def actualEveryNonleafRootedCapSource (b : N.graph.Blob) (hb : N.NonleafBlob b) :
    RootedBinary (N.RootedCapVertex b) (N.RootedCapArc b) (N.BlobPort b) :=
  N.actualRootedCapSource b hb (N.actual_nonleaf_blob_has_two_ports b hb)
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_nonleaf_blob_has_two_ports
#print axioms Nanuq.Source.RootedBinary.actualEveryNonleafRootedCapSource
