import NanuqActualFullAnchor

/-! Actual-source weighted anchor composition. The anchor identity is proved
from the original source, not supplied as a composition premise. This is the
anchor-sum form; the global circular-support/semidirected conclusions remain
separate. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical BigOperators
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

noncomputable def actualWeightedAnchorDistance (m : X → ℚ) (x y : X) : ℚ :=
  (∑ p, ∑ q, m p * m q * N.actualTupleAnchor ![x,y,p,q]) / 2

theorem actual_blob_anchor_eq_rooted_cap (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (v : Fin 4 → X) :
    N.actualBlobTupleAnchor b hb v =
      (N.actualEveryNonleafRootedCapSource b hb).actualTupleAnchor
        (fun i => N.blobProjection b hb (v i)) := rfl

theorem actual_weighted_anchor_composition (m : X → ℚ) (x y : X) :
    N.actualWeightedAnchorDistance m x y =
      ∑ b : {b : N.graph.Blob // N.NonleafBlob b},
        (N.actualEveryNonleafRootedCapSource b.val b.property).actualWeightedAnchorDistance
          (Nanuq.Composition.weightedPortMass (N.blobProjection b.val b.property) m)
          (N.blobProjection b.val b.property x) (N.blobProjection b.val b.property y) := by
  classical
  unfold actualWeightedAnchorDistance
  simp_rw [N.actual_full_anchor_identity,N.actual_blob_anchor_eq_rooted_cap,Finset.mul_sum]
  rw [Finset.sum_comm_cycle,div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  have hvec (p q : X) :
      (fun i => N.blobProjection b.val b.property (![x,y,p,q] i)) =
        ![N.blobProjection b.val b.property x,N.blobProjection b.val b.property y,
          N.blobProjection b.val b.property p,N.blobProjection b.val b.property q] := by
    funext i;fin_cases i <;> rfl
  simp_rw [hvec]
  rw [Nanuq.Composition.sum_weighted_pairs_by_ports (N.blobProjection b.val b.property) m
    (fun p q => (N.actualEveryNonleafRootedCapSource b.val b.property).actualTupleAnchor
      ![N.blobProjection b.val b.property x,N.blobProjection b.val b.property y,p,q])]
  rw [div_eq_mul_inv]

theorem actual_unit_anchor_composition (x y : X) :
    N.actualWeightedAnchorDistance (fun _ => 1) x y =
      ∑ b : {b : N.graph.Blob // N.NonleafBlob b},
        (N.actualEveryNonleafRootedCapSource b.val b.property).actualWeightedAnchorDistance
          (Nanuq.Composition.portMass (N.blobProjection b.val b.property))
          (N.blobProjection b.val b.property x) (N.blobProjection b.val b.property y) := by
  rw [N.actual_weighted_anchor_composition]
  simp_rw [Nanuq.Composition.weightedPortMass_unit]
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_weighted_anchor_composition
#print axioms Nanuq.Source.RootedBinary.actual_unit_anchor_composition
