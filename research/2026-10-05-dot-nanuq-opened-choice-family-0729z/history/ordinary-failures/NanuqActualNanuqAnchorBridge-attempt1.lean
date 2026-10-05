import NanuqActualQuartetWitnessSymmetry

/-! Literal bridge from the source's original NANUQ formula to the proved
actual anchor decomposition. Its 2n-4 constant, repeated-label masks and
uniform DISTINCT quartet convention are retained. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical BigOperators
open Nanuq.Weighted Nanuq.Composition Nanuq.PortPatterns
variable {V E : Type*} {n : Nat}
variable [Fintype V] [Fintype E] [DecidableEq V]
variable (N : RootedBinary V E (Fin n))

noncomputable def actualQuartetData : QuartetData n := fun x y p q => N.actualTupleMean ![x,y,p,q]

theorem actualQuartetData_witness_symmetric : WitnessSymmetric N.actualQuartetData := by
  intro x y p q _ _ _ _
  exact N.actualTupleMean_witness_swap x y p q

theorem actual_orderedAnchor_eq (p q x y : Fin n) :
    orderedAnchor N.actualQuartetData p q x y = N.actualTupleAnchor ![x,y,p,q] := by
  by_cases hxy : x = y <;> by_cases hpq : p = q <;>
    simp [orderedAnchor,anchorMatrix,actualTupleAnchor,tupleAnchor,actualQuartetData,hxy,hpq]

theorem actual_weightedNanuq_eq_anchor (m : Fin n → ℚ) (x y : Fin n) :
    weightedNanuq N.actualQuartetData m x y = N.actualWeightedAnchorDistance m x y := by
  rw [weightedNanuq_eq_ordered_anchor N.actualQuartetData N.actualQuartetData_witness_symmetric]
  simp_rw [N.actual_orderedAnchor_eq]
  rfl

theorem actual_weightedNanuq_blob_composition (m : Fin n → ℚ) (x y : Fin n) :
    weightedNanuq N.actualQuartetData m x y =
      ∑ b : {b : N.graph.Blob // N.NonleafBlob b},
        (N.actualEveryNonleafRootedCapSource b.val b.property).actualWeightedAnchorDistance
          (weightedPortMass (N.blobProjection b.val b.property) m)
          (N.blobProjection b.val b.property x) (N.blobProjection b.val b.property y) := by
  rw [N.actual_weightedNanuq_eq_anchor,N.actual_weighted_anchor_composition]

theorem actual_sourceNanuq_blob_composition (x y : Fin n) :
    sourceNanuq N.actualQuartetData x y =
      ∑ b : {b : N.graph.Blob // N.NonleafBlob b},
        (N.actualEveryNonleafRootedCapSource b.val b.property).actualWeightedAnchorDistance
          (portMass (N.blobProjection b.val b.property))
          (N.blobProjection b.val b.property x) (N.blobProjection b.val b.property y) := by
  rw [← weightedNanuq_unit_eq_source N.actualQuartetData,
    N.actual_weightedNanuq_eq_anchor,N.actual_unit_anchor_composition]
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_sourceNanuq_blob_composition
#print axioms Nanuq.Source.RootedBinary.actual_weightedNanuq_blob_composition
