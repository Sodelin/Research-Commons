import CanonicalTheta
import RawNanuq
import NanuqActualNanuqAnchorBridge
import AllLevelParameterDomain
import NanuqActualWeightedAnchorComposition
import NanuqActualOpenedChoiceFamily
import NanuqActualSourceCycleCurve

/-! Typed reuse of CB-NANUQ-001's named source-to-geometry chain,
plus ORIGINAL CB-NANUQ-002 local theta/raw-source/composition components
and CB-NANUQ-003's exact real-domain component. No new alias proof is added
for the latter components: their original names and owners are checked.
Distinct resolution SETS/arithmetic means and all original graph/drawing/
hybrid-child premises remain. No all-level circularity/support theorem,
NMSC concordance factor, sequence likelihood or numerical embedding is added. -/
noncomputable section
namespace ResearchCommons.Claims.NANUQ
abbrev rooted_cap_distinct_set_and_mean :=
  @Nanuq.Source.RootedBinary.actual_four_port_rooted_cap_distinct_set_and_mean
abbrev repeated_label_anchor :=
  @Nanuq.Source.RootedBinary.actual_full_anchor_identity
abbrev weighted_anchor_composition :=
  @Nanuq.Source.RootedBinary.actual_weighted_anchor_composition
abbrev unit_anchor_composition :=
  @Nanuq.Source.RootedBinary.actual_unit_anchor_composition
abbrev opened_choice_distinct_set_and_mean :=
  @Nanuq.Source.RootedBinary.actual_opened_choice_distinct_family_and_mean
abbrev galled_cap_opened_family_and_mean :=
  @Nanuq.Source.RootedBinary.actual_galled_cap_opened_family_and_mean
abbrev actual_opened_curve_drawing :=
  @Nanuq.Source.RootedBinary.actualOpenedCurveDrawing
abbrev actual_opened_curve_subset :=
  @Nanuq.Source.RootedBinary.actualOpenedCurveDrawing_subset
abbrev original_curve_adapter_roundtrip :=
  @G1OuterLabelledMultigraphCurves.from_to_CurveDrawing
abbrev actual_opened_planar_curves :=
  @G1OuterLabelledMultigraphCurves.actualOpenedPlanarCurves
abbrev actual_opened_planar_subset :=
  @G1OuterLabelledMultigraphCurves.actualOpenedPlanarCurves_drawing_subset
abbrev actual_source_cycle_circle :=
  @G1OuterLabelledMultigraphCurves.actual_source_interface_cycle_circle

open scoped Classical BigOperators
open Nanuq.Source.RootedBinary Nanuq.Weighted Nanuq.Composition

variable {V E : Type*} {n : ℕ}
variable [Fintype V] [Fintype E] [DecidableEq V]

private theorem four_taxa_chart (x y p q : Fin n)
    (h : ValidFour x y p q) :
    (fourTaxa x y p q h : Fin 4 → Fin n) = ![x,y,p,q] := by
  funext i
  fin_cases i <;> simp [fourTaxa]

private theorem valid_four_of_tuple_injective (x y p q : Fin n)
    (h : Function.Injective ![x,y,p,q]) : ValidFour x y p q := by
  have hne (i j : Fin 4) (hij : i ≠ j) :
      (![x,y,p,q] i) ≠ (![x,y,p,q] j) := fun he => hij (h he)
  exact ⟨by simpa using hne 0 1 (by decide),
    by simpa using hne 2 3 (by decide),
    ⟨by simpa using hne 2 0 (by decide), by simpa using hne 2 1 (by decide)⟩,
    ⟨by simpa using hne 3 0 (by decide), by simpa using hne 3 1 (by decide)⟩⟩

/-- The two actual original-source charts agree on ALL labels, including
repeated-label/invalid quartet zeros. No stochastic/source equality is assumed. -/
theorem raw_tensor_eq_actual (N : Nanuq.Source.RootedBinary V E (Fin n)) :
    N.rawRho = N.actualQuartetData := by
  classical
  funext x y p q
  by_cases h : ValidFour x y p q
  · have hi : Function.Injective ![x,y,p,q] := by
      rw [← four_taxa_chart x y p q h]
      exact (fourTaxa x y p q h).injective
    rw [N.rawRho_valid x y p q h]
    change N.rawQuartetMean (fourTaxa x y p q h) = N.actualTupleMean ![x,y,p,q]
    rw [actualTupleMean, dif_pos hi]
    apply congrArg N.rawQuartetMean
    exact Function.Embedding.ext (fun i => congrFun (four_taxa_chart x y p q h) i)
  · have hi : ¬ Function.Injective ![x,y,p,q] :=
      fun hinj => h (valid_four_of_tuple_injective x y p q hinj)
    simp only [rawRho, dif_neg h, actualQuartetData, actualTupleMean, dif_neg hi]

/-- Literal weighted raw-source readout uses the SAME original blob law. -/
theorem raw_weighted_blob_composition
    (N : Nanuq.Source.RootedBinary V E (Fin n)) (m : Fin n → ℚ) (x y : Fin n) :
    weightedNanuq N.rawRho m x y =
      ∑ b : {b : N.graph.Blob // N.NonleafBlob b},
        (N.actualEveryNonleafRootedCapSource b.val b.property).actualWeightedAnchorDistance
          (weightedPortMass (N.blobProjection b.val b.property) m)
          (N.blobProjection b.val b.property x) (N.blobProjection b.val b.property y) := by
  rw [raw_tensor_eq_actual N]
  exact N.actual_weightedNanuq_blob_composition m x y

/-- Original2n-4 NANUQ constant and DISTINCT-quartet convention are preserved. -/
theorem raw_source_blob_composition
    (N : Nanuq.Source.RootedBinary V E (Fin n)) (x y : Fin n) :
    N.rawNanuq x y =
      ∑ b : {b : N.graph.Blob // N.NonleafBlob b},
        (N.actualEveryNonleafRootedCapSource b.val b.property).actualWeightedAnchorDistance
          (portMass (N.blobProjection b.val b.property))
          (N.blobProjection b.val b.property x) (N.blobProjection b.val b.property y) := by
  change sourceNanuq N.rawRho x y = _
  rw [raw_tensor_eq_actual N]
  exact N.actual_sourceNanuq_blob_composition x y

end ResearchCommons.Claims.NANUQ
