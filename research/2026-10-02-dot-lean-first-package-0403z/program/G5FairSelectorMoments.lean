import G5CoupledQuartetKernel
import Mathlib.Probability.Distributions.Uniform

/-!
# Genuine fair selector probability equals the raw pair count

Contributor: dot, 2026-10-02. The probability law is the uniform PMF on two
actual independent binary selectors. Its co-occupancy probability is proved
from PMF counting, not stored as a requested observation-output field.
Original graph route coins must still be mapped to this law separately.
-/
namespace GProgram.G5.QuartetKernel
open scoped BigOperators ENNReal NNReal
variable {α : Type*} [DecidableEq α]

def meetingChoices (p q : Fin 2 → α) : Finset (Fin 2 × Fin 2) :=
  Finset.univ.filter (fun k => p k.1 = q k.2)

theorem meetingChoices_card (p q : Fin 2 → α) :
    (meetingChoices p q).card = pairCount p q := by
  rw [Finset.card_eq_sum_ones]
  simp only [meetingChoices, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two, pairCount]
  omega

noncomputable def fairMeetingMass (p q : Fin 2 → α) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin 2 × Fin 2)).toOuterMeasure
    {k | p k.1 = q k.2}

theorem fairMeetingMass_eq_count (p q : Fin 2 → α) :
    fairMeetingMass p q = (pairCount p q : ℝ≥0∞) / 4 := by
  classical
  rw [fairMeetingMass, PMF.toOuterMeasure_uniformOfFintype_apply]
  have hc : Fintype.card {k : Fin 2 × Fin 2 // p k.1 = q k.2} = pairCount p q := by
    simpa [meetingChoices, Fintype.card_subtype] using meetingChoices_card p q
  change (Fintype.card {k : Fin 2 × Fin 2 // p k.1 = q k.2} : ℝ≥0∞) /
    (Fintype.card (Fin 2 × Fin 2) : ℝ≥0∞) = (pairCount p q : ℝ≥0∞) / 4
  rw [hc]
  norm_num

#print axioms meetingChoices_card
#print axioms fairMeetingMass_eq_count
end GProgram.G5.QuartetKernel
