/- Hosted4.35 source variant only. The pinned4.33 source is unchanged.
The old uniformOfFintype PMF API became a measure alias. This variant uses
an actual normalized PMF with the SAME four atom masses1/4 and proves the
unchanged event-count theorem. It has not been accepted by preparation alone.
-/
import G5CoupledQuartetKernel
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

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
  (PMF.ofFintype (fun _ : Fin 2 × Fin 2 => (1 / 4 : ℝ≥0∞))
    (by
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))).toOuterMeasure
    {k | p k.1 = q k.2}

theorem fairMeetingMass_eq_count (p q : Fin 2 → α) :
    fairMeetingMass p q = (pairCount p q : ℝ≥0∞) / 4 := by
  classical
  rw [fairMeetingMass, PMF.toOuterMeasure_ofFintype_apply, tsum_fintype]
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  change (∑ k : Fin 2 × Fin 2, if p k.1 = q k.2 then (1 / 4 : ℝ≥0∞) else 0) = _
  calc
    _ = ∑ k ∈ meetingChoices p q, (1 / 4 : ℝ≥0∞) := by
      rw [meetingChoices, Finset.sum_filter]
    _ = (pairCount p q : ℝ≥0∞) / 4 := by
      simp [Finset.sum_const, meetingChoices_card, nsmul_eq_mul, div_eq_mul_inv]

#print axioms meetingChoices_card
#print axioms fairMeetingMass_eq_count
end GProgram.G5.QuartetKernel
