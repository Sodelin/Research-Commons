import G5FourGroupCriterion
import G5FairSelectorMoments

/-!
# Genuine fair pair probabilities determine quartet route witnesses

Contributor: dot, 2026-10-02. Only SIX DISTINCT-label pair probabilities are
read. The probabilities are the actual uniform independent selector PMFs.
Population alphabets may differ. No quartet/output equality is assumed.
Original source graphs must still be mapped to these fair selector laws.
-/
namespace GProgram.G5.QuartetKernel
open scoped ENNReal NNReal
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem pairCount_eq_of_fair_mass_eq
    (p q : Fin 2 → α) (p' q' : Fin 2 → β)
    (h : fairMeetingMass p q = fairMeetingMass p' q') :
    pairCount p q = pairCount p' q' := by
  rw [fairMeetingMass_eq_count, fairMeetingMass_eq_count] at h
  have hh := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at hh
  have he : (pairCount p q : ℝ) = (pairCount p' q' : ℝ) := by linarith
  exact_mod_cast he

theorem selectorWitness_iff_of_six_distinct_counts
    (p : Fin 4 → Fin 2 → α) (q : Fin 4 → Fin 2 → β)
    (h : ∀ i j : Fin 4, i ≠ j → pairCount (p i) (p j) = pairCount (q i) (q j)) :
    selectorWitness p ↔ selectorWitness q := by
  have h01 := h 0 1 (by decide)
  have h02 := h 0 2 (by decide)
  have h03 := h 0 3 (by decide)
  have h12 := h 1 2 (by decide)
  have h13 := h 1 3 (by decide)
  have h23 := h 2 3 (by decide)
  apply not_iff_not.mp
  rw [selector_absence_iff_six_moments, selector_absence_iff_six_moments]
  simp only [absenceCases, h01, h02, h03, h12, h13, h23]

theorem selectorWitness_iff_of_six_fair_pair_masses
    (p : Fin 4 → Fin 2 → α) (q : Fin 4 → Fin 2 → β)
    (h : ∀ i j : Fin 4, i ≠ j → fairMeetingMass (p i) (p j) = fairMeetingMass (q i) (q j)) :
    selectorWitness p ↔ selectorWitness q := by
  apply selectorWitness_iff_of_six_distinct_counts p q
  intro i j hij
  exact pairCount_eq_of_fair_mass_eq (p i) (p j) (q i) (q j) (h i j hij)

theorem threeGroupWitness_iff_of_three_fair_pair_masses
    (g h i : Fin 2 → α) (g' h' i' : Fin 2 → β)
    (hgh : fairMeetingMass g h = fairMeetingMass g' h')
    (hgi : fairMeetingMass g i = fairMeetingMass g' i')
    (hhi : fairMeetingMass h i = fairMeetingMass h' i') :
    threeGroupWitness g h i ↔ threeGroupWitness g' h' i' := by
  have cgh := pairCount_eq_of_fair_mass_eq g h g' h' hgh
  have cgi := pairCount_eq_of_fair_mass_eq g i g' i' hgi
  have chi := pairCount_eq_of_fair_mass_eq h i h' i' hhi
  apply not_iff_not.mp
  rw [threeGroup_absence_iff, threeGroup_absence_iff]
  simp only [cgh,cgi,chi]

#print axioms pairCount_eq_of_fair_mass_eq
#print axioms selectorWitness_iff_of_six_fair_pair_masses
#print axioms threeGroupWitness_iff_of_three_fair_pair_masses
end GProgram.G5.QuartetKernel
