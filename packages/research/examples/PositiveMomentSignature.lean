import CMFullMomentUniqueness
import CMRationalBank
import Mathlib.Tactic

namespace ResearchCommons.Generated.PositiveMomentSignature
open Astra.CommonMoment Astra.CommonMoment.RationalBank
open scoped Classical BigOperators

def referenceNodes : Finset ℚ := {(1 / 1 : ℚ), (2 / 1 : ℚ), (3 / 1 : ℚ)}
def referenceWeight (q : ℚ) : ℚ := if q = (1 / 1 : ℚ) then (1 / 3 : ℚ) else if q = (2 / 1 : ℚ) then (1 / 3 : ℚ) else if q = (3 / 1 : ℚ) then (1 / 3 : ℚ) else 0
theorem referenceNodePos : ∀ q ∈ referenceNodes, 0 < q := by
  intro q hq
  norm_num [referenceNodes] at hq
  rcases hq with rfl | rfl | rfl
  all_goals norm_num
theorem referenceWeightPos : ∀ q ∈ referenceNodes, 0 < referenceWeight q := by
  intro q hq
  norm_num [referenceNodes] at hq
  rcases hq with rfl | rfl | rfl
  all_goals norm_num [referenceWeight]
theorem referenceMass : (∑ q ∈ referenceNodes, referenceWeight q) = 1 := by
  norm_num [referenceNodes, referenceWeight]
noncomputable def reference : FinitePositiveLaw :=
  fromGroupedRationals referenceNodes referenceWeight referenceNodePos referenceWeightPos referenceMass

def suppliedSignature : Fin 7 → ℚ := ![(1 / 1 : ℚ), (2 / 1 : ℚ), (14 / 3 : ℚ), (12 / 1 : ℚ), (98 / 3 : ℚ), (92 / 1 : ℚ), (794 / 3 : ℚ)]
theorem reference_support_cardinality : reference.nodes.card = 3 := by
  change (referenceNodes.image (fun q : ℚ => (q : ℝ))).card = 3
  rw [Finset.card_image_of_injective _ Rat.cast_injective]
  norm_num [referenceNodes]

theorem literal_signature_checked (i : Fin 7) :
    moment reference i.val = (suppliedSignature i : ℝ) := by
  fin_cases i
  all_goals unfold reference
  all_goals rw [fromGroupedRationals_moment]
  all_goals norm_num [referenceNodes, referenceWeight, suppliedSignature]

theorem supplied_signature_identifies_every_finite_positive_rival
    (rival : FinitePositiveLaw)
    (h : ∀ i : Fin 7, moment rival i.val = (suppliedSignature i : ℝ)) :
    atomMass rival = atomMass reference := by
  apply atomMass_eq_of_equal_consecutive_moments
  intro k hk
  have hi : k < 7 := by
    rw [reference_support_cardinality] at hk
    omega
  exact (h ⟨k, hi⟩).trans (literal_signature_checked ⟨k, hi⟩).symm

theorem supplied_signature_determines_every_further_moment
    (rival : FinitePositiveLaw)
    (h : ∀ i : Fin 7, moment rival i.val = (suppliedSignature i : ℝ)) :
    ∀ k, moment rival k = moment reference k := by
  apply all_moments_eq_of_equal_consecutive_moments
  intro k hk
  have hi : k < 7 := by
    rw [reference_support_cardinality] at hk
    omega
  exact (h ⟨k, hi⟩).trans (literal_signature_checked ⟨k, hi⟩).symm
#check literal_signature_checked
#check supplied_signature_identifies_every_finite_positive_rival
#check supplied_signature_determines_every_further_moment
end ResearchCommons.Generated.PositiveMomentSignature
