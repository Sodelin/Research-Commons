import SocialScience.Identifiability

namespace SocialScience.Aggregation

/-- Cross-multiplied rate comparison; use only with positive denominators. -/
def Higher (successA sizeA successB sizeB : Nat) : Prop :=
  successB * sizeA < successA * sizeB

/-- All four synthetic cells are valid positive-denominator counts. -/
theorem reversal_cells_valid :
    9 ≤ (10 : Nat) ∧ 80 ≤ (100 : Nat) ∧ 20 ≤ (100 : Nat) ∧ 1 ≤ (10 : Nat) ∧
    0 < (10 : Nat) ∧ 0 < (100 : Nat) := by decide

theorem first_stratum_advantage : Higher 9 10 80 100 := by
  unfold Higher
  decide

theorem second_stratum_advantage : Higher 20 100 1 10 := by
  unfold Higher
  decide

theorem pooled_reversal : Higher (80 + 1) (100 + 10) (9 + 20) (10 + 100) := by
  unfold Higher
  decide

theorem simpson_reversal :
    Higher 9 10 80 100 ∧ Higher 20 100 1 10 ∧
    Higher (80 + 1) (100 + 10) (9 + 20) (10 + 100) :=
  ⟨first_stratum_advantage, second_stratum_advantage, pooled_reversal⟩

/-- Equal-weight addition preserves two count inequalities. -/
theorem equal_weight_addition_preserves_order (a b c d : Int)
    (first : a ≤ b) (second : c ≤ d) : a + c ≤ b + d := by omega

/-- A sum loses the component distinction even when values are exact. -/
theorem aggregate_cannot_identify_components :
    ¬ Identifiability.Identified Identifiability.twoComponent (fun probe => probe = false) :=
  Identifiability.baseline_not_identified

/-- No downstream recoding restores a distinction already lost by summing. -/
theorem recoding_cannot_restore_components {Y : Type} (recode : Int → Y) :
    Identifiability.Equivalent
      (fun p probe => recode (Identifiability.twoComponent p probe))
      (fun probe => probe = false) (1, 0) (0, 1) :=
  Identifiability.postprocess_preserves_equivalence recode Identifiability.baseline_ambiguous

end SocialScience.Aggregation
