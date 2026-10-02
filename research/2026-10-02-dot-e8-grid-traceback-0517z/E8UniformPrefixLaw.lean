import E8StrictPrefixSelector
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The least-strict-prefix selector has exact weight/W branch masses under the
actual continuous uniform probability measure on [0,1). This establishes one
branch law, not independence across recursive draws, exact floating arithmetic,
or the versioned RNA traceback language/decomposition.
-/

noncomputable section

namespace E8UniformPrefixLaw

open MeasureTheory E8StrictPrefixSelector

def unitUniform : Measure ℝ := volume.restrict (Set.Ico 0 1)

theorem unitUniform_total : unitUniform Set.univ = 1 := by
  simp [unitUniform, Real.volume_Ico]

/-- The sentinel n is used off the uniform source domain; real branch indices
are below n. Thus each genuine branch preimage is its exact interval. -/
def uniformSelect (n : ℕ) (weight : ℕ → ℝ)
    (hpositive : 0 < prefixSum weight n) (u : ℝ) : ℕ := by
  classical
  exact if hu : u ∈ Set.Ico 0 1 then
    select n weight (u * prefixSum weight n)
      (uniform_target_valid n weight u hpositive hu.1 hu.2).1
      (uniform_target_valid n weight u hpositive hu.1 hu.2).2
    else n

theorem interval_bounds (n : ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ j < n, 0 ≤ weight j)
    (hpositive : 0 < prefixSum weight n) (j : ℕ) (hj : j < n) :
    0 ≤ prefixSum weight j / prefixSum weight n ∧
      prefixSum weight (j + 1) / prefixSum weight n ≤ 1 := by
  have hlo : 0 ≤ prefixSum weight j := by
    have h := prefix_monotone n weight hweight (Nat.zero_le j) (by omega)
    simpa only [prefix_zero] using h
  have hhi : prefixSum weight (j + 1) ≤ prefixSum weight n :=
    prefix_monotone n weight hweight (by omega) (le_refl n)
  refine ⟨div_nonneg hlo (le_of_lt hpositive), ?_⟩
  have h := div_le_div_of_nonneg_right hhi (le_of_lt hpositive)
  simpa only [div_self (ne_of_gt hpositive)] using h

theorem branch_preimage_interval (n : ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ j < n, 0 ≤ weight j)
    (hpositive : 0 < prefixSum weight n) (j : ℕ) (hj : j < n) :
    {u | uniformSelect n weight hpositive u = j} =
      Set.Ico (prefixSum weight j / prefixSum weight n)
        (prefixSum weight (j + 1) / prefixSum weight n) := by
  classical
  ext u
  constructor
  · intro hselect
    by_cases hu : u ∈ Set.Ico 0 1
    · simp only [Set.mem_ofPred_eq, uniformSelect, dif_pos hu] at hselect
      have hi := (selection_iff_interval n weight (u * prefixSum weight n)
        hweight (uniform_target_valid n weight u hpositive hu.1 hu.2).1
        (uniform_target_valid n weight u hpositive hu.1 hu.2).2 j).mp hselect
      exact ⟨(div_le_iff₀ hpositive).mpr hi.2.1,
        (lt_div_iff₀ hpositive).mpr hi.2.2⟩
    · simp only [Set.mem_ofPred_eq, uniformSelect, dif_neg hu] at hselect
      omega
  · intro hi
    have hb := interval_bounds n weight hweight hpositive j hj
    have hu : u ∈ Set.Ico 0 1 :=
      ⟨le_trans hb.1 hi.1, lt_of_lt_of_le hi.2 hb.2⟩
    simp only [Set.mem_ofPred_eq, uniformSelect, dif_pos hu]
    apply (selection_iff_interval n weight (u * prefixSum weight n) hweight
      (uniform_target_valid n weight u hpositive hu.1 hu.2).1
      (uniform_target_valid n weight u hpositive hu.1 hu.2).2 j).mpr
    exact ⟨hj, (div_le_iff₀ hpositive).mp hi.1, (lt_div_iff₀ hpositive).mp hi.2⟩

theorem branch_probability (n : ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ j < n, 0 ≤ weight j)
    (hpositive : 0 < prefixSum weight n) (j : ℕ) (hj : j < n) :
    unitUniform {u | uniformSelect n weight hpositive u = j} =
      ENNReal.ofReal (weight j / prefixSum weight n) := by
  rw [branch_preimage_interval n weight hweight hpositive j hj]
  have hb := interval_bounds n weight hweight hpositive j hj
  have hsub : Set.Ico (prefixSum weight j / prefixSum weight n)
      (prefixSum weight (j + 1) / prefixSum weight n) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro u hu
    exact ⟨le_trans hb.1 hu.1, lt_of_lt_of_le hu.2 hb.2⟩
  rw [unitUniform, Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr hsub, Real.volume_Ico]
  congr 1
  rw [prefix_step, add_div]
  ring

theorem zero_weight_branch_probability (n : ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ j < n, 0 ≤ weight j)
    (hpositive : 0 < prefixSum weight n) (j : ℕ) (hj : j < n)
    (hzero : weight j = 0) :
    unitUniform {u | uniformSelect n weight hpositive u = j} = 0 := by
  rw [branch_probability n weight hweight hpositive j hj, hzero]
  simp

end E8UniformPrefixLaw

#print axioms E8UniformPrefixLaw.unitUniform_total
#print axioms E8UniformPrefixLaw.interval_bounds
#print axioms E8UniformPrefixLaw.branch_preimage_interval
#print axioms E8UniformPrefixLaw.branch_probability
#print axioms E8UniformPrefixLaw.zero_weight_branch_probability
