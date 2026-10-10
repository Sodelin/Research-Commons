import ResearchCommonsBernstein

/-!
Range certificate for the cubic alternating Taylor partial used by the
existing range-reduced exponential primitive. This establishes polynomial
bounds only, not a Python refinement, exponential remainder bound or
squaring/tolerance correctness theorem.
-/
open scoped BigOperators
open ResearchCommons.Bernstein

namespace ResearchCommons.BernsteinExpRange

noncomputable def cubicCoefficients (r : ℕ) : ℝ :=
  if r = 0 then 1 else if r = 1 then -1 else if r = 2 then 1 / 2 else -1 / 6

theorem cubic_coefficient_lower :
    ∀ d < 3 + 1, (1 / 3 : ℝ) ≤ bernsteinCoefficient 3 cubicCoefficients d := by
  intro d hd
  have hz : Nat.choose 1 3 = 0 := by decide
  interval_cases d <;>
    norm_num [bernsteinCoefficient, cubicCoefficients, Finset.sum_range_succ, hz]

theorem negative_cubic_coefficient_lower :
    ∀ d < 3 + 1, (-1 : ℝ) ≤
      bernsteinCoefficient 3 (fun r => -cubicCoefficients r) d := by
  intro d hd
  have hz : Nat.choose 1 3 = 0 := by decide
  interval_cases d <;>
    norm_num [bernsteinCoefficient, cubicCoefficients, Finset.sum_range_succ, hz]

theorem cubic_lower (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    (1 / 3 : ℝ) ≤ 1 - u + u ^ 2 / 2 - u ^ 3 / 6 := by
  have h := bernstein_polynomial_lower 3 cubicCoefficients (1 / 3)
    cubic_coefficient_lower hu
  norm_num [cubicCoefficients, Finset.sum_range_succ] at h
  linarith

theorem cubic_upper (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    1 - u + u ^ 2 / 2 - u ^ 3 / 6 ≤ 1 := by
  have h := bernstein_polynomial_lower 3 (fun r => -cubicCoefficients r) (-1)
    negative_cubic_coefficient_lower hu
  norm_num [cubicCoefficients, Finset.sum_range_succ] at h
  linarith

theorem cubic_range (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    (1 / 3 : ℝ) ≤ 1 - u + u ^ 2 / 2 - u ^ 3 / 6 ∧
    1 - u + u ^ 2 / 2 - u ^ 3 / 6 ≤ 1 :=
  ⟨cubic_lower u hu, cubic_upper u hu⟩

#print axioms cubic_coefficient_lower
#print axioms negative_cubic_coefficient_lower
#print axioms cubic_lower
#print axioms cubic_upper
#print axioms cubic_range

end ResearchCommons.BernsteinExpRange
