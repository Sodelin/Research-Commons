import ResearchCommonsBernstein

open scoped BigOperators
open ResearchCommons.Bernstein

namespace ResearchCommons.BernsteinTests

theorem constant_lower (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (2 : ℝ) ≤ ∑ r ∈ Finset.range (0 + 1), (fun _ : ℕ => (3 : ℝ)) r * x ^ r := by
  apply bernstein_polynomial_lower 0 (fun _ => 3) 2 _ hx
  intro d hd
  have : d = 0 := by omega
  subst d
  norm_num [bernsteinCoefficient]

theorem constant_strict (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (2 : ℝ) < ∑ r ∈ Finset.range (0 + 1), (fun _ : ℕ => (3 : ℝ)) r * x ^ r := by
  apply strict_bernstein_bound 0 (fun _ => 3) 2 _ hx
  intro d hd
  have : d = 0 := by omega
  subst d
  norm_num [bernsteinCoefficient]

def quadraticCoefficients (r : ℕ) : ℝ :=
  if r = 0 then 1 else if r = 1 then -1 else 1

theorem quadratic_coefficients :
    ∀ d < 2 + 1, (1 / 2 : ℝ) ≤ bernsteinCoefficient 2 quadraticCoefficients d := by
  intro d hd
  interval_cases d <;>
    norm_num [bernsteinCoefficient, quadraticCoefficients, Finset.sum_range_succ]

theorem quadratic_lower (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (1 / 2 : ℝ) ≤ 1 - x + x ^ 2 := by
  have h := bernstein_polynomial_lower 2 quadraticCoefficients (1 / 2) quadratic_coefficients hx
  norm_num [quadraticCoefficients, Finset.sum_range_succ] at h
  nlinarith

theorem quadratic_positive (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    0 < 1 - x + x ^ 2 := by
  have h := quadratic_lower x hx
  linarith

theorem insufficient_coefficient_bound :
    ¬ (∀ d < 2 + 1, (1 : ℝ) ≤ bernsteinCoefficient 2 quadraticCoefficients d) := by
  intro h
  have h1 := h 1 (by omega)
  norm_num [bernsteinCoefficient, quadraticCoefficients, Finset.sum_range_succ] at h1

theorem left_endpoint : bernsteinBasis 2 0 0 = 1 := by
  norm_num [bernsteinBasis]

theorem right_endpoint : bernsteinBasis 2 2 1 = 1 := by
  norm_num [bernsteinBasis]

#print axioms ResearchCommons.Bernstein.bernsteinBasis_sum
#print axioms ResearchCommons.Bernstein.bernsteinBasis_nonneg
#print axioms ResearchCommons.Bernstein.choose_ratio
#print axioms ResearchCommons.Bernstein.bernstein_monomial
#print axioms ResearchCommons.Bernstein.bernstein_polynomial
#print axioms ResearchCommons.Bernstein.bernstein_polynomial_lower
#print axioms ResearchCommons.Bernstein.strict_bernstein_bound
#print axioms constant_lower
#print axioms constant_strict
#print axioms quadratic_coefficients
#print axioms quadratic_lower
#print axioms quadratic_positive
#print axioms insufficient_coefficient_bound
#print axioms left_endpoint
#print axioms right_endpoint

end ResearchCommons.BernsteinTests

