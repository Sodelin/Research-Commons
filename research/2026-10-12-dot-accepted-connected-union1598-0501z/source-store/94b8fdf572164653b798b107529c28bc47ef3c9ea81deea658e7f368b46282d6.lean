import G3CriticalFinSixExpansion
import G3CriticalSourceFactors5

noncomputable section
namespace GProgram.G3.CriticalCertificates
open Polynomial
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def s5PSourceRows : List (List ℤ) := addRows (addRows (addRows (addRows (addRows (mulRows [scaleCoeffs (1-(5:ℤ)^1) normalRow0] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(3:ℕ)-1]]) ([[1], [5^(6:ℕ)-1]])) ([[1], [5^(10:ℕ)-1]])) ([[1], [5^(15:ℕ)-1]])) ([[1], [5^(21:ℕ)-1]]))) (mulRows [scaleCoeffs (1-(5:ℤ)^3) normalRow1] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(1:ℕ)-1]]) ([[1], [5^(6:ℕ)-1]])) ([[1], [5^(10:ℕ)-1]])) ([[1], [5^(15:ℕ)-1]])) ([[1], [5^(21:ℕ)-1]])))) (mulRows [scaleCoeffs (1-(5:ℤ)^6) normalRow2] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(1:ℕ)-1]]) ([[1], [5^(3:ℕ)-1]])) ([[1], [5^(10:ℕ)-1]])) ([[1], [5^(15:ℕ)-1]])) ([[1], [5^(21:ℕ)-1]])))) (mulRows [scaleCoeffs (1-(5:ℤ)^10) normalRow3] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(1:ℕ)-1]]) ([[1], [5^(3:ℕ)-1]])) ([[1], [5^(6:ℕ)-1]])) ([[1], [5^(15:ℕ)-1]])) ([[1], [5^(21:ℕ)-1]])))) (mulRows [scaleCoeffs (1-(5:ℤ)^15) normalRow4] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(1:ℕ)-1]]) ([[1], [5^(3:ℕ)-1]])) ([[1], [5^(6:ℕ)-1]])) ([[1], [5^(10:ℕ)-1]])) ([[1], [5^(21:ℕ)-1]])))) (mulRows [scaleCoeffs (1-(5:ℤ)^21) normalRow5] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(1:ℕ)-1]]) ([[1], [5^(3:ℕ)-1]])) ([[1], [5^(6:ℕ)-1]])) ([[1], [5^(10:ℕ)-1]])) ([[1], [5^(15:ℕ)-1]])))
def s5Q0SourceRows : List (List ℤ) := addRows (addRows (addRows (addRows (addRows (mulRows [scaleCoeffs ((1:ℤ)*(5:ℤ)^0) normalRow0] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(3:ℕ)-1]]) ([[1], [5^(6:ℕ)-1]])) ([[1], [5^(10:ℕ)-1]])) ([[1], [5^(15:ℕ)-1]])) ([[1], [5^(21:ℕ)-1]]))) (mulRows [scaleCoeffs ((3:ℤ)*(5:ℤ)^2) normalRow1] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(1:ℕ)-1]]) ([[1], [5^(6:ℕ)-1]])) ([[1], [5^(10:ℕ)-1]])) ([[1], [5^(15:ℕ)-1]])) ([[1], [5^(21:ℕ)-1]])))) (mulRows [scaleCoeffs ((6:ℤ)*(5:ℤ)^5) normalRow2] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(1:ℕ)-1]]) ([[1], [5^(3:ℕ)-1]])) ([[1], [5^(10:ℕ)-1]])) ([[1], [5^(15:ℕ)-1]])) ([[1], [5^(21:ℕ)-1]])))) (mulRows [scaleCoeffs ((10:ℤ)*(5:ℤ)^9) normalRow3] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(1:ℕ)-1]]) ([[1], [5^(3:ℕ)-1]])) ([[1], [5^(6:ℕ)-1]])) ([[1], [5^(15:ℕ)-1]])) ([[1], [5^(21:ℕ)-1]])))) (mulRows [scaleCoeffs ((15:ℤ)*(5:ℤ)^14) normalRow4] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(1:ℕ)-1]]) ([[1], [5^(3:ℕ)-1]])) ([[1], [5^(6:ℕ)-1]])) ([[1], [5^(10:ℕ)-1]])) ([[1], [5^(21:ℕ)-1]])))) (mulRows [scaleCoeffs ((21:ℤ)*(5:ℤ)^20) normalRow5] (mulRows (mulRows (mulRows (mulRows ([[1], [5^(1:ℕ)-1]]) ([[1], [5^(3:ℕ)-1]])) ([[1], [5^(6:ℕ)-1]])) ([[1], [5^(10:ℕ)-1]])) ([[1], [5^(15:ℕ)-1]])))

theorem s5_P_source_coefficients : s5PSourceRows = s5PRows := by decide
theorem s5_Q0_source_coefficients : mulRows [[1], [-1]] s5QRows = s5Q0SourceRows := by decide

theorem s5_P_source_binding (r : ℝ) :
    evalRows r s5PRows = AllResidue.criticalProbabilityPolynomial
      (AllResidue.normalWeight r) AllResidue.capSevenExponent 5 := by
  rw [← s5_P_source_coefficients]
  simp only [s5PSourceRows, evalRows_add, evalRows_mul, evalRows_const, ofCoeffs_scale, Polynomial.eval₂_mul, Polynomial.eval₂_C, evalRows_factor, normalRow0_eval, normalRow1_eval, normalRow2_eval, normalRow3_eval, normalRow4_eval, normalRow5_eval]
  norm_num [AllResidue.criticalProbabilityPolynomial, fin6_sum_expansion,
    fin6_prod_erase_0, fin6_prod_erase_1, fin6_prod_erase_2, fin6_prod_erase_3, fin6_prod_erase_4, fin6_prod_erase_5, AllResidue.normalWeight, AllResidue.capSevenExponent]
  <;> simp only [Polynomial.C_ofNat, Polynomial.C_1, Polynomial.C_0]
  <;> ring

theorem s5_Q0_source_binding (r : ℝ) :
    (1-X) * evalRows r s5QRows = AllResidue.sourceQProbabilityPolynomial
      (AllResidue.normalWeight r) AllResidue.capSevenExponent 5 := by
  have hf : evalRows r [[1], [-1]] = (1-X : Polynomial ℝ) := by
    simp [evalRows, ofRows, ofCoeffs, sub_eq_add_neg]
  rw [← hf, ← evalRows_mul, s5_Q0_source_coefficients]
  simp only [s5Q0SourceRows, evalRows_add, evalRows_mul, evalRows_const, ofCoeffs_scale, Polynomial.eval₂_mul, Polynomial.eval₂_C, evalRows_factor, normalRow0_eval, normalRow1_eval, normalRow2_eval, normalRow3_eval, normalRow4_eval, normalRow5_eval]
  norm_num [AllResidue.sourceQProbabilityPolynomial, fin6_sum_expansion,
    fin6_prod_erase_0, fin6_prod_erase_1, fin6_prod_erase_2, fin6_prod_erase_3, fin6_prod_erase_4, fin6_prod_erase_5, AllResidue.normalWeight, AllResidue.capSevenExponent]
  <;> simp only [Polynomial.C_ofNat, Polynomial.C_1, Polynomial.C_0]
  <;> ring

#print axioms s5_P_source_binding
#print axioms s5_Q0_source_binding
end GProgram.G3.CriticalCertificates
