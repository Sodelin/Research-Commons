import G3CriticalFinSixExpansion
import G3CriticalSourceFactors3

noncomputable section
namespace GProgram.G3.CriticalCertificates
open Polynomial
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def s3PSourceRows : List (List ℤ) := addRows (addRows (addRows (addRows (addRows (mulRows [scaleCoeffs (1-(3:ℤ)^1) normalRow0] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(3:ℕ)-1]]) ([[1], [3^(6:ℕ)-1]])) ([[1], [3^(10:ℕ)-1]])) ([[1], [3^(15:ℕ)-1]])) ([[1], [3^(21:ℕ)-1]]))) (mulRows [scaleCoeffs (1-(3:ℤ)^3) normalRow1] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(1:ℕ)-1]]) ([[1], [3^(6:ℕ)-1]])) ([[1], [3^(10:ℕ)-1]])) ([[1], [3^(15:ℕ)-1]])) ([[1], [3^(21:ℕ)-1]])))) (mulRows [scaleCoeffs (1-(3:ℤ)^6) normalRow2] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(1:ℕ)-1]]) ([[1], [3^(3:ℕ)-1]])) ([[1], [3^(10:ℕ)-1]])) ([[1], [3^(15:ℕ)-1]])) ([[1], [3^(21:ℕ)-1]])))) (mulRows [scaleCoeffs (1-(3:ℤ)^10) normalRow3] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(1:ℕ)-1]]) ([[1], [3^(3:ℕ)-1]])) ([[1], [3^(6:ℕ)-1]])) ([[1], [3^(15:ℕ)-1]])) ([[1], [3^(21:ℕ)-1]])))) (mulRows [scaleCoeffs (1-(3:ℤ)^15) normalRow4] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(1:ℕ)-1]]) ([[1], [3^(3:ℕ)-1]])) ([[1], [3^(6:ℕ)-1]])) ([[1], [3^(10:ℕ)-1]])) ([[1], [3^(21:ℕ)-1]])))) (mulRows [scaleCoeffs (1-(3:ℤ)^21) normalRow5] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(1:ℕ)-1]]) ([[1], [3^(3:ℕ)-1]])) ([[1], [3^(6:ℕ)-1]])) ([[1], [3^(10:ℕ)-1]])) ([[1], [3^(15:ℕ)-1]])))
def s3Q0SourceRows : List (List ℤ) := addRows (addRows (addRows (addRows (addRows (mulRows [scaleCoeffs ((1:ℤ)*(3:ℤ)^0) normalRow0] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(3:ℕ)-1]]) ([[1], [3^(6:ℕ)-1]])) ([[1], [3^(10:ℕ)-1]])) ([[1], [3^(15:ℕ)-1]])) ([[1], [3^(21:ℕ)-1]]))) (mulRows [scaleCoeffs ((3:ℤ)*(3:ℤ)^2) normalRow1] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(1:ℕ)-1]]) ([[1], [3^(6:ℕ)-1]])) ([[1], [3^(10:ℕ)-1]])) ([[1], [3^(15:ℕ)-1]])) ([[1], [3^(21:ℕ)-1]])))) (mulRows [scaleCoeffs ((6:ℤ)*(3:ℤ)^5) normalRow2] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(1:ℕ)-1]]) ([[1], [3^(3:ℕ)-1]])) ([[1], [3^(10:ℕ)-1]])) ([[1], [3^(15:ℕ)-1]])) ([[1], [3^(21:ℕ)-1]])))) (mulRows [scaleCoeffs ((10:ℤ)*(3:ℤ)^9) normalRow3] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(1:ℕ)-1]]) ([[1], [3^(3:ℕ)-1]])) ([[1], [3^(6:ℕ)-1]])) ([[1], [3^(15:ℕ)-1]])) ([[1], [3^(21:ℕ)-1]])))) (mulRows [scaleCoeffs ((15:ℤ)*(3:ℤ)^14) normalRow4] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(1:ℕ)-1]]) ([[1], [3^(3:ℕ)-1]])) ([[1], [3^(6:ℕ)-1]])) ([[1], [3^(10:ℕ)-1]])) ([[1], [3^(21:ℕ)-1]])))) (mulRows [scaleCoeffs ((21:ℤ)*(3:ℤ)^20) normalRow5] (mulRows (mulRows (mulRows (mulRows ([[1], [3^(1:ℕ)-1]]) ([[1], [3^(3:ℕ)-1]])) ([[1], [3^(6:ℕ)-1]])) ([[1], [3^(10:ℕ)-1]])) ([[1], [3^(15:ℕ)-1]])))

theorem s3_P_source_coefficients : s3PSourceRows = s3PRows := by decide
theorem s3_Q0_source_coefficients : mulRows [[1], [-1]] s3QRows = s3Q0SourceRows := by decide

theorem s3_P_source_binding (r : ℝ) :
    evalRows r s3PRows = AllResidue.criticalProbabilityPolynomial
      (AllResidue.normalWeight r) AllResidue.capSevenExponent 3 := by
  rw [← s3_P_source_coefficients]
  simp only [s3PSourceRows, evalRows_add, evalRows_mul, evalRows_const, ofCoeffs_scale, Polynomial.eval₂_mul, Polynomial.eval₂_C, evalRows_factor, normalRow0_eval, normalRow1_eval, normalRow2_eval, normalRow3_eval, normalRow4_eval, normalRow5_eval]
  norm_num [AllResidue.criticalProbabilityPolynomial, fin6_sum_expansion,
    fin6_prod_erase_0, fin6_prod_erase_1, fin6_prod_erase_2, fin6_prod_erase_3, fin6_prod_erase_4, fin6_prod_erase_5, AllResidue.normalWeight, AllResidue.capSevenExponent]
  <;> simp only [Polynomial.C_ofNat, Polynomial.C_1, Polynomial.C_0]
  <;> ring

theorem s3_Q0_source_binding (r : ℝ) :
    (1-X) * evalRows r s3QRows = AllResidue.sourceQProbabilityPolynomial
      (AllResidue.normalWeight r) AllResidue.capSevenExponent 3 := by
  have hf : evalRows r [[1], [-1]] = (1-X : Polynomial ℝ) := by
    simp [evalRows, ofRows, ofCoeffs, sub_eq_add_neg]
  rw [← hf, ← evalRows_mul, s3_Q0_source_coefficients]
  simp only [s3Q0SourceRows, evalRows_add, evalRows_mul, evalRows_const, ofCoeffs_scale, Polynomial.eval₂_mul, Polynomial.eval₂_C, evalRows_factor, normalRow0_eval, normalRow1_eval, normalRow2_eval, normalRow3_eval, normalRow4_eval, normalRow5_eval]
  norm_num [AllResidue.sourceQProbabilityPolynomial, fin6_sum_expansion,
    fin6_prod_erase_0, fin6_prod_erase_1, fin6_prod_erase_2, fin6_prod_erase_3, fin6_prod_erase_4, fin6_prod_erase_5, AllResidue.normalWeight, AllResidue.capSevenExponent]
  <;> simp only [Polynomial.C_ofNat, Polynomial.C_1, Polynomial.C_0]
  <;> ring

#print axioms s3_P_source_binding
#print axioms s3_Q0_source_binding
end GProgram.G3.CriticalCertificates
