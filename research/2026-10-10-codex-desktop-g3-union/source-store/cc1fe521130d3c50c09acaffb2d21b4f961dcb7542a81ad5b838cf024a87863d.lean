import G3CriticalModularLifting
import G3CriticalPositiveProduct

/-! No common positive real root of the exact exported slice polynomials.
The source-polynomial Bezout bindings are a separate required bridge. -/
noncomputable section
namespace GProgram.G3.CriticalCertificates
open Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def E3 : Polynomial ℤ := ofCoeffs e3Coeffs
def E5 : Polynomial ℤ := ofCoeffs e5Coeffs

theorem E3_eq_product : E3 = ofCoeffs gCoeffs * H3 := by
  have h := congrArg ofCoeffs integer_product_3
  simpa only [ofCoeffs_mul, E3, H3] using h.symm

theorem E5_eq_product : E5 = ofCoeffs gCoeffs * H5 := by
  have h := congrArg ofCoeffs integer_product_5
  simpa only [ofCoeffs_mul, E5, H5] using h.symm

theorem exported_no_common_positive_root {r : ℝ} (hr : 0 < r) :
    E3.eval₂ (Int.castRingHom ℝ) r ≠ 0 ∨
    E5.eval₂ (Int.castRingHom ℝ) r ≠ 0 := by
  by_contra! h
  have hg : (ofCoeffs gCoeffs).eval₂ (Int.castRingHom ℝ) r ≠ 0 := ne_of_gt (g_eval_pos hr)
  rw [E3_eq_product, Polynomial.eval₂_mul] at h
  rw [E5_eq_product, Polynomial.eval₂_mul] at h
  have h3 := (mul_eq_zero.mp h.1).resolve_left hg
  have h5 := (mul_eq_zero.mp h.2).resolve_left hg
  apply quotients_no_common_real_root r
  simpa only [Polynomial.eval_map] using And.intro h3 h5

#print axioms exported_no_common_positive_root
end GProgram.G3.CriticalCertificates
