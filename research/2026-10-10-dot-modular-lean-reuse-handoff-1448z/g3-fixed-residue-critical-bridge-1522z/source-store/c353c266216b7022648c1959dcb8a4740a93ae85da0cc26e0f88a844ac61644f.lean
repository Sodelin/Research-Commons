import G3CriticalSliceSourceBinding3
import G3CriticalSliceSourceBinding5
import G3CriticalSourceBlockAssembly3
import G3CriticalSourceBlockAssembly5
import G3CriticalExportedNoCommon

/-! The actual-source, two-slice coprimality interface. The witnesses 3 and5
are algebraic elimination specializations, outside the strict source square. -/
noncomputable section
namespace GProgram.G3.CriticalCertificates
open Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem coprime_of_integer_source_bezout
    (P Q : Polynomial (Polynomial ℤ)) (E : Polynomial ℤ) (K : ℤ) (r : ℝ)
    (hK : K ≠ 0) (hE : E.eval₂ (Int.castRingHom ℝ) r ≠ 0)
    (h : ∃ u v : Polynomial (Polynomial ℤ), u*P+v*Q=C (C K*E)) :
    IsCoprime (P.map (Polynomial.eval₂RingHom (Int.castRingHom ℝ) r))
      (Q.map (Polynomial.eval₂RingHom (Int.castRingHom ℝ) r)) := by
  obtain ⟨u,v,h⟩ := h
  let φ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) r
  let d : ℝ := (K : ℝ) * E.eval₂ (Int.castRingHom ℝ) r
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  have hd : d ≠ 0 := mul_ne_zero hk hE
  have hm := congrArg (Polynomial.map φ) h
  have hm' : u.map φ * P.map φ + v.map φ * Q.map φ = C d := by
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Int.coe_castRingHom, d] using hm
  refine ⟨C d⁻¹ * u.map φ, C d⁻¹ * v.map φ, ?_⟩
  calc
    _ = C d⁻¹ * (u.map φ * P.map φ + v.map φ * Q.map φ) := by ring
    _ = C d⁻¹ * C d := by rw [hm']
    _ = 1 := by rw [← map_mul]; simp [hd]

private theorem quotient_from_factorization (P Q : Polynomial ℝ)
    (h : (1-X)*Q=P) : -(P /ₘ (X-C 1)) = Q := by
  have hp : P = (X-C 1)*(-Q) := by rw [← h]; simp only [map_one]; ring
  rw [hp, Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_sub_C _), neg_neg]

theorem actual_slice_coprime {r : ℝ} (hr : 0 < r) :
    IsCoprime
      (AllResidue.criticalProbabilityPolynomial (AllResidue.normalWeight r) AllResidue.capSevenExponent 3)
      (-(AllResidue.sourceQProbabilityPolynomial (AllResidue.normalWeight r) AllResidue.capSevenExponent 3 /ₘ (X-C 1))) ∨
    IsCoprime
      (AllResidue.criticalProbabilityPolynomial (AllResidue.normalWeight r) AllResidue.capSevenExponent 5)
      (-(AllResidue.sourceQProbabilityPolynomial (AllResidue.normalWeight r) AllResidue.capSevenExponent 5 /ₘ (X-C 1))) := by
  obtain h3 | h5 := exported_no_common_positive_root hr
  · left
    have h := coprime_of_integer_source_bezout (ofRows s3PRows) (ofRows s3QRows)
      (ofCoeffs e3Coeffs) s3K r s3_K_ne_zero h3 s3_source_bezout
    change IsCoprime (evalRows r s3PRows) (evalRows r s3QRows) at h
    rw [s3_P_source_binding, ← quotient_from_factorization _ _ (s3_Q0_source_binding r)] at h
    exact h
  · right
    have h := coprime_of_integer_source_bezout (ofRows s5PRows) (ofRows s5QRows)
      (ofCoeffs e5Coeffs) s5K r s5_K_ne_zero h5 s5_source_bezout
    change IsCoprime (evalRows r s5PRows) (evalRows r s5QRows) at h
    rw [s5_P_source_binding, ← quotient_from_factorization _ _ (s5_Q0_source_binding r)] at h
    exact h

#print axioms actual_slice_coprime
end GProgram.G3.CriticalCertificates
