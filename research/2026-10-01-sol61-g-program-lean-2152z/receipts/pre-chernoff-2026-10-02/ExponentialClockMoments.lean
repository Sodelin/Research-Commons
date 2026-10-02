import G1SharedRegisterStress
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# Actual exponential-clock first moment and exponential transform

Dedicated Sol6.1 contribution. These moments are derived from Mathlib's actual
probability density and Gamma/Exponential normalization, not assumed as source
bridge conclusions. They support later finite holding-clock tail bounds.
-/

namespace GProgram.Kingman.ClockMoments

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem first_moment_pdf_factor {r : ℝ} (hr : 0 < r) (x : ℝ) :
    exponentialPDF r x * ENNReal.ofReal x =
      ENNReal.ofReal (1/r) * gammaPDF 2 r x := by
  by_cases hx : 0 ≤ x
  · have hG : Real.Gamma 2 = 1 := by
      simpa using Real.Gamma_nat_eq_factorial 1
    rw [exponentialPDF_of_nonneg hx,gammaPDF_of_nonneg hx,hG]
    norm_num [Real.rpow_two,Real.rpow_one]
    rw [← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
    congr 1
    field_simp [hr.ne']
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_first_moment {r : ℝ} (hr : 0 < r) :
    (∫⁻ x, ENNReal.ofReal x ∂expMeasure r) = ENNReal.ofReal (1/r) := by
  change (∫⁻ x, ENNReal.ofReal x ∂volume.withDensity (exponentialPDF r)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold exponentialPDF; fun_prop) (by fun_prop)]
  simp_rw [Pi.mul_apply,first_moment_pdf_factor hr]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one (by norm_num : (0 : ℝ) < 2) hr,mul_one]

private theorem exponential_tilt_pdf_factor {r θ : ℝ} (hr : 0 < r) (hθ : θ < r) (x : ℝ) :
    exponentialPDF r x * ENNReal.ofReal (Real.exp (θ*x)) =
      ENNReal.ofReal (r/(r-θ)) * exponentialPDF (r-θ) x := by
  have hd : 0 < r-θ := sub_pos.mpr hθ
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx,exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (div_nonneg hr.le hd.le)]
    congr 1
    have he : Real.exp (-(r*x))*Real.exp (θ*x) = Real.exp (-((r-θ)*x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      r*Real.exp (-(r*x))*Real.exp (θ*x) = r*(Real.exp (-(r*x))*Real.exp (θ*x)) := by ring
      _ = r*Real.exp (-((r-θ)*x)) := by rw [he]
      _ = r/(r-θ)*((r-θ)*Real.exp (-((r-θ)*x))) := by
        field_simp [hd.ne']
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_transform {r θ : ℝ} (hr : 0 < r) (hθ : θ < r) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (θ*x)) ∂expMeasure r) =
      ENNReal.ofReal (r/(r-θ)) := by
  change (∫⁻ x, ENNReal.ofReal (Real.exp (θ*x))
    ∂volume.withDensity (exponentialPDF r)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold exponentialPDF; fun_prop) (by fun_prop)]
  simp_rw [Pi.mul_apply,exponential_tilt_pdf_factor hr hθ]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one (sub_pos.mpr hθ),mul_one]

#print axioms exponential_first_moment
#print axioms exponential_transform

end GProgram.Kingman.ClockMoments
