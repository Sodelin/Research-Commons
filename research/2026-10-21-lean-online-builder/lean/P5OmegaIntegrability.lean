import P5SquareTriangle
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MeasureTheory Set

namespace P5OriginalGenerator

variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

noncomputable def omega (F B C : E) : E :=
  B*F*C - (1/2 : ℂ) • (B*C*F+F*(B*C))

theorem omega_unit_bound (F B C : E) (hB : ‖B‖ ≤ 1) (hC : ‖C‖ ≤ 1) :
    ‖omega F B C‖ ≤ 2*‖F‖ := by
  have hBC : ‖B*C‖ ≤ 1 := by
    calc
      _ ≤ ‖B‖*‖C‖ := norm_mul_le B C
      _ ≤ 1*1 := mul_le_mul hB hC (norm_nonneg C) (by norm_num)
      _ = 1 := by ring
  have hBF : ‖B*F‖ ≤ ‖F‖ := by
    calc
      _ ≤ ‖B‖*‖F‖ := norm_mul_le B F
      _ ≤ 1*‖F‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg F)
      _ = ‖F‖ := one_mul _
  have hBFC : ‖B*F*C‖ ≤ ‖F‖ := by
    calc
      _ ≤ ‖B*F‖*‖C‖ := norm_mul_le (B*F) C
      _ ≤ ‖F‖*1 := mul_le_mul hBF hC (norm_nonneg C) (norm_nonneg F)
      _ = ‖F‖ := mul_one _
  have hBCF : ‖B*C*F‖ ≤ ‖F‖ := by
    calc
      _ ≤ ‖B*C‖*‖F‖ := norm_mul_le (B*C) F
      _ ≤ 1*‖F‖ := mul_le_mul_of_nonneg_right hBC (norm_nonneg F)
      _ = ‖F‖ := one_mul _
  have hFBC : ‖F*(B*C)‖ ≤ ‖F‖ := by
    calc
      _ ≤ ‖F‖*‖B*C‖ := norm_mul_le F (B*C)
      _ ≤ ‖F‖*1 := mul_le_mul_of_nonneg_left hBC (norm_nonneg F)
      _ = ‖F‖ := mul_one _
  have hsum : ‖B*C*F+F*(B*C)‖ ≤ 2*‖F‖ := by
    have h := norm_add_le (B*C*F) (F*(B*C))
    linarith
  have hhalf : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  calc
    _ ≤ ‖B*F*C‖ + ‖(1/2 : ℂ) • (B*C*F+F*(B*C))‖ := norm_sub_le _ _
    _ = ‖B*F*C‖ + (1/2 : ℝ)*‖B*C*F+F*(B*C)‖ := by rw [norm_smul,hhalf]
    _ ≤ _ := by linarith

/-- The actual fixed-F ordered Omega kernel has a square L1 witness. Its
continuous operator factor has separable range because its DOMAIN is R x R. -/
theorem omega_square_integrable (F : E) (A : ℝ → E) (Phi : ℝ → ℂ)
    (T C0 : ℝ) (hT : 0 ≤ T) (hC0 : 0 ≤ C0) (hA : Continuous A)
    (hAnorm : ∀ t, ‖A t‖ ≤ 1) (hPhi : Measurable Phi)
    (hPhinorm : ∀ t, ‖Phi t‖ ≤ C0) :
    IntegrableOn
      (fun p : ℝ × ℝ => Phi (p.2-p.1) • omega F (A p.1) (A p.2))
      (uIoc 0 T ×ˢ uIoc 0 T) := by
  have hq : Continuous (fun p : ℝ × ℝ => omega F (A p.1) (A p.2)) := by
    unfold omega
    fun_prop
  have hb : StronglyMeasurable (fun p : ℝ × ℝ => Phi (p.2-p.1)) :=
    (hPhi.comp (measurable_snd.sub measurable_fst)).stronglyMeasurable
  have hk := hb.smul hq.stronglyMeasurable
  have hfinite : volume (uIoc 0 T ×ˢ uIoc 0 T) < ⊤ := by
    rw [uIoc_of_le hT]
    exact lt_of_le_of_lt
      (measure_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  letI : IsFiniteMeasure (volume.restrict (uIoc 0 T ×ˢ uIoc 0 T)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  apply (integrable_const (2*C0*‖F‖)).mono' hk.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  change ‖Phi (p.2-p.1) • omega F (A p.1) (A p.2)‖ ≤ 2*C0*‖F‖
  rw [norm_smul]
  calc
    _ ≤ C0*(2*‖F‖) := mul_le_mul (hPhinorm _) (omega_unit_bound F _ _ (hAnorm _) (hAnorm _))
      (norm_nonneg _) hC0
    _ = _ := by ring

theorem omega_square_to_triangles (F : E) (A : ℝ → E) (Phi : ℝ → ℂ)
    (T C0 : ℝ) (hT : 0 ≤ T) (hC0 : 0 ≤ C0) (hA : Continuous A)
    (hAnorm : ∀ t, ‖A t‖ ≤ 1) (hPhi : Measurable Phi)
    (hPhinorm : ∀ t, ‖Phi t‖ ≤ C0) :
    (∫ s in 0..T, ∫ t in 0..T, Phi (t-s) • omega F (A s) (A t)) =
      ∫ u in 0..T, ∫ r in 0..(T-u),
        (Phi (-r) • omega F (A (u+r)) (A u) + Phi r • omega F (A u) (A (u+r))) :=
  bath_square_to_triangles A Phi (omega F) hT
    (omega_square_integrable F A Phi T C0 hT hC0 hA hAnorm hPhi hPhinorm)

end P5OriginalGenerator
