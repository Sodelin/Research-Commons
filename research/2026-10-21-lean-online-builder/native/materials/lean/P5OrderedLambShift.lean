import P5OmegaIntegrability
import P5OrderedTriangle
import BoundedTriangleIntegral
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Positivity

open MeasureTheory Set

namespace P5OriginalGenerator

variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

noncomputable def orderedLambKernel (A : ℝ → E) (Phi : ℝ → ℂ) (p : ℝ × ℝ) : E :=
  Phi (-p.2) • (A (p.1+p.2)*A p.1) - Phi p.2 • (A p.1*A (p.1+p.2))

noncomputable def triangleOmegaKernel (F : E) (A : ℝ → E) (Phi : ℝ → ℂ)
    (p : ℝ × ℝ) : E :=
  Phi (-p.2) • omega F (A (p.1+p.2)) (A p.1) +
    Phi p.2 • omega F (A p.1) (A (p.1+p.2))

noncomputable def orderedLambOperator (A : ℝ → E) (Phi : ℝ → ℂ) (T : ℝ) : E :=
  ∫ u in 0..T, ∫ r in 0..(T-u), orderedLambKernel A Phi (u,r)

theorem ordered_lamb_shift_identity (F : E) (A : ℝ → E) (Phi : ℝ → ℂ)
    (T C0 : ℝ) (hT : 0 ≤ T) (hC0 : 0 ≤ C0) (hA : Continuous A)
    (hAnorm : ∀ t, ‖A t‖ ≤ 1) (hPhi : Measurable Phi)
    (hPhinorm : ∀ t, ‖Phi t‖ ≤ C0) :
    (∫ s in 0..T, ∫ t in 0..T, Phi (t-s) • omega F (A s) (A t)) -
      (1/2 : ℂ) • (orderedLambOperator A Phi T*F-F*orderedLambOperator A Phi T) =
      ∫ u in 0..T, ∫ r in 0..(T-u),
        (Phi r • ((A u*F-F*A u)*A (u+r)) -
          Phi (-r) • (A (u+r)*(A u*F-F*A u))) := by
  have hp : StronglyMeasurable (fun p : ℝ × ℝ => Phi p.2) :=
    (hPhi.comp measurable_snd).stronglyMeasurable
  have hn : StronglyMeasurable (fun p : ℝ × ℝ => Phi (-p.2)) :=
    (hPhi.comp measurable_snd.neg).stronglyMeasurable
  have hprod1 : Continuous (fun p : ℝ × ℝ => A (p.1+p.2)*A p.1) := by fun_prop
  have hprod2 : Continuous (fun p : ℝ × ℝ => A p.1*A (p.1+p.2)) := by fun_prop
  have hJ : StronglyMeasurable (orderedLambKernel A Phi) :=
    (hn.smul hprod1.stronglyMeasurable).sub (hp.smul hprod2.stronglyMeasurable)
  have hprod (u v : ℝ) : ‖A u*A v‖ ≤ 1 := by
    calc
      _ ≤ ‖A u‖*‖A v‖ := norm_mul_le _ _
      _ ≤ 1*1 := mul_le_mul (hAnorm u) (hAnorm v) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hscale (t u v : ℝ) : ‖Phi t • (A u*A v)‖ ≤ C0 := by
    rw [norm_smul]
    calc
      _ ≤ C0*1 := mul_le_mul (hPhinorm _) (hprod _ _) (norm_nonneg _) hC0
      _ = _ := mul_one _
  have hJbound (p : ℝ × ℝ) : ‖orderedLambKernel A Phi p‖ ≤ 2*C0 := by
    have h := norm_sub_le (Phi (-p.2) • (A (p.1+p.2)*A p.1))
      (Phi p.2 • (A p.1*A (p.1+p.2)))
    exact h.trans (by linarith [hscale (-p.2) (p.1+p.2) p.1,hscale p.2 p.1 (p.1+p.2)])
  have hO1 : Continuous (fun p : ℝ × ℝ => omega F (A (p.1+p.2)) (A p.1)) := by
    unfold omega; fun_prop
  have hO2 : Continuous (fun p : ℝ × ℝ => omega F (A p.1) (A (p.1+p.2))) := by
    unfold omega; fun_prop
  have hO : StronglyMeasurable (triangleOmegaKernel F A Phi) :=
    (hn.smul hO1.stronglyMeasurable).add (hp.smul hO2.stronglyMeasurable)
  have hsOmega (t u v : ℝ) : ‖Phi t • omega F (A u) (A v)‖ ≤ C0*(2*‖F‖) := by
    rw [norm_smul]
    exact mul_le_mul (hPhinorm _) (omega_unit_bound F _ _ (hAnorm _) (hAnorm _))
      (norm_nonneg _) hC0
  have hObound (p : ℝ × ℝ) : ‖triangleOmegaKernel F A Phi p‖ ≤ 4*C0*‖F‖ := by
    have h := norm_add_le (Phi (-p.2) • omega F (A (p.1+p.2)) (A p.1))
      (Phi p.2 • omega F (A p.1) (A (p.1+p.2)))
    exact h.trans (by nlinarith [hsOmega (-p.2) (p.1+p.2) p.1,hsOmega p.2 p.1 (p.1+p.2)])
  have hJi := BoundedTriangleIntegral.bounded_triangle_integrable
    (orderedLambKernel A Phi) (2*C0) T (by positivity) hT hJ hJbound
  have hOi := BoundedTriangleIntegral.bounded_triangle_integrable
    (triangleOmegaKernel F A Phi) (4*C0*‖F‖) T (by positivity) hT hO hObound
  let L : E →L[ℂ] E := ((ContinuousLinearMap.mul ℂ E).flip F)-ContinuousLinearMap.mul ℂ E F
  have hL (x : E) : L x = x*F-F*x := rfl
  have lint {f : ℝ → E} {a b : ℝ} (hi : IntervalIntegrable f volume a b) :
      IntervalIntegrable (fun x => L (f x)) volume a b :=
    ⟨L.integrable_comp hi.1,L.integrable_comp hi.2⟩
  have hpoint (u r : ℝ) :
      triangleOmegaKernel F A Phi (u,r) - (1/2 : ℂ) • L (orderedLambKernel A Phi (u,r)) =
      Phi r • ((A u*F-F*A u)*A (u+r)) - Phi (-r) • (A (u+r)*(A u*F-F*A u)) := by
    rw [hL]
    have h := ordered_triangle_identity (A (u+r)) (A u) F (Phi (-r)) (Phi r)
    convert h using 1 <;>
      simp only [triangleOmegaKernel,orderedLambKernel,omega,sub_mul,mul_sub,
        smul_sub,smul_mul_assoc,mul_smul_comm] <;> module
  have hinner (u : ℝ) :
      (∫ r in 0..(T-u), Phi r • ((A u*F-F*A u)*A (u+r)) -
        Phi (-r) • (A (u+r)*(A u*F-F*A u))) =
      (∫ r in 0..(T-u), triangleOmegaKernel F A Phi (u,r)) -
        (1/2 : ℂ) • L (∫ r in 0..(T-u), orderedLambKernel A Phi (u,r)) := by
    simp_rw [← hpoint]
    have hsmall : IntervalIntegrable
        (fun r => (1/2 : ℂ) • L (orderedLambKernel A Phi (u,r))) volume 0 (T-u) :=
      (lint (hJi.1 u)).smul (1/2 : ℂ)
    rw [intervalIntegral.integral_sub (hOi.1 u) hsmall,
      intervalIntegral.integral_smul (1/2 : ℂ) (fun r => L (orderedLambKernel A Phi (u,r))),
      L.intervalIntegral_comp_comm (hJi.1 u)]
  rw [omega_square_to_triangles F A Phi T C0 hT hC0 hA hAnorm hPhi hPhinorm]
  change (∫ u in 0..T, ∫ r in 0..(T-u), triangleOmegaKernel F A Phi (u,r)) -
    (1/2 : ℂ) • L (∫ u in 0..T, ∫ r in 0..(T-u), orderedLambKernel A Phi (u,r)) = _
  simp_rw [hinner]
  have hlarge : IntervalIntegrable (fun u =>
      (1/2 : ℂ) • L (∫ r in 0..(T-u), orderedLambKernel A Phi (u,r))) volume 0 T :=
    (lint hJi.2).smul (1/2 : ℂ)
  rw [intervalIntegral.integral_sub hOi.2 hlarge,
    intervalIntegral.integral_smul (1/2 : ℂ)
      (fun u => L (∫ r in 0..(T-u), orderedLambKernel A Phi (u,r))),
    L.intervalIntegral_comp_comm hJi.2]

end P5OriginalGenerator
