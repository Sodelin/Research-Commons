import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set

namespace BoundedTriangleIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem bounded_interval_integrable (f : ℝ → E) (C a b : ℝ)
    (hf : StronglyMeasurable f) (hbound : ∀ x, ‖f x‖ ≤ C) :
    IntervalIntegrable f volume a b := by
  apply intervalIntegrable_iff.mpr
  have hc : IntegrableOn (fun _ : ℝ => C) (uIoc a b) :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume a b).def'
  exact hc.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/-- Actual individually bounded sections plus the outer measurability witness.
This is stronger input than an arbitrary product L1 function. -/
theorem bounded_triangle_integrable (f : ℝ × ℝ → E) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hf : StronglyMeasurable f)
    (hbound : ∀ p, ‖f p‖ ≤ C) :
    (∀ u, IntervalIntegrable (fun r => f (u,r)) volume 0 (T-u)) ∧
      IntervalIntegrable (fun u => ∫ r in 0..(T-u), f (u,r)) volume 0 T := by
  classical
  have hsection (u : ℝ) : StronglyMeasurable (fun r => f (u,r)) :=
    hf.comp_measurable measurable_prodMk_left
  refine ⟨fun u => bounded_interval_integrable _ C _ _ (hsection u) (fun r => hbound _),?_⟩
  let g : ℝ × ℝ → E := {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ T-p.1}.indicator f
  have hset : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ T-p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))
  have hg : StronglyMeasurable g := hf.indicator hset
  have hout : StronglyMeasurable (fun u => ∫ r, g (u,r)) := hg.integral_prod_right'
  have heq (u : ℝ) (hu : u ≤ T) :
      (∫ r in 0..(T-u), f (u,r)) = ∫ r, g (u,r) := by
    rw [intervalIntegral.integral_of_le (sub_nonneg.mpr hu)]
    calc
      _ = ∫ r, (Ioc 0 (T-u)).indicator (fun r => f (u,r)) r :=
        (integral_indicator measurableSet_Ioc).symm
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun r => by simp [g,Set.indicator])
  have heqae : (fun u => ∫ r, g (u,r)) =ᵐ[volume.restrict (Ioc 0 T)]
      (fun u => ∫ r in 0..(T-u), f (u,r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (heq u hu.2).symm
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
  have hc : IntegrableOn (fun _ : ℝ => C*T) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp intervalIntegrable_const
  apply hc.mono' (hout.aestronglyMeasurable.congr heqae)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r (_ : r ∈ uIoc 0 (T-u)) => hbound (u,r))
  rw [sub_zero,abs_of_nonneg (sub_nonneg.mpr hu.2)] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (by linarith [hu.1] : T-u ≤ T) hC)

end BoundedTriangleIntegral
