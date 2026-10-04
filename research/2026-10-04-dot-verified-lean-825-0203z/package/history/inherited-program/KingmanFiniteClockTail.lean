import ExponentialClockMoments
import G4AllRootPairClocks
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Uniform finite initial-root holding-clock tail

Classical Kingman1982 ordinary-population pure-death clocks, pp236--239.
This module defines the finite clock product explicitly. It does not construct
an infinite entrance law or the full graph-driven labelled forest process.
-/

namespace GProgram.Kingman.FiniteClockTail

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable def holdingRate (M : Nat) {q : Nat} (i : Fin q) : ℝ :=
  (M+i.val+1).choose 2

theorem holdingRate_positive {M q : Nat} (hM : 0 < M) (i : Fin q) : 0 < holdingRate M i := by
  unfold holdingRate
  exact_mod_cast Nat.choose_pos (show 2 ≤ M+i.val+1 by omega)

noncomputable def clocks (M q : Nat) : Measure (Fin q → ℝ) :=
  Measure.pi (fun i : Fin q => expMeasure (holdingRate M i))

/-- Nonnegative clock sum. Negative real samples have zero exponential mass,
but clipping makes nonnegativity explicit on every sample, including null sets. -/
noncomputable def hitClock (q : Nat) (ω : Fin q → ℝ) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (ω i)

noncomputable def reciprocalSum (M q : Nat) : ℝ :=
  ∑ j ∈ Finset.range q, 1/((M+j+1).choose 2 : ℝ)

theorem inverse_rate_difference {M : Nat} (hM : 0 < M) (j : Nat) :
    1/((M+j+1).choose 2 : ℝ) = 2/(M+j : ℝ)-2/(M+j+1 : ℝ) := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have h0 : (M : ℝ)+j ≠ 0 := ne_of_gt (by linarith)
  have h1 : (M : ℝ)+j+1 ≠ 0 := ne_of_gt (by linarith)
  rw [Nat.cast_choose_two]
  norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
  field_simp [h0,h1] <;> ring

theorem reciprocalSum_exact {M : Nat} (hM : 0 < M) (q : Nat) :
    reciprocalSum M q = 2/(M : ℝ)-2/(M+q : ℝ) := by
  unfold reciprocalSum
  simp_rw [inverse_rate_difference hM]
  have h := Finset.sum_range_sub' (fun j : Nat => 2/(M+j : ℝ)) q
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero,add_assoc] using h

theorem reciprocalSum_le {M : Nat} (hM : 0 < M) (q : Nat) :
    reciprocalSum M q ≤ 2/(M : ℝ) := by
  rw [reciprocalSum_exact hM]
  have h : 0 ≤ 2/(M+q : ℝ) := by positivity
  linarith

theorem finite_clock_mean {M : Nat} (hM : 0 < M) (q : Nat) :
    (∫⁻ ω, hitClock q ω ∂clocks M q) = ENNReal.ofReal (reciprocalSum M q) := by
  letI : ∀ i : Fin q, IsProbabilityMeasure (expMeasure (holdingRate M i)) :=
    fun i => isProbabilityMeasure_expMeasure (holdingRate_positive hM i)
  have hmap (i : Fin q) :
      (clocks M q).map (Function.eval i) = expMeasure (holdingRate M i) := by
    unfold clocks
    rw [Measure.pi_map_eval]
    simp
  have hm (i : Fin q) : (∫⁻ ω, ENNReal.ofReal (ω i) ∂clocks M q) =
      ENNReal.ofReal (1/holdingRate M i) := by
    rw [← lintegral_map (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal x))
      (measurable_pi_apply i),hmap i,
      GProgram.Kingman.ClockMoments.exponential_first_moment (holdingRate_positive hM i)]
  unfold hitClock
  rw [lintegral_finsetSum Finset.univ (by intro i _; fun_prop)]
  simp_rw [hm]
  rw [← ENNReal.ofReal_sum_of_nonneg (by
    intro i _
    exact div_nonneg zero_le_one (holdingRate_positive hM i).le)]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun j => 1/((M+j+1).choose 2 : ℝ)) q

theorem uniform_markov_tail {M : Nat} (hM : 0 < M) (q : Nat)
    {t : ℝ} (ht : 0 < t) :
    (clocks M q {ω | ENNReal.ofReal t ≤ hitClock q ω}).toReal ≤ 2/((M : ℝ)*t) := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have hmeas : Measurable (hitClock q) := by unfold hitClock; fun_prop
  have hb := meas_ge_le_lintegral_div (μ := clocks M q) hmeas.aemeasurable
    (by positivity : ENNReal.ofReal t ≠ 0) (by simp : ENNReal.ofReal t ≠ ⊤)
  rw [finite_clock_mean hM q] at hb
  have hbound : clocks M q {ω | ENNReal.ofReal t ≤ hitClock q ω} ≤
      ENNReal.ofReal (2/((M : ℝ)*t)) := by
    apply hb.trans
    calc
      ENNReal.ofReal (reciprocalSum M q) / ENNReal.ofReal t ≤
          ENNReal.ofReal (2/(M : ℝ)) / ENNReal.ofReal t :=
        ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal (reciprocalSum_le hM q)) (ENNReal.ofReal t)
      _ = _ := by rw [← ENNReal.ofReal_div_of_pos ht,div_div]
  have hh := ENNReal.toReal_mono (by simp : ENNReal.ofReal (2/((M : ℝ)*t)) ≠ ⊤) hbound
  simpa [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2/((M : ℝ)*t))] using hh

#print axioms uniform_markov_tail
#print axioms reciprocalSum_exact
#print axioms finite_clock_mean

end GProgram.Kingman.FiniteClockTail
