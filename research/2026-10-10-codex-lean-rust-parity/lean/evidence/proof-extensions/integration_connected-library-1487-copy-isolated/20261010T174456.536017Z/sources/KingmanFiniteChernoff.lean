import KingmanFiniteClockTail
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Uniform classical Chernoff bound for the finite holding-clock model

Dedicated Sol6.1 contribution. Every clock, moment and product integral is
explicit. No tail/MGF source conclusion is inserted as a premise. The count
trajectory, labelled jump chain, whole graph and infinite entrance law remain
separate source interpretations. No recognition-minimum claim is made.
-/

namespace GProgram.Kingman.FiniteChernoff

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open GProgram.Kingman.FiniteClockTail
open GProgram.Kingman.ClockMoments

noncomputable def hitReal (q : Nat) (ω : Fin q → ℝ) : ℝ := ∑ i, max 0 (ω i)
noncomputable def tilt (M : Nat) : ℝ := (M : ℝ)*((M : ℝ)+1)/4

theorem tilt_positive {M : Nat} (hM : 0 < M) : 0 < tilt M := by
  unfold tilt
  positivity

theorem tilt_le_half_rate {M q : Nat} (hM : 0 < M) (i : Fin q) :
    tilt M ≤ holdingRate M i/2 := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hmi := mul_nonneg hm.le hi
  unfold tilt holdingRate
  rw [Nat.cast_choose_two]
  norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
  nlinarith [sq_nonneg (i.val : ℝ)]

theorem factor_le_exp {r θ : ℝ} (hr : 0 < r) (hθ : 0 ≤ θ) (hh : θ ≤ r/2) :
    r/(r-θ) ≤ Real.exp (2*θ/r) := by
  have hd : 0 < r-θ := by linarith
  have hp := mul_nonneg hθ (show 0 ≤ r-2*θ by linarith)
  have hrat : r/(r-θ) ≤ (r+2*θ)/r :=
    (div_le_div_iff₀ hd hr).mpr (by nlinarith)
  have he : (r+2*θ)/r = 2*θ/r+1 := by field_simp [hr.ne'] <;> ring
  rw [he] at hrat
  exact hrat.trans (Real.add_one_le_exp _)

theorem exp_hitReal_product (q : Nat) (θ : ℝ) (ω : Fin q → ℝ) :
    Real.exp (θ*hitReal q ω) = ∏ i, Real.exp (θ*(max 0 (ω i))) := by
  unfold hitReal
  rw [Finset.mul_sum,Real.exp_sum]

theorem finite_mgf_integrable {M : Nat} (hM : 0 < M) (q : Nat) {θ : ℝ}
    (hθ : ∀ i : Fin q, θ < holdingRate M i) :
    Integrable (fun ω => Real.exp (θ*hitReal q ω)) (clocks M q) := by
  letI : ∀ i : Fin q, IsProbabilityMeasure (expMeasure (holdingRate M i)) :=
    fun i => isProbabilityMeasure_expMeasure (holdingRate_positive hM i)
  simp_rw [exp_hitReal_product]
  unfold clocks
  exact Integrable.fintype_prod
    (fun i => exponential_positivePart_integrable (holdingRate_positive hM i) (hθ i))

theorem finite_mgf_exact {M : Nat} (hM : 0 < M) (q : Nat) {θ : ℝ}
    (hθ : ∀ i : Fin q, θ < holdingRate M i) :
    (∫ ω, Real.exp (θ*hitReal q ω) ∂clocks M q) =
      ∏ i : Fin q, holdingRate M i/(holdingRate M i-θ) := by
  letI : ∀ i : Fin q, IsProbabilityMeasure (expMeasure (holdingRate M i)) :=
    fun i => isProbabilityMeasure_expMeasure (holdingRate_positive hM i)
  simp_rw [exp_hitReal_product]
  unfold clocks
  have hh := integral_fintype_prod_eq_prod
    (μ := fun i : Fin q => expMeasure (holdingRate M i))
    (fun (_i : Fin q) (x : ℝ) => Real.exp (θ*(max 0 x)))
  rw [hh]
  apply Finset.prod_congr rfl
  intro i _
  exact exponential_positivePart_integral (holdingRate_positive hM i) (hθ i)

theorem product_bound {M : Nat} (hM : 0 < M) (q : Nat) :
    (∏ i : Fin q, holdingRate M i/(holdingRate M i-tilt M)) ≤ Real.exp ((M : ℝ)+1) := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have ht := tilt_positive hM
  have hb : (∏ i : Fin q, holdingRate M i/(holdingRate M i-tilt M)) ≤
      ∏ i : Fin q, Real.exp (2*tilt M/holdingRate M i) := by
    apply Finset.prod_le_prod
    · intro i _
      exact div_nonneg (holdingRate_positive hM i).le (by
        have h := tilt_le_half_rate hM i
        have hp := holdingRate_positive hM i
        linarith)
    · intro i _
      exact factor_le_exp (holdingRate_positive hM i) ht.le (tilt_le_half_rate hM i)
  rw [← Real.exp_sum] at hb
  have hs : (∑ i : Fin q, 2*tilt M/holdingRate M i) = 2*tilt M*reciprocalSum M q := by
    unfold reciprocalSum
    rw [← Fin.sum_univ_eq_sum_range (fun j => 1/((M+j+1).choose 2 : ℝ)) q,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold holdingRate
    ring
  rw [hs] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (reciprocalSum_le hM q) (by positivity : 0 ≤ 2*tilt M)
  have he : 2*tilt M*(2/(M : ℝ)) = (M : ℝ)+1 := by
    unfold tilt
    field_simp [hm.ne'] <;> ring
  rwa [he] at hh

theorem uniform_chernoff_tail {M : Nat} (hM : 0 < M) (q : Nat) (t : ℝ) :
    (clocks M q).real {ω | t ≤ hitReal q ω} ≤
      Real.exp ((M : ℝ)+1-t*tilt M) := by
  have ht := tilt_positive hM
  have hθ (i : Fin q) : tilt M < holdingRate M i := by
    have hp := holdingRate_positive hM i
    have hh := tilt_le_half_rate hM i
    linarith
  have h_int := finite_mgf_integrable hM q hθ
  have he : {ω : Fin q → ℝ | Real.exp (tilt M*t) ≤ Real.exp (tilt M*hitReal q ω)} =
      {ω | t ≤ hitReal q ω} := by
    ext ω
    simp only [Set.mem_setOf_eq,Real.exp_le_exp]
    exact ⟨fun h => le_of_mul_le_mul_left h ht,
      fun h => mul_le_mul_of_nonneg_left h ht.le⟩
  have hb := mul_meas_ge_le_integral_of_nonneg
    (μ := clocks M q) (Filter.Eventually.of_forall (fun ω => (Real.exp_pos (tilt M*hitReal q ω)).le))
    h_int (Real.exp (tilt M*t))
  rw [he,finite_mgf_exact hM q hθ] at hb
  have hbound := hb.trans (product_bound hM q)
  have hdiv : (clocks M q).real {ω | t ≤ hitReal q ω} ≤
      Real.exp ((M : ℝ)+1)/Real.exp (tilt M*t) :=
    (le_div_iff₀' (Real.exp_pos _)).mpr hbound
  simpa only [← Real.exp_sub,mul_comm] using hdiv

#print axioms finite_mgf_exact
#print axioms product_bound
#print axioms uniform_chernoff_tail

end GProgram.Kingman.FiniteChernoff
