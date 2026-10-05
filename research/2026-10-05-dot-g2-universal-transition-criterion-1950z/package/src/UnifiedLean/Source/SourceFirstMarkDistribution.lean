import UnifiedLean.Source.SourceFirstMergerMark

/-!
# Derived ACTUAL source first-pair/by-time distribution

Contributor: dot, 2026-10-02. Computes the first actual original-population
CURRENT pair mark of the genuine source augmentation. Its by-time mass is
(rate/totalRate)*(1-exp(-totalRate*time)), derived from actual choice weights,
absorbing first-mark recursion and Poisson mixing. It is not supplied as a
clock/source-law field. Equality with the winning independent exponential
clock joint law, and reset/path/terminal observations, remain next gates.
-/
namespace UnifiedLean.Source.SourceFirstMarkDistribution
open Nanuq.Source ProbabilityTheory
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceFirstMergerMark
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma current_pair_total_positive (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) : 0 < totalRate N r s := by
  have hp : 0 < choiceRate N r s p := div_pos (pairRate_pos r p.1) (by norm_num)
  have hle : choiceRate N r s p ≤ totalRate N r s :=
    Finset.single_le_sum (fun q _ => (div_pos (pairRate_pos r q.1) (by norm_num)).le) (Finset.mem_univ p)
  exact hp.trans_le hle

lemma stopped_mark_absorbed (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (k : Nat) (p : Choice N s) :
    stoppedMarkIteration N r s k (some p) = PMF.pure (some p) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [stoppedMarkIteration,stoppedMarkStep,PMF.pure_bind,ih]

lemma first_mark_some_recurrence (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (k : Nat) (p : Choice N s) :
    (stoppedMarkIteration N r s (k+1) none (some p)).toReal =
      choiceMass N r s none * (stoppedMarkIteration N r s k none (some p)).toReal +
        choiceMass N r s (some p) := by
  rw [stoppedMarkIteration,stoppedMarkStep,bind_probability_real,tsum_fintype,Fintype.sum_option]
  simp only [choicePMF_real]
  congr 1
  calc
    _ = ∑ q : Choice N s, if q = p then choiceMass N r s (some q) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      rw [stopped_mark_absorbed]
      by_cases hq : q = p
      · simp [PMF.pure_apply,hq]
      · simp [PMF.pure_apply,hq,Ne.symm hq]
    _ = _ := by simp

/-- Exact first actual pair mark at each finite attempt count. -/
theorem actual_first_mark_attempt_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (k : Nat) (p : Choice N s) :
    (stoppedMarkIteration N r s k none (some p)).toReal =
      choiceRate N r s p / totalRate N r s * (1-(choiceMass N r s none)^k) := by
  have htotal := (current_pair_total_positive N r s p).ne'
  have hbound := (globalRateBound_positive (Copy := Copy) r).ne'
  have hchoice : choiceMass N r s (some p) =
      choiceRate N r s p / totalRate N r s * (1-choiceMass N r s none) := by
    simp only [choiceMass]
    field_simp [htotal,hbound]
    ring
  induction k with
  | zero => simp [stoppedMarkIteration,PMF.pure_apply]
  | succ k ih =>
      rw [first_mark_some_recurrence,ih,hchoice,pow_succ']
      ring

lemma actual_hold_poisson_hasSum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) :
    HasSum (fun k : Nat =>
      (Real.exp (-((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ)) *
        (((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ)^k) / k.factorial) *
          (choiceMass N r s none)^k)
      (Real.exp (-(totalRate N r s * (t : ℝ)))) := by
  let a : ℝ := ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ)
  let h : ℝ := choiceMass N r s none
  have hh : HasSum (fun k : Nat => (Real.exp (-a)*a^k/k.factorial)*h^k)
      (Real.exp (-a)*Real.exp (a*h)) := by
    simpa only [mul_pow,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,← Real.exp_eq_exp_ℝ]
      using (NormedSpace.expSeries_div_hasSum_exp (a*h)).mul_left (Real.exp (-a))
  have he : Real.exp (-a)*Real.exp (a*h) = Real.exp (-(totalRate N r s * (t : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    change -(globalRateBound (Copy := Copy) r*(t : ℝ)) +
      (globalRateBound (Copy := Copy) r*(t : ℝ))*(1-totalRate N r s/globalRateBound (Copy := Copy) r) = _
    have hne := (globalRateBound_positive (Copy := Copy) r).ne'
    field_simp [hne]
    ring
  rw [he] at hh
  exact hh

/-- Pair identity AND event-before-time probability are computed from the
ACTUAL continued source process first-mark marginal. Physical exponential
race winning-label/time identification is a further source binding. -/
theorem actual_first_pair_by_time (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (p : Choice N s) :
    (firstMarkTimeKernel N r s t none (some p)).toReal =
      choiceRate N r s p / totalRate N r s * (1-Real.exp (-(totalRate N r s*(t : ℝ)))) := by
  rw [firstMarkTimeKernel,bind_probability_real]
  simp_rw [countPMF_real,actual_first_mark_attempt_mass]
  let a : ℝ≥0 := globalClockRate (Copy := Copy) r * t
  have hc := hasSum_one_poissonMeasure a
  have hh := actual_hold_poisson_hasSum N r s t
  have hs := (hc.sub hh).mul_left (choiceRate N r s p/totalRate N r s)
  have htarget : HasSum (fun k : Nat =>
      (Real.exp (-(a : ℝ))*(a : ℝ)^k/k.factorial) *
      (choiceRate N r s p/totalRate N r s*(1-(choiceMass N r s none)^k)))
      (choiceRate N r s p/totalRate N r s*(1-Real.exp (-(totalRate N r s*(t : ℝ))))) := by
    simpa only [a,mul_sub,mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hs
  exact htarget.tsum_eq

/-- Explicit first-pair law belongs to the actual source augmentation that
forgets exactly to the previously constructed whole original epoch kernel. -/
theorem actual_augmented_first_pair_by_time (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (p : Choice N s) :
    (((firstSourceTimeKernel N r s t none).map (firstMark N s)) (some p)).toReal =
      choiceRate N r s p / totalRate N r s * (1-Real.exp (-(totalRate N r s*(t : ℝ)))) := by
  rw [first_time_kernel_mark]
  exact actual_first_pair_by_time N r s t p

#print axioms current_pair_total_positive
#print axioms actual_first_mark_attempt_mass
#print axioms actual_first_pair_by_time
#print axioms actual_augmented_first_pair_by_time
end UnifiedLean.Source.SourceFirstMarkDistribution
