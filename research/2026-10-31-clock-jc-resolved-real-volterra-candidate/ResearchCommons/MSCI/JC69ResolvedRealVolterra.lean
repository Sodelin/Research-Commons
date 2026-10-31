import ResearchCommons.MSCI.JC69RootResolvent
import ResearchCommons.MSCI.JC69EndpointQuotient

/-! Actual endpoint-resolved REAL Volterra identity before signed partial
fractions. UNCOMPILED, dot (OpenAI), 31 October 2026. Finite source masses,
measurability and real integrability are derived, not assumed. No ofReal is
distributed over a signed sum and no endpoint target/failure flag is removed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69ResolvedRealVolterra
open MeasureTheory ProbabilityTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceRaceWinnerSelection
open GProgram.G2.LiteralMarkedClockTrace
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69TraceOccupation
open ResearchCommons.MSCI.JC69WeightedTrace ResearchCommons.MSCI.JC69EndpointWeight
open ResearchCommons.MSCI.JC69EndpointQuotient ResearchCommons.MSCI.JC69ActualDensity
open ResearchCommons.MSCI.JC69RootResolvent
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Joint actual trace/readout measurability, with the SAME target kept. -/
theorem actual_resolved_measurable_time (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (target : BlockPopulationObservation Copy V E) :
    Measurable (fun t => actualResolvedWeight N r L q n s t target) := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r s) := by
    unfold currentPairClockMeasure
    infer_instance
  have htrace := marked_trace_joint_measurable N n s
  have ho : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
      ∑ j, occupationAt N (q j) n s 0 z.1 (literalMarkedTrace N n z.1 s z.2).2) := by
    apply Finset.measurable_sum
    intro j _
    exact (occupation_joint_measurable N (q j) n s).comp
      (measurable_const.prodMk (measurable_fst.prodMk htrace.snd))
  have hl : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
      locusTraceWeight N L q n s z.1 (literalMarkedTrace N n z.1 s z.2)) := by
    unfold locusTraceWeight
    apply Measurable.ite
    · exact measurableSet_eq_fun htrace.fst measurable_const
    · exact (Real.measurable_exp.comp (measurable_const.mul ho).neg).ennreal_ofReal
    · exact measurable_const
  have he : Measurable (fun d : Code N sample =>
      if observeCode N d = target then (1:ℝ≥0∞) else 0) := measurable_of_countable _
  have hx := he.comp ((trace_endpoint_measurable N n s).comp htrace.snd)
  have hw : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
      resolvedTraceWeight N L q n s z.1 target (literalMarkedTrace N n z.1 s z.2)) := hl.mul hx
  have hi := hw.lintegral_prod_right' (ν := currentPairClockMeasure N r s)
  have heq := funext (fun t => actual_resolved_clock_integral N r L q n s t target)
  rw [heq]
  exact hi

lemma actual_resolved_le_locus (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ) (target : BlockPopulationObservation Copy V E) :
    actualResolvedWeight N r L q n s t target ≤ actualLocusWeight N r L q n s t := by
  unfold actualResolvedWeight actualLocusWeight
  apply lintegral_mono
  intro z
  unfold resolvedTraceWeight exitIndicator
  split_ifs <;> simp

theorem actual_resolved_weight_le_one (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ) (ht : 0 ≤ t)
    (target : BlockPopulationObservation Copy V E) : actualResolvedWeight N r L q n s t target ≤ 1 :=
  (actual_resolved_le_locus N r L q n s t target).trans (actual_weight_le_one N r L q n s t ht)

/-- Original endpoint-resolved density integrand, not a new transition law. -/
def branchDensity (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ) (target : BlockPopulationObservation Copy V E)
    (p : Choice N s) (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (choiceRate N r s p * Real.exp (-((totalRate N r s+locusKill N L q s)*u))) *
    actualResolvedWeight N r L q n (stepDestination N s (some p)) (t-u) target

theorem actual_resolved_density_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    actualResolvedWeight N r L q (n+1) s t target =
      ENNReal.ofReal (Real.exp (-((totalRate N r s+locusKill N L q s)*(t:ℝ)))) *
        (if observeCode N s = target then 1 else 0) +
      ∑ p : Choice N s, ∫⁻ u in Icc (0:ℝ) (t:ℝ), branchDensity N r L q n s t target p u := by
  rw [actual_resolved_weight_renewal]
  apply congrArg₂ (· + ·)
  · rw [← mul_assoc,← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
    congr 3
    ring
  · apply Finset.sum_congr rfl
    intro p _
    have hr := actual_choiceRate_positive N r s p
    have hC : 0 < totalRate N r s :=
      hr.trans_le (Finset.single_le_sum
        (fun i _ => (actual_choiceRate_positive N r s i).le) (Finset.mem_univ p))
    rw [winner_density (totalRate N r s) (choiceRate N r s p) (t:ℝ) hC hr.le t.property
      (fun u => ENNReal.ofReal (Real.exp (-(locusKill N L q s*u))) *
        actualResolvedWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u) target)]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u _
    change ENNReal.ofReal (choiceRate N r s p * Real.exp (-(totalRate N r s*u))) *
      (ENNReal.ofReal (Real.exp (-(locusKill N L q s*u))) *
        actualResolvedWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u) target) = _
    unfold branchDensity
    rw [← mul_assoc,← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.exp_nonneg _))]
    congr 2
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring

lemma branch_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ) (target : BlockPopulationObservation Copy V E)
    (p : Choice N s) : Measurable (branchDensity N r L q n s t target p) := by
  have hf := (actual_resolved_measurable_time N r L q n (stepDestination N s (some p)) target).comp
    (measurable_const.sub measurable_id)
  exact (by fun_prop : Measurable (fun u : ℝ => ENNReal.ofReal
    (choiceRate N r s p * Real.exp (-((totalRate N r s+locusKill N L q s)*u))))).mul hf

/-- Finiteness is derived from the genuine nonnegative source renewal and
mass bound, not added as an integrability premise. -/
lemma branch_integral_le_one (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) (target : BlockPopulationObservation Copy V E)
    (p : Choice N s) :
    (∫⁻ u in Icc (0:ℝ) (t:ℝ), branchDensity N r L q n s t target p u) ≤ 1 := by
  have hR := actual_resolved_density_renewal N r L q n s t target
  calc
    _ ≤ ∑ p : Choice N s, ∫⁻ u in Icc (0:ℝ) (t:ℝ), branchDensity N r L q n s t target p u :=
      Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ p)
    _ ≤ actualResolvedWeight N r L q (n+1) s t target := by
      rw [hR]
      exact le_add_of_nonneg_left (zero_le _)
    _ ≤ 1 := actual_resolved_weight_le_one N r L q (n+1) s t t.property target

/-- Real signed-convolution linearity is now legitimate for each actual
branch; it is never justified by treating signed coefficients as masses. -/
theorem actual_resolved_real_branch_integrable (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) (target : BlockPopulationObservation Copy V E)
    (p : Choice N s) :
    IntegrableOn (fun u => choiceRate N r s p *
      Real.exp (-((totalRate N r s+locusKill N L q s)*u)) *
      (actualResolvedWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u) target).toReal)
      (Icc (0:ℝ) (t:ℝ)) := by
  have hfin : (∫⁻ u in Icc (0:ℝ) (t:ℝ), branchDensity N r L q n s t target p u) ≠ ∞ :=
    ne_of_lt ((branch_integral_le_one N r L q n s t target p).trans_lt ENNReal.one_lt_top)
  have hi := integrable_toReal_of_lintegral_ne_top
    (μ := volume.restrict (Icc (0:ℝ) (t:ℝ)))
    (branch_measurable N r L q n s t target p).aemeasurable hfin
  simpa only [branchDensity,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg (actual_choiceRate_positive N r s p).le (Real.exp_nonneg _))] using hi

lemma branch_toReal_integral (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) (target : BlockPopulationObservation Copy V E)
    (p : Choice N s) :
    (∫⁻ u in Icc (0:ℝ) (t:ℝ), branchDensity N r L q n s t target p u).toReal =
      ∫ u in Icc (0:ℝ) (t:ℝ), choiceRate N r s p *
        Real.exp (-((totalRate N r s+locusKill N L q s)*u)) *
        (actualResolvedWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u) target).toReal := by
  have hfinite : ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) (t:ℝ)),
      branchDensity N r L q n s t target p u < ∞ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((actual_resolved_weight_le_one N r L q n (stepDestination N s (some p)) _
        (sub_nonneg.mpr hu.2) target).trans_lt ENNReal.one_lt_top)
  have h := (integral_toReal (branch_measurable N r L q n s t target p).aemeasurable hfinite).symm
  simpa only [branchDensity,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg (actual_choiceRate_positive N r s p).le (Real.exp_nonneg _))] using h

/-- The exact original zero-fuel/no-event base, now in ℝ. -/
theorem actual_resolved_real_zero (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (s : Code N sample) (t : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    (actualResolvedWeight N r L q 0 s t target).toReal =
      Real.exp (-((totalRate N r s+locusKill N L q s)*(t:ℝ))) *
        (if observeCode N s = target then 1 else 0) := by
  rw [actual_resolved_weight_zero]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  by_cases h : observeCode N s = target
  · simp only [h,if_true,ENNReal.toReal_one,mul_one,← Real.exp_add]
    congr 1
    ring
  · simp [h]

/-- Source-derived real Volterra identity with SAME final target and actual
reset continuation. This is the input to a future path expansion, not an
assumed exponential-polynomial representation. -/
theorem actual_resolved_real_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    (actualResolvedWeight N r L q (n+1) s t target).toReal =
      Real.exp (-((totalRate N r s+locusKill N L q s)*(t:ℝ))) *
        (if observeCode N s = target then 1 else 0) +
      ∑ p : Choice N s, ∫ u in Icc (0:ℝ) (t:ℝ), choiceRate N r s p *
        Real.exp (-((totalRate N r s+locusKill N L q s)*u)) *
        (actualResolvedWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u) target).toReal := by
  have hp (p : Choice N s) : (∫⁻ u in Icc (0:ℝ) (t:ℝ),
      branchDensity N r L q n s t target p u) ≠ ∞ :=
    ne_of_lt ((branch_integral_le_one N r L q n s t target p).trans_lt ENNReal.one_lt_top)
  have hbase : ENNReal.ofReal (Real.exp (-((totalRate N r s+locusKill N L q s)*(t:ℝ)))) *
      (if observeCode N s = target then 1 else 0) ≠ ∞ := by
    split_ifs <;> simp
  have hsum : (∑ p : Choice N s, ∫⁻ u in Icc (0:ℝ) (t:ℝ),
      branchDensity N r L q n s t target p u) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun p _ => hp p)
  rw [actual_resolved_density_renewal,ENNReal.toReal_add hbase hsum,
    ENNReal.toReal_sum (fun p _ => hp p)]
  apply congrArg₂ (· + ·)
  · rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    split_ifs <;> simp
  · exact Finset.sum_congr rfl (fun p _ => branch_toReal_integral N r L q n s t target p)

#print axioms actual_resolved_measurable_time
#print axioms actual_resolved_weight_le_one
#print axioms actual_resolved_density_renewal
#print axioms actual_resolved_real_branch_integrable
#print axioms actual_resolved_real_zero
#print axioms actual_resolved_real_renewal
end ResearchCommons.MSCI.JC69ResolvedRealVolterra
