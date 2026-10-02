import UnifiedLean.Source.SourceExponentialRace

/-!
# ORIGINAL CURRENT-pair exponential winner/by-time density

Contributor: dot, 2026-10-02. Derives the actual independent exponential race
winning coordinate/time CDF by product-measure/Fubini/PDF calculation, then
instantiates actual source rates and matches the derived first-mark source law.
No race equality is an input field. Ordered half-rate clocks are internal
encoding; complete unordered/unranked reset/path/timed-law assembly remains.
-/
namespace UnifiedLean.Source.SourceExponentialRaceDensity
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open UnifiedLean.Source.SourceExponentialRace
open scoped Classical BigOperators NNReal ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sum_other_plus_pair (rate : I → ℝ) (p : I) :
    rate p + (∑ q : Other p, rate q.val) = ∑ i : I, rate i := by
  letI : Unique {q : I // q = p} :=
    {default := ⟨p,rfl⟩,uniq := by intro q; exact Subtype.ext q.property}
  have hd : (default : {q : I // q = p}).val = p := (default : {q : I // q = p}).property
  simpa only [Fintype.sum_unique,hd] using
    (Fintype.sum_subtype_add_sum_subtype (fun q : I => q = p) rate)

lemma race_total_positive (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I) :
    0 < ∑ i : I, rate i :=
  (hr p).trans_le (Finset.single_le_sum (fun i _ => (hr i).le) (Finset.mem_univ p))

/-- Exact independent competitor tail, conditional on the actual winning
coordinate time x. Empty competitors correctly have probability one. -/
lemma competitor_tail (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I)
    {x : ℝ} (hx : 0 ≤ x) :
    (Measure.pi (fun q : Other p => expMeasure (rate q.val)))
      (Set.univ.pi (fun _ : Other p => Set.Ioi x)) =
        ENNReal.ofReal (Real.exp (-((∑ q : Other p, rate q.val)*x))) := by
  letI : ∀ q : Other p, IsProbabilityMeasure (expMeasure (rate q.val)) :=
    fun q => isProbabilityMeasure_expMeasure (hr q.val)
  have hh : ((Measure.pi (fun q : Other p => expMeasure (rate q.val)))
      (Set.univ.pi (fun _ : Other p => Set.Ioi x))).toReal =
        Real.exp (-((∑ q : Other p, rate q.val)*x)) := by
    rw [Measure.pi_pi,ENNReal.toReal_prod]
    change (∏ q : Other p, (expMeasure (rate q.val)).real (Set.Ioi x)) = _
    have htail : (∏ q : Other p, (expMeasure (rate q.val)).real (Set.Ioi x)) =
        ∏ q : Other p, Real.exp (-(rate q.val*x)) := by
      apply Finset.prod_congr rfl
      intro q _
      exact UnifiedLean.Source.NativePairClockLaw.positive_exp_clock_tail (hr q.val) hx
    rw [htail,← Real.exp_sum,Finset.sum_neg_distrib,← Finset.sum_mul]
  rw [← hh,ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Multiplying the ACTUAL winning clock's PDF by its independent competitor
tails is the rate fraction times the ACTUAL total-rate exponential PDF. -/
lemma actual_race_pdf_factor (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I) (x : ℝ) :
    exponentialPDF (rate p) x *
      (Measure.pi (fun q : Other p => expMeasure (rate q.val)))
        (Set.univ.pi (fun _ : Other p => Set.Ioi x)) =
      ENNReal.ofReal (rate p/(∑ i : I, rate i)) * exponentialPDF (∑ i : I, rate i) x := by
  have htotal := race_total_positive rate hr p
  by_cases hx : 0 ≤ x
  · rw [competitor_tail rate hr p hx,exponentialPDF_of_nonneg hx,exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (mul_nonneg (hr p).le (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (div_nonneg (hr p).le htotal.le)]
    congr 1
    have hs := sum_other_plus_pair rate p
    have hexp : Real.exp (-(rate p*x))*Real.exp (-((∑ q : Other p, rate q.val)*x)) =
        Real.exp (-((∑ i : I, rate i)*x)) := by
      rw [← Real.exp_add]
      congr 1
      rw [← hs]
      ring
    calc
      rate p*Real.exp (-(rate p*x))*Real.exp (-((∑ q : Other p, rate q.val)*x)) =
        rate p*(Real.exp (-(rate p*x))*Real.exp (-((∑ q : Other p, rate q.val)*x))) := by ring
      _ = rate p*Real.exp (-((∑ i : I, rate i)*x)) := by rw [hexp]
      _ = rate p/(∑ i : I, rate i)*((∑ i : I, rate i)*Real.exp (-((∑ i : I, rate i)*x))) := by
        field_simp [htotal.ne']
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),exponentialPDF_of_neg (lt_of_not_ge hx),zero_mul,mul_zero]

/-- Full actual winning-coordinate/by-time probability, not merely survival
or an assumed proportional winner distribution. -/
theorem actual_exponential_race_winner_by_time (rate : I → ℝ) (hr : ∀ i, 0 < rate i)
    (p : I) (t : ℝ≥0) :
    ((Measure.pi (fun i => expMeasure (rate i))) (winnerBefore p (t : ℝ))).toReal =
      rate p/(∑ i : I, rate i)*(1-Real.exp (-((∑ i : I, rate i)*(t : ℝ)))) := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  have htotal := race_total_positive rate hr p
  rw [actual_race_measure_reduction]
  have hh : (∫⁻ x in Set.Iic (t : ℝ),
      (Measure.pi (fun q : Other p => expMeasure (rate q.val)))
        (Set.univ.pi (fun _ : Other p => Set.Ioi x)) ∂expMeasure (rate p)) =
      ENNReal.ofReal (rate p/(∑ i : I, rate i)) *
        ∫⁻ x in Set.Iic (t : ℝ), exponentialPDF (∑ i : I, rate i) x := by
    change (∫⁻ x in Set.Iic (t : ℝ), _ ∂volume.withDensity (exponentialPDF (rate p))) = _
    rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
      (by unfold exponentialPDF; fun_prop) _ measurableSet_Iic
      (Filter.Eventually.of_forall (fun x => by unfold exponentialPDF; exact ENNReal.ofReal_lt_top))]
    simp only [Pi.mul_apply]
    simp_rw [actual_race_pdf_factor rate hr p]
    rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop)]
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.property
  rw [hh,lintegral_exponentialPDF_eq_antiDeriv htotal,if_pos ht]
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_nonneg (hr p).le htotal.le)]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [t.property])))]

open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceFirstMarkDistribution
open UnifiedLean.Source.SourceFirstMergerMark
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Actual ORIGINAL current-pair exponential winner/time law matches the
actual source first-mark/by-time law. Post-event reset/path consistency and
physical unordered/unranked observation still require their next source links. -/
theorem original_current_race_source_mark_binding (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (p : Choice N s) :
    (currentPairClockMeasure N r s (winnerBefore p (t : ℝ))).toReal =
      (firstMarkTimeKernel N r s t none (some p)).toReal := by
  have hp : ∀ q : Choice N s, 0 < choiceRate N r s q :=
    fun q => div_pos (pairRate_pos r q.1) (by norm_num)
  rw [currentPairClockMeasure,actual_exponential_race_winner_by_time _ hp,
    actual_first_pair_by_time]
  rfl

#print axioms actual_race_pdf_factor
#print axioms actual_exponential_race_winner_by_time
#print axioms original_current_race_source_mark_binding
end UnifiedLean.Source.SourceExponentialRaceDensity
