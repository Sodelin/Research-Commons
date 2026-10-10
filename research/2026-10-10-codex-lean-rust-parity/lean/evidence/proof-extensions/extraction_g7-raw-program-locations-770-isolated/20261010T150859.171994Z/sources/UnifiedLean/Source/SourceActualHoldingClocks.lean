import UnifiedLean.Source.SourceEpochSemigroup
import UnifiedLean.Source.SourceInitializedCalendar

/-!
# ACTUAL current-source first holding clocks and Poisson kernel

Contributor: dot, 2026-10-02. Every original-population CURRENT legal pair has
an actual independent exponential clock (two ordered orientations at half-rate).
The source PMF can return to its original finite state only through holding:
every genuine source merger strictly decreases live cardinality. Its Poisson
no-real-merger probability is derived and matches the independent clock product
tail. This is the arbitrary-copy/source-state FIRST-event binding; winner/time
path/reset equivalence and final unranked/timed observation remain later gates.
-/
namespace UnifiedLean.Source.SourceActualHoldingClocks
open Nanuq.Source GProgram.SourceForest ProbabilityTheory MeasureTheory Set
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def liveCard {N : RootedBinary V E X} {sample : Copy → X} (s : Code N sample) : Nat :=
  s.val.live.card

lemma merger_destination_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    liveCard (stepDestination N s (some p)) + 1 = liveCard s :=
  merge_live_card (state s)
    (GProgram.SourceForestKingmanPopulationProjection.population_pair_is_source_legal
      (state s) (originalPlace N p.1) (originalPlace_not_node N p.1) p.2.property)

lemma step_support_card_le (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceStep N r s).support) : liveCard d ≤ liveCard s := by
  obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  rw [← hp]
  cases p with
  | none => exact le_refl _
  | some p => have h := merger_destination_card N s p; omega

lemma iteration_support_card_le (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceIteration N r k s).support) : liveCard d ≤ liveCard s := by
  induction k generalizing s with
  | zero =>
      have h : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      rw [h]
  | succ k ih =>
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact (ih m hdm).trans (step_support_card_le N r s hm)

lemma iteration_larger_card_zero (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s d : Code N sample) (h : liveCard s < liveCard d) :
    sourceIteration N r k s d = 0 := by
  by_contra hd
  have hle := iteration_support_card_le N r k s ((PMF.mem_support_iff _ _).mpr hd)
  omega

/-- No real source merger can be hidden in a return to the same encoded state.
Its kth-step return mass is precisely k genuine holding outcomes. -/
theorem actual_iteration_no_merger (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s : Code N sample) :
    sourceIteration N r k s s = (choicePMF N r s none)^k := by
  induction k with
  | zero => simp only [sourceIteration,PMF.pure_apply_self,pow_zero]
  | succ k ih =>
      rw [sourceIteration,sourceStep,PMF.bind_map,PMF.bind_apply,tsum_fintype,Fintype.sum_option]
      have hzero : (∑ p : Choice N s, choicePMF N r s (some p) *
          sourceIteration N r k (stepDestination N s (some p)) s) = 0 := by
        apply Finset.sum_eq_zero
        intro p _
        have hc := merger_destination_card N s p
        rw [iteration_larger_card_zero N r k (stepDestination N s (some p)) s (by omega)]
        simp
      simp only [Function.comp_apply] at *
      rw [hzero,add_zero]
      change choicePMF N r s none * sourceIteration N r k s s = _
      rw [ih,pow_succ']

lemma poisson_hold_series (a q : ℝ) :
    (∑' k : Nat, (Real.exp (-a) * a^k / k.factorial) * q^k) = Real.exp (a*(q-1)) := by
  have hh : HasSum (fun k : Nat => (Real.exp (-a) * a^k / k.factorial) * q^k)
      (Real.exp (-a) * Real.exp (a*q)) := by
    simpa only [mul_pow,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,← Real.exp_eq_exp_ℝ]
      using (NormedSpace.expSeries_div_hasSum_exp (a*q)).mul_left (Real.exp (-a))
  rw [hh.tsum_eq,← Real.exp_add]
  congr 1
  ring

/-- Exact no-real-merger probability of the constructed ACTUAL source epoch
PMF, with CURRENT total legal pair rate, not a fitted exponential premise. -/
theorem actual_source_kernel_no_merger (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s s).toReal = Real.exp (-(totalRate N r s * (t : ℝ))) := by
  rw [sourceTimeKernel,bind_probability_real]
  simp_rw [countPMF_real,actual_iteration_no_merger,ENNReal.toReal_pow,choicePMF_real]
  rw [poisson_hold_series]
  congr 1
  change (globalRateBound (Copy := Copy) r * (t : ℝ)) *
    ((1-totalRate N r s/globalRateBound (Copy := Copy) r)-1) = -(totalRate N r s * (t : ℝ))
  have hne := (globalRateBound_positive (Copy := Copy) r).ne'
  field_simp [hne]
  ring

noncomputable def currentPairClockMeasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Measure (Choice N s → ℝ) :=
  Measure.pi (fun p => expMeasure (choiceRate N r s p))

/-- All clocks are indexed by genuine CURRENT original-population pair choices;
when there are no pairs the empty product gives survival probability one. -/
def currentNoFirstMerger (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : ℝ≥0) : Set (Choice N s → ℝ) :=
  Set.univ.pi (fun _ => Set.Ioi (t : ℝ))

theorem actual_current_clock_no_merger (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (currentPairClockMeasure N r s (currentNoFirstMerger N s t)).toReal =
      Real.exp (-(totalRate N r s * (t : ℝ))) := by
  have hp : ∀ p : Choice N s, 0 < choiceRate N r s p :=
    fun p => div_pos (pairRate_pos r p.1) (by norm_num)
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (hp p)
  rw [currentPairClockMeasure,currentNoFirstMerger,Measure.pi_pi,ENNReal.toReal_prod]
  change (∏ p : Choice N s, (expMeasure (choiceRate N r s p)).real (Set.Ioi (t : ℝ))) = _
  have htail : (∏ p : Choice N s, (expMeasure (choiceRate N r s p)).real (Set.Ioi (t : ℝ))) =
      ∏ p : Choice N s, Real.exp (-(choiceRate N r s p * (t : ℝ))) := by
    apply Finset.prod_congr rfl
    intro p _
    exact positive_exp_clock_tail (hp p) t.property
  rw [htail,← Real.exp_sum,Finset.sum_neg_distrib,← Finset.sum_mul]
  rfl

/-- Independent ORIGINAL current-root pair clocks are bound to the actual
Poisson-source kernel at its first event. No desired clock survival equality
is assumed as a source field. -/
theorem actual_first_clock_source_binding (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (currentPairClockMeasure N r s (currentNoFirstMerger N s t)).toReal =
      (sourceTimeKernel N r t s s).toReal := by
  rw [actual_current_clock_no_merger,actual_source_kernel_no_merger]

#print axioms actual_iteration_no_merger
#print axioms actual_source_kernel_no_merger
#print axioms actual_current_clock_no_merger
#print axioms actual_first_clock_source_binding
end UnifiedLean.Source.SourceActualHoldingClocks
