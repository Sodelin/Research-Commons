import G5ObservableSafePairSupport

/-!
# Actual ancestral pair-law right germ
Contributor: dot / OpenAI, 2026-10-03.
Above the original root, literal original edge exposures are complete and the
positive original ancestral clock gives one genuine exponential. This extends
the intrinsic observed coefficients to the root and all older ages; no root
age or rate grid is an observer premise.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativePairCalendarObservation UnifiedLean.Source.NativeFairCurrentPosition
open UnifiedLean.Source.SourceNaturalInitialization
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma original_route_survival_above_root (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : E → ℝ) (R : RouteFamily N) (x y : X) {t : ℝ} (ht : C.age N.root ≤ t) :
    routeSurvival N C r R x y t = routeSurvival N C r R x y (C.age N.root) := by
  unfold routeSurvival
  congr 2
  unfold accumulatedHazard
  apply Finset.sum_congr rfl
  intro e _
  have ha := C.age_le_of_directed (N.rooted (N.graph.source e))
  simp only [exposure,min_eq_right ha,min_eq_right (ha.trans ht)]

lemma original_clock_ancestral_tail_factor (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (R : RouteFamily N) (x y : X) {t u : ℝ}
    (ht : C.age N.root ≤ t) (hu : 0 ≤ u) :
    (originalClockMeasure r (noFirstMerger N C R x y (t+u))).toReal =
      (originalClockMeasure r (noFirstMerger N C R x y t)).toReal * Real.exp (-r.ancestral*u) := by
  have htu : C.age N.root ≤ t+u := by linarith
  rw [original_clock_survival_eq_routeSurvival,original_clock_survival_eq_routeSurvival,
    original_route_survival_above_root N C r.edge R x y htu,
    original_route_survival_above_root N C r.edge R x y ht,
    max_eq_right (sub_nonneg.mpr htu),max_eq_right (sub_nonneg.mpr ht)]
  have he : -(r.ancestral * (t+u-C.age N.root)) = -(r.ancestral*(t-C.age N.root))+(-r.ancestral*u) := by ring
  rw [he,Real.exp_add]
  ring

section FiniteSeeds
variable {Seed : Type*} [Fintype Seed] [MeasurableSpace Seed] [MeasurableSingletonClass Seed]

lemma original_seed_ancestral_tail_factor (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (routes : Seed → RouteFamily N) (x y : X) {t u : ℝ}
    (ht : C.age N.root ≤ t) (hu : 0 ≤ u) :
    (originalPairRootAgeLaw N C r μ routes x y (Ioi (t+u))).toReal =
      (originalPairRootAgeLaw N C r μ routes x y (Ioi t)).toReal * Real.exp (-r.ancestral*u) := by
  haveI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  haveI : IsProbabilityMeasure (originalClockMeasure r) := by unfold originalClockMeasure; infer_instance
  rw [original_seed_root_age_tail,original_seed_root_age_tail,
    ENNReal.toReal_sum (by intro a _; exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_sum (by intro a _; exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,original_clock_ancestral_tail_factor N C r (routes a) x y ht hu]
  ring
end FiniteSeeds

/-- The genuine ordinary root-age law retains the ORIGINAL positive ancestral
clock for both mechanisms. -/
theorem pair_calendar_ancestral_tail_factor (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) (x y : X) {t u : ℝ} (ht : C.age N.root ≤ t) (hu : 0 ≤ u) :
    (pairCalendarLaw N C H p r common x y (Ioi (t+u))).toReal =
      (pairCalendarLaw N C H p r common x y (Ioi t)).toReal * Real.exp (-r.ancestral*u) := by
  cases common with
  | false =>
      exact original_seed_ancestral_tail_factor N C r (originalCoinPMF N p).toMeasure
        (seededRoutes N C H) x y ht hu
  | true =>
      exact original_seed_ancestral_tail_factor N C r (originalRegisterMeasure N p)
        (commonRoutes N C H) x y ht hu

/-- Full intrinsic observed coefficients, including ancestry. The source clock
selects a REPRESENTATION, whose uniqueness is proved from the observed law. -/
noncomputable def fullPairCalendarCoefficients (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) (x y : X) (t : ℝ) : ℝ →₀ ℝ :=
  if t < C.age N.root then pairCalendarCoefficients N C H p r common x y t
  else Finsupp.single (-r.ancestral) ((pairCalendarLaw N C H p r common x y (Ioi t)).toReal)

theorem full_pair_calendar_positive_right_germ (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) (x y : X) (hne : x ≠ y) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ, 0 ≤ u → u < ε →
      (pairCalendarLaw N C H p r common x y (Ioi (t+u))).toReal =
        GProgram.G5.ExponentialGerm.finiteExpSum (fullPairCalendarCoefficients N C H p r common x y t) u := by
  by_cases ht : t < C.age N.root
  · simpa only [fullPairCalendarCoefficients,if_pos ht] using
      pair_calendar_positive_right_germ N C H p r common x y hne ht
  · refine ⟨1,by norm_num,?_⟩
    intro u hu _
    rw [fullPairCalendarCoefficients,if_neg ht,GProgram.G5.ExponentialGerm.finiteExpSum,
      Finsupp.sum_single_index (zero_mul _)]
    exact pair_calendar_ancestral_tail_factor N C H p r common x y (le_of_not_gt ht) hu

lemma full_pair_ancestral_zero_coefficient (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) (x y : X) {t : ℝ} (ht : C.age N.root ≤ t) :
    fullPairCalendarCoefficients N C H p r common x y t 0 = 0 := by
  have hn : -r.ancestral ≠ 0 := neg_ne_zero.mpr (ne_of_gt r.ancestral_pos)
  rw [fullPairCalendarCoefficients,if_neg (not_lt.mpr ht)]
  exact Finsupp.single_eq_of_ne hn.symm

section DifferentSources
variable {V₂ E₂ : Type*} [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

/-- No below-root cutoff is required: equality of the observed distinct-pair
law identifies the intrinsic germ even at one or both original root ages. -/
theorem equal_pair_calendar_laws_identify_full_coefficients
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph) (H₂ : OriginalParentRegistry N₂)
    (p₂ : HybridProbabilities N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (x y : X) (hne : x ≠ y) (t : ℝ)
    (heq : pairCalendarLaw N C H p r common x y = pairCalendarLaw N₂ C₂ H₂ p₂ r₂ common₂ x y) :
    fullPairCalendarCoefficients N C H p r common x y t =
      fullPairCalendarCoefficients N₂ C₂ H₂ p₂ r₂ common₂ x y t := by
  obtain ⟨ε,hε,hw⟩ := full_pair_calendar_positive_right_germ N C H p r common x y hne t
  obtain ⟨δ,hδ,hz⟩ := full_pair_calendar_positive_right_germ N₂ C₂ H₂ p₂ r₂ common₂ x y hne t
  apply GProgram.G5.ExponentialGerm.finite_coefficients_eq_of_right_germ _ _ (lt_min hε hδ)
  intro u hu hue
  rw [←hw u hu (hue.trans_le (min_le_left _ _)),←hz u hu (hue.trans_le (min_le_right _ _)),heq]
end DifferentSources

#print axioms pair_calendar_ancestral_tail_factor
#print axioms full_pair_calendar_positive_right_germ
#print axioms full_pair_ancestral_zero_coefficient
#print axioms equal_pair_calendar_laws_identify_full_coefficients
end GProgram.G5.AttainedChronology
