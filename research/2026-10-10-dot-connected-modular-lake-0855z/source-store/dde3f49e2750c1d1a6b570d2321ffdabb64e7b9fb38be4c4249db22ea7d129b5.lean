import UnifiedLean.Source.NativeFairSelectorAssembly
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Original two-tip calendar genealogy readout

Contributor: dot (OpenAI), 2026-10-02. The first coalescence age is constructed
from the literal original edge holding clocks and the ancestral fallback.
Only clocks ringing while their shared original population is active enter the
minimum. This is the root age of the ordinary rooted two-tip calendar genealogy;
latent routes, original population IDs and coins are discarded by this readout.
Tail identities are proved from that decoder, not passed as observation fields.
The later attained-deletion and displayed-quartet assembly remain separate.
-/
namespace UnifiedLean.Source.NativePairCalendarObservation
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.SourceNaturalInitialization
open MeasureTheory ProbabilityTheory Set
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- An actual original shared-edge clock rings only before that population's
exit age. Missed and nonshared edges contribute the ancestral fallback. -/
noncomputable def candidateAge (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (clock : Option E → ℝ) : Option E → ℝ
  | none => C.age N.root + clock none
  | some e => if e ∈ R.edges x ∧ e ∈ R.edges y ∧
      clock (some e) ≤ C.age (N.graph.source e)-C.age (N.graph.target e)
    then C.age (N.graph.target e)+clock (some e)
    else C.age N.root+clock none

noncomputable def firstCoalescenceAge (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (clock : Option E → ℝ) : ℝ :=
  (Finset.univ.toList.map (candidateAge N C R x y clock)).foldr min
    (C.age N.root+clock none)

lemma lt_foldr_min (xs : List ℝ) (t z : ℝ) :
    t < xs.foldr min z ↔ t < z ∧ ∀ a ∈ xs, t < a := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.foldr_cons,lt_min_iff,ih,List.mem_cons]
      aesop

lemma positive_wait_exposure_iff (start finish wait t : ℝ)
    (hw : 0 < wait) (hcap : wait ≤ finish-start) :
    max 0 (min t finish-start) < wait ↔ t < start+wait := by
  rw [max_lt_iff]
  constructor
  · rintro ⟨_,h⟩
    by_contra hn
    have htw : start+wait ≤ t := le_of_not_gt hn
    have hm : start+wait ≤ min t finish := le_min htw (by linarith)
    linarith
  · intro h
    exact ⟨hw,by have hm := min_le_left t finish; linarith⟩

/-- Decoder tail matches ALL literal local-clock survival tests on their
probability-one positive support, including missed edges and the root clock. -/
theorem first_age_tail_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (clock : Option E → ℝ)
    (hc : ∀ e, 0 < clock e) (t : ℝ) :
    t < firstCoalescenceAge N C R x y clock ↔
      clock ∈ noFirstMerger N C R x y t := by
  rw [firstCoalescenceAge,lt_foldr_min,noFirstMerger_iff]
  have ha : t < C.age N.root+clock none ↔ max 0 (t-C.age N.root) < clock none := by
    rw [max_lt_iff]
    constructor
    · intro h; exact ⟨hc none,by linarith⟩
    · rintro ⟨_,h⟩; linarith
  have he : ∀ e, t < C.age N.root+clock none →
      (t < candidateAge N C R x y clock (some e) ↔
        occupiedDuration N C R x y t (some e) < clock (some e)) := by
    intro e hr
    by_cases hs : e ∈ R.edges x ∧ e ∈ R.edges y
    · by_cases hcap : clock (some e) ≤ C.age (N.graph.source e)-C.age (N.graph.target e)
      · simp only [candidateAge,hs.1,hs.2,hcap,true_and,if_true,occupiedDuration,hs,if_true,exposure]
        exact (positive_wait_exposure_iff _ _ _ _ (hc (some e)) hcap).symm
      · have hl : C.age (N.graph.source e)-C.age (N.graph.target e) < clock (some e) :=
          lt_of_not_ge hcap
        have hx : exposure N.graph C t e < clock (some e) := by
          rw [exposure,max_lt_iff]
          exact ⟨hc (some e),by have hm := min_le_right t (C.age (N.graph.source e)); linarith⟩
        simp only [candidateAge,hs.1,hs.2,hcap,true_and,and_false,if_false,occupiedDuration,hs,if_true]
        exact iff_of_true hr hx
    · have hf : ¬(e ∈ R.edges x ∧ e ∈ R.edges y ∧
          clock (some e) ≤ C.age (N.graph.source e)-C.age (N.graph.target e)) :=
        fun h => hs ⟨h.1,h.2.1⟩
      simp only [candidateAge,hf,if_false,occupiedDuration,hs,if_false]
      exact iff_of_true hr (hc (some e))
  constructor
  · rintro ⟨hr,hall⟩ e
    cases e with
    | none => exact ha.mp hr
    | some e =>
        apply (he e hr).mp
        exact hall _ (List.mem_map.mpr ⟨some e,by simp,rfl⟩)
  · intro hall
    have hr := ha.mpr (hall none)
    refine ⟨hr,?_⟩
    intro a ha
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha
    cases e with
    | none => exact hr
    | some e => exact (he e hr).mpr (hall (some e))

lemma candidate_age_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (e : Option E) :
    Measurable (fun clock : Option E → ℝ => candidateAge N C R x y clock e) := by
  cases e with
  | none => exact measurable_const.add (measurable_pi_apply none)
  | some e =>
      by_cases hs : e ∈ R.edges x ∧ e ∈ R.edges y
      · simp only [candidateAge,hs.1,hs.2,true_and]
        exact Measurable.ite (measurableSet_le (measurable_pi_apply _) measurable_const)
          (measurable_const.add (measurable_pi_apply _))
          (measurable_const.add (measurable_pi_apply _))
      · have hf : ∀ clock : Option E → ℝ, ¬(e ∈ R.edges x ∧ e ∈ R.edges y ∧
          clock (some e) ≤ C.age (N.graph.source e)-C.age (N.graph.target e)) :=
          fun _ h => hs ⟨h.1,h.2.1⟩
        simp only [candidateAge,hf,if_false]
        exact measurable_const.add (measurable_pi_apply none)

lemma foldr_min_measurable {I A : Type*} [MeasurableSpace A] (xs : List I)
    (f : I → A → ℝ) (z : A → ℝ) (hf : ∀ i, Measurable (f i)) (hz : Measurable z) :
    Measurable (fun a => (xs.map (fun i => f i a)).foldr min (z a)) := by
  induction xs with
  | nil => exact hz
  | cons i xs ih => exact (hf i).min ih

lemma first_age_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) : Measurable (firstCoalescenceAge N C R x y) :=
  foldr_min_measurable _ _ _ (candidate_age_measurable N C R x y)
    (measurable_const.add (measurable_pi_apply none))

lemma original_clocks_positive_ae (r : PositivePairRates E) :
    ∀ᵐ clock ∂originalClockMeasure r, ∀ e, 0 < clock e := by
  haveI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  have h : ∀ e : Option E, ∀ᵐ u ∂expMeasure (pairRate r e), 0 < u := by
    intro e
    apply (mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
    simpa only [measureReal_def,mul_zero,neg_zero,Real.exp_zero,ENNReal.toReal_one] using positive_exp_clock_tail (pairRate_pos r e) (le_refl (0:ℝ))
  apply ae_all_iff.mpr
  intro e
  exact (Measure.tendsto_eval_ae_ae (μ := fun e : Option E => expMeasure (pairRate r e))).eventually (h e)

/-- The actual ordinary two-tip ROOT AGE law is a measurable pushforward of
the original clocks; its tail equals the previously constructed stopped law. -/
noncomputable def fixedRouteRootAgeLaw (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (R : RouteFamily N) (x y : X) : Measure ℝ :=
  (originalClockMeasure r).map (firstCoalescenceAge N C R x y)

theorem fixed_route_root_age_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (R : RouteFamily N) (x y : X) (t : ℝ) :
    fixedRouteRootAgeLaw N C r R x y (Ioi t) =
      originalClockMeasure r (noFirstMerger N C R x y t) := by
  rw [fixedRouteRootAgeLaw,Measure.map_apply (first_age_measurable N C R x y) measurableSet_Ioi]
  apply measure_congr
  filter_upwards [original_clocks_positive_ae r] with clock hc
  exact propext (first_age_tail_iff N C R x y clock hc t)


/-- The decoded age is later than BOTH original sampling ages on the literal
positive clock support; hence it really gives a valid rooted pair chronology. -/
theorem first_age_after_sampling (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (clock : Option E → ℝ)
    (hc : ∀ e, 0 < clock e) :
    max (C.age (N.leaf x)) (C.age (N.leaf y)) < firstCoalescenceAge N C R x y clock := by
  rw [firstCoalescenceAge,lt_foldr_min]
  have hrx := C.age_le_of_directed (N.rooted (N.leaf x))
  have hry := C.age_le_of_directed (N.rooted (N.leaf y))
  have hr : max (C.age (N.leaf x)) (C.age (N.leaf y)) < C.age N.root+clock none := by
    rw [max_lt_iff]
    constructor <;> linarith [hc none]
  refine ⟨hr,?_⟩
  intro a ha
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha
  cases e with
  | none => exact hr
  | some e =>
      simp only [candidateAge]
      split_ifs with he
      · have hx := C.age_le_of_directed ((R.valid x).target_reaches_end_of_mem he.1)
        have hy := C.age_le_of_directed ((R.valid y).target_reaches_end_of_mem he.2.1)
        rw [max_lt_iff]
        constructor <;> linarith [hc (some e)]
      · exact hr

section FiniteOriginalSeeds
variable {Seed : Type*} [Fintype Seed] [MeasurableSpace Seed] [MeasurableSingletonClass Seed]

noncomputable def decodedSeedAge (N : RootedBinary V E X) (C : Calendar N.graph)
    (routes : Seed → RouteFamily N) (x y : X) (z : Seed × (Option E → ℝ)) : ℝ :=
  firstCoalescenceAge N C (routes z.1) x y z.2

lemma decoded_seed_age_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (routes : Seed → RouteFamily N) (x y : X) : Measurable (decodedSeedAge N C routes x y) :=
  measurable_from_prod_countable_right (fun a => first_age_measurable N C (routes a) x y)

/-- Finite actual source seeds are marginalized, never returned as observation
labels. The readout contains the rooted two-tip coalescence age alone. -/
noncomputable def originalPairRootAgeLaw (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (μ : Measure Seed) (routes : Seed → RouteFamily N)
    (x y : X) : Measure ℝ :=
  (μ.prod (originalClockMeasure r)).map (decodedSeedAge N C routes x y)

/-- Fubini derives the whole decoder tail from the actual original-seed measure
and original clocks; no observation equality is an assumption. -/
theorem original_seed_root_age_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (μ : Measure Seed) [SFinite μ]
    (routes : Seed → RouteFamily N) (x y : X) (t : ℝ) :
    originalPairRootAgeLaw N C r μ routes x y (Ioi t) =
      ∑ a : Seed, μ {a} * originalClockMeasure r (noFirstMerger N C (routes a) x y t) := by
  haveI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  haveI : IsProbabilityMeasure (originalClockMeasure r) := by
    unfold originalClockMeasure
    infer_instance
  rw [originalPairRootAgeLaw,Measure.map_apply (decoded_seed_age_measurable N C routes x y)
    measurableSet_Ioi,Measure.prod_apply ((decoded_seed_age_measurable N C routes x y) measurableSet_Ioi),
    lintegral_fintype]
  apply Finset.sum_congr rfl
  intro a _
  have hf := fixed_route_root_age_tail N C r (routes a) x y t
  rw [fixedRouteRootAgeLaw,Measure.map_apply (first_age_measurable N C (routes a) x y)
    measurableSet_Ioi] at hf
  change originalClockMeasure r ((firstCoalescenceAge N C (routes a) x y) ⁻¹' Ioi t) * μ {a} = _
  rw [hf,mul_comm]
end FiniteOriginalSeeds

noncomputable def independentPairCalendarLaw (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (x y : X) : Measure ℝ :=
  originalPairRootAgeLaw N C r (originalCoinPMF N p).toMeasure (seededRoutes N C H) x y

noncomputable def commonPairCalendarLaw (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (x y : X) : Measure ℝ :=
  originalPairRootAgeLaw N C r (originalRegisterMeasure N p) (commonRoutes N C H) x y

/-- Actual I root-age readout implies the original no-first-merger observer;
different original sampled tips remain untouched current owners until merging. -/
theorem independent_pair_calendar_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (x y : X) (t : ℝ) :
    independentPairCalendarLaw N C H p r x y (Ioi t) =
      nativePairMeasure N p r (survivingReadoutEvent N C H x y t (fun _ => True)) := by
  rw [independentPairCalendarLaw,original_seed_root_age_tail,native_surviving_readout_mass]
  apply Finset.sum_congr rfl
  intro a _
  simp only [if_true,PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)]

/-- Actual COMMON rooted-calendar readout retains exactly the source's one
original-site register prior, with every latent register integrated out. -/
theorem common_pair_calendar_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (x y : X) (t : ℝ) :
    commonPairCalendarLaw N C H p r x y (Ioi t) =
      commonPairMeasure N p r (commonSurvivingEvent N C H x y t) := by
  rw [commonPairCalendarLaw,original_seed_root_age_tail,actual_common_survival_mass]
  apply Finset.sum_congr rfl
  intro a _
  simp only [commonSeedPMF,Measure.toPMF_apply]


/-- The source coin/clock product is a probability law and the explicit root-age
readout preserves its normalization. No observer normalization is supplied. -/
lemma original_pair_age_probability (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) {Seed : Type*} [Fintype Seed] [MeasurableSpace Seed]
    [MeasurableSingletonClass Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (routes : Seed → RouteFamily N) (x y : X) :
    IsProbabilityMeasure (originalPairRootAgeLaw N C r μ routes x y) := by
  haveI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  haveI : IsProbabilityMeasure (originalClockMeasure r) := by
    unfold originalClockMeasure
    infer_instance
  exact Measure.isProbabilityMeasure_map (decoded_seed_age_measurable N C routes x y).aemeasurable

noncomputable def pairCalendarLaw (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) (x y : X) : Measure ℝ :=
  if common then commonPairCalendarLaw N C H p r x y else independentPairCalendarLaw N C H p r x y

noncomputable def pairCalendarCoefficients (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) (x y : X) (t : ℝ) : ℝ →₀ ℝ :=
  if common then commonGermCoefficients N C H p r x y t
  else UnifiedLean.Source.NativeSafePastGerm.nativeGermCoefficients N C H p r x y t

/-- The ordinary ROOT AGE law itself has the intrinsic source-derived finite
right germ. Neither the hidden rate support nor its event grid is an input. -/
theorem pair_calendar_positive_right_germ (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) (x y : X) (hne : x ≠ y) {t : ℝ} (ht : t < C.age N.root) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ, 0 ≤ u → u < ε →
      (pairCalendarLaw N C H p r common x y (Ioi (t+u))).toReal =
        GProgram.G5.ExponentialGerm.finiteExpSum (pairCalendarCoefficients N C H p r common x y t) u := by
  cases common with
  | false =>
      obtain ⟨ε,hε,hw⟩ := UnifiedLean.Source.NativeSafePastGerm.native_probability_positive_right_window
        N C H p r x y hne ht
      refine ⟨ε,hε,?_⟩
      intro u hu hue
      simpa only [pairCalendarLaw,pairCalendarCoefficients,Bool.false_eq_true,if_false,
        independent_pair_calendar_tail,UnifiedLean.Source.NativeSafePastGerm.nativeSurvival] using hw u hu hue
  | true =>
      obtain ⟨ε,hε,hw⟩ := actual_common_probability_positive_right_window N C H p r x y ht
      refine ⟨ε,hε,?_⟩
      intro u hu hue
      simpa only [pairCalendarLaw,pairCalendarCoefficients,if_true,common_pair_calendar_tail,
        commonSurvival] using hw u hu hue

section DifferentOriginalSources
variable {V₂ E₂ : Type*} [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

/-- Equality of actual observed rooted pair calendar laws identifies every
intrinsic coefficient even for DIFFERENT original graphs/calendars/rates and
DIFFERENT COMMON/I modes. Unknown rates need not have the same support. -/
theorem equal_pair_calendar_laws_identify_coefficients
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph) (H₂ : OriginalParentRegistry N₂)
    (p₂ : HybridProbabilities N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (x y : X) (hne : x ≠ y) {t : ℝ} (ht : t < C.age N.root) (ht₂ : t < C₂.age N₂.root)
    (heq : pairCalendarLaw N C H p r common x y = pairCalendarLaw N₂ C₂ H₂ p₂ r₂ common₂ x y) :
    pairCalendarCoefficients N C H p r common x y t =
      pairCalendarCoefficients N₂ C₂ H₂ p₂ r₂ common₂ x y t := by
  obtain ⟨ε,hε,hw⟩ := pair_calendar_positive_right_germ N C H p r common x y hne ht
  obtain ⟨δ,hδ,hz⟩ := pair_calendar_positive_right_germ N₂ C₂ H₂ p₂ r₂ common₂ x y hne ht₂
  apply GProgram.G5.ExponentialGerm.finite_coefficients_eq_of_right_germ _ _ (lt_min hε hδ)
  intro u hu hue
  rw [← hw u hu (hue.trans_le (min_le_left _ _)),← hz u hu (hue.trans_le (min_le_right _ _)),heq]
end DifferentOriginalSources


/-- All current bridge/ordinary/hybrid cases are linked to the observed
calendar law's actual constant coefficient, with no supplied port law. -/
lemma safe_calendar_constant_count (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ}
    (ht : t < C.age N.root) (hsafe : GProgram.G5.SafePast.SafeAt N C B t)
    (D : UnifiedLean.Source.NativeCurrentPortCompiler.NativeCurrentDescription N C H x t)
    (F : UnifiedLean.Source.NativeCurrentPortCompiler.NativeCurrentDescription N C H y t) :
    pairCalendarCoefficients N C H (UnifiedLean.Source.NativeFairCurrentPosition.fairParameters N)
      r common x y t 0 = 1-
      (GProgram.G5.QuartetKernel.pairCount
        (GProgram.G5.OriginalCoinLaw.binaryPositions
          (UnifiedLean.Source.NativeCurrentPortCompiler.descriptionPositions N C hcut H D))
        (GProgram.G5.OriginalCoinLaw.binaryPositions
          (UnifiedLean.Source.NativeCurrentPortCompiler.descriptionPositions N C hcut H F)) : ℝ)/4 := by
  cases common with
  | false =>
      exact UnifiedLean.Source.NativeFairSelectorAssembly.all_case_safe_native_zero_coefficient
        N C hcut H r B hx hy hne ht hsafe D F
  | true =>
      exact UnifiedLean.Source.NativeFairSelectorAssembly.all_case_safe_common_zero_coefficient
        N C hcut H r B hx hy hne ht hsafe D F

section SafeDifferentSources
open UnifiedLean.Source.NativeCurrentPortCompiler UnifiedLean.Source.NativeFairCurrentPosition
open GProgram.G5.SafePast GProgram.G5.QuartetKernel GProgram.G5.OriginalCoinLaw
variable {V₂ E₂ : Type*} [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

/-- Genuine safe-stage observable-moment bridge between arbitrary different
fair original sources and inheritance modes. Actual descriptions are
constructed, not supplied. Chronology/deletion and Q remain later ports. -/
theorem equal_fair_pair_calendar_laws_identify_safe_counts
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ}
    (hlx : C.age (N.leaf x) ≤ t) (hly : C.age (N.leaf y) ≤ t) (ht : t < C.age N.root)
    (hlx₂ : C₂.age (N₂.leaf x) ≤ t) (hly₂ : C₂.age (N₂.leaf y) ≤ t) (ht₂ : t < C₂.age N₂.root)
    (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (heq : pairCalendarLaw N C H (fairParameters N) r common x y =
      pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    ∃ (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t)
      (D₂ : NativeCurrentDescription N₂ C₂ H₂ x t) (F₂ : NativeCurrentDescription N₂ C₂ H₂ y t),
      pairCount (binaryPositions (descriptionPositions N C hcut H D))
        (binaryPositions (descriptionPositions N C hcut H F)) =
      pairCount (binaryPositions (descriptionPositions N₂ C₂ hcut₂ H₂ D₂))
        (binaryPositions (descriptionPositions N₂ C₂ hcut₂ H₂ F₂)) := by
  obtain ⟨D⟩ := original_current_description_exists N C H x hlx ht
  obtain ⟨F⟩ := original_current_description_exists N C H y hly ht
  obtain ⟨D₂⟩ := original_current_description_exists N₂ C₂ H₂ x hlx₂ ht₂
  obtain ⟨F₂⟩ := original_current_description_exists N₂ C₂ H₂ y hly₂ ht₂
  refine ⟨D,F,D₂,F₂,?_⟩
  have he := congrArg (fun c : ℝ →₀ ℝ => c 0)
    (equal_pair_calendar_laws_identify_coefficients N C H (fairParameters N) r common
      N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y hne ht ht₂ heq)
  rw [safe_calendar_constant_count N C hcut H r common B hx hy hne ht hsafe D F,
    safe_calendar_constant_count N₂ C₂ hcut₂ H₂ r₂ common₂ B hx hy hne ht₂ hsafe₂ D₂ F₂] at he
  have hc : (pairCount (binaryPositions (descriptionPositions N C hcut H D))
        (binaryPositions (descriptionPositions N C hcut H F)) : ℝ) =
      (pairCount (binaryPositions (descriptionPositions N₂ C₂ hcut₂ H₂ D₂))
        (binaryPositions (descriptionPositions N₂ C₂ hcut₂ H₂ F₂)) : ℝ) := by linarith
  exact_mod_cast hc
end SafeDifferentSources

#print axioms first_age_tail_iff
#print axioms first_age_measurable
#print axioms original_clocks_positive_ae
#print axioms fixed_route_root_age_tail
#print axioms first_age_after_sampling
#print axioms original_seed_root_age_tail
#print axioms independent_pair_calendar_tail
#print axioms common_pair_calendar_tail
#print axioms original_pair_age_probability
#print axioms pair_calendar_positive_right_germ
#print axioms equal_pair_calendar_laws_identify_coefficients
#print axioms safe_calendar_constant_count
#print axioms equal_fair_pair_calendar_laws_identify_safe_counts
end UnifiedLean.Source.NativePairCalendarObservation
