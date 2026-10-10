import UnifiedLean.Source.NativeFairCurrentPosition
import UnifiedLean.Source.SourceEpochSemigroup
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Actual COMMON original-register stopped-pair germ

Contributor: dot / GPT-6.1 Sol, 2026-10-02. Constructs the stopped pair law
from the SAME once-drawn original hybrid register measure and original edge/
ancestral exponential clocks. The COMMON seed is not indexed by copies. Its
finite right germ and safe zero coefficient are derived directly, without an
assumed mode coupling, a calibrated rate grid or a posterior routing refit.
Binding this stopped readout to ordinary observed pair laws and the attained
representative-deletion/quartet assembly remain separate original G5 ports.
-/
namespace UnifiedLean.Source.NativeCommonPairGerm
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard GProgram.G5.SafePast
open GProgram.G5.ExponentialGerm
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeFairCurrentPosition
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

abbrev CommonSeed (N : RootedBinary V E X) := Hybrid N → Bool

/-- Both original tip routes reuse the same original site's register bit. -/
noncomputable def commonRoutes (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : CommonSeed N) : RouteFamily N :=
  compiledRouteFamily N C H (fun _ h => a h)

noncomputable def commonSeedPMF (N : RootedBinary V E X) (p : HybridProbabilities N) :
    PMF (CommonSeed N) := (originalRegisterMeasure N p).toPMF

noncomputable def commonSeedWeight (N : RootedBinary V E X) (p : HybridProbabilities N)
    (a : CommonSeed N) : ℝ := (commonSeedPMF N p a).toReal

noncomputable def commonPairMeasure (N : RootedBinary V E X) (p : HybridProbabilities N)
    (r : PositivePairRates E) : Measure (CommonSeed N × (Option E → ℝ)) :=
  (originalRegisterMeasure N p).prod (originalClockMeasure r)

/-- Only the first merger is observed; all original shared registers remain
latent, and no post-merger inherited owner receives a new COMMON coin. -/
def commonSurvivingEvent (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x y : X) (t : ℝ) :
    Set (CommonSeed N × (Option E → ℝ)) :=
  ⋃ a : CommonSeed N, {a} ×ˢ noFirstMerger N C (commonRoutes N C H a) x y t

lemma common_surviving_event_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x y : X) (t : ℝ) :
    MeasurableSet (commonSurvivingEvent N C H x y t) := by
  exact MeasurableSet.iUnion (fun a => (measurableSet_singleton a).prod
    (noFirstMerger_measurable N C _ x y t))

lemma common_surviving_event_section (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x y : X) (t : ℝ) (a : CommonSeed N) :
    Prod.mk a ⁻¹' commonSurvivingEvent N C H x y t =
      noFirstMerger N C (commonRoutes N C H a) x y t := by
  ext c
  simp only [commonSurvivingEvent,mem_preimage,mem_iUnion,mem_prod,mem_singleton_iff]
  constructor
  · rintro ⟨b,hab,hb⟩
    subst b
    exact hb
  · exact fun hc => ⟨a,rfl,hc⟩

/-- Actual COMMON original-register/clock product disintegration. No desired
finite mixture or current-position law is a field. -/
theorem actual_common_survival_mass (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (x y : X) (t : ℝ) :
    commonPairMeasure N p r (commonSurvivingEvent N C H x y t) =
      ∑ a : CommonSeed N, (commonSeedPMF N p a) *
        originalClockMeasure r (noFirstMerger N C (commonRoutes N C H a) x y t) := by
  haveI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  haveI : IsProbabilityMeasure (originalClockMeasure r) := by
    unfold originalClockMeasure
    infer_instance
  rw [commonPairMeasure,Measure.prod_apply (common_surviving_event_measurable N C H x y t),
    lintegral_fintype]
  apply Finset.sum_congr rfl
  intro a _
  rw [common_surviving_event_section]
  simp only [commonSeedPMF,Measure.toPMF_apply,mul_comm]

noncomputable def commonSurvival (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (x y : X) (t : ℝ) : ℝ :=
  (commonPairMeasure N p r (commonSurvivingEvent N C H x y t)).toReal

/-- Below the original root the actual COMMON measure equals the intrinsic
finite route survival mixture. The ancestral clock is retained by the source
measure, with correctly zero exposure in this window. -/
theorem below_root_common_pair_probability (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (x y : X) {t : ℝ} (ht : t ≤ C.age N.root) :
    commonSurvival N C H p r x y t =
      ∑ a : CommonSeed N, commonSeedWeight N p a *
        routeSurvival N C r.edge (commonRoutes N C H a) x y t := by
  haveI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  haveI : IsProbabilityMeasure (originalClockMeasure r) := by
    unfold originalClockMeasure
    infer_instance
  rw [commonSurvival,actual_common_survival_mass,ENNReal.toReal_sum (by
    intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_mul,below_root_original_clock_law N C r _ x y ht]
  rfl

/-- Repeated unknown original rate values are merged intrinsically. -/
noncomputable def commonGermCoefficients (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (x y : X) (t : ℝ) : ℝ →₀ ℝ :=
  ∑ a : CommonSeed N, Finsupp.single
    (-currentPairRate N C r.edge (commonRoutes N C H a) x y t)
    (commonSeedWeight N p a * routeSurvival N C r.edge (commonRoutes N C H a) x y t)

lemma common_germ_evaluation (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (x y : X) (t u : ℝ) :
    finiteExpSum (commonGermCoefficients N C H p r x y t) u =
      ∑ a : CommonSeed N, (commonSeedWeight N p a *
        routeSurvival N C r.edge (commonRoutes N C H a) x y t) *
        Real.exp ((-currentPairRate N C r.edge (commonRoutes N C H a) x y t)*u) := by
  unfold commonGermCoefficients finiteExpSum
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  apply Finset.sum_congr rfl
  intro a _
  exact Finsupp.sum_single_index (zero_mul _)

/-- Actual COMMON stopped-pair probability has the constructed finite right
germ on an original event-free window, without supplying the germ as a law. -/
theorem actual_common_probability_right_germ (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (x y : X) {t ε u : ℝ} (hgap : EndpointGap N.graph C t ε)
    (hu : 0 ≤ u) (huε : u < ε) (hroot : t+u ≤ C.age N.root) :
    commonSurvival N C H p r x y (t+u) = finiteExpSum (commonGermCoefficients N C H p r x y t) u := by
  rw [below_root_common_pair_probability N C H p r x y hroot,common_germ_evaluation]
  apply Finset.sum_congr rfl
  intro a _
  rw [routeSurvival_add_on_endpoint_gap N C r.edge _ x y hgap hu huε]
  ring

/-- Finiteness of the SAME original calendar gives a positive event-free
window; no calibrated common clock list is an observer premise. -/
theorem actual_common_probability_positive_right_window (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (x y : X) {t : ℝ} (ht : t < C.age N.root) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ, 0 ≤ u → u < ε →
      commonSurvival N C H p r x y (t+u) = finiteExpSum (commonGermCoefficients N C H p r x y t) u := by
  obtain ⟨δ,hδ,hgap⟩ := positive_endpoint_gap_exists N C t
  refine ⟨min δ (C.age N.root-t),lt_min hδ (sub_pos.mpr ht),?_⟩
  intro u hu huε
  apply actual_common_probability_right_germ N C H p r x y hgap hu
  · exact huε.trans_le (min_le_left _ _)
  · have hh := huε.trans_le (min_le_right δ (C.age N.root-t))
    linarith

noncomputable def commonSeparationMass (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (x y : X) (t : ℝ) : ℝ :=
  ∑ a : CommonSeed N, if ¬CoOccupy N (commonRoutes N C H a) C t x y
    then commonSeedWeight N p a else 0

/-- Safe-past permanence removes survival weighting on EVERY zero-current
rate branch of the actual COMMON measure, not merely its support. -/
theorem safe_actual_common_zero_coefficient (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    {t : ℝ} (ht : t < C.age N.root) (hsafe : SafeAt N C B t) :
    commonGermCoefficients N C H p r x y t 0 = commonSeparationMass N C H p x y t := by
  unfold commonGermCoefficients commonSeparationMass
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : ¬CoOccupy N (commonRoutes N C H a) C t x y
  · have hz := (currentPairRate_zero_iff_separated N C r.edge r.edge_pos _ x y t).mpr hs
    have hv := separated_safe_routeSurvival_one N C r.edge B (commonRoutes N C H a)
      ht hsafe hx hy hne hs
    simp [hz,hv,hs]
  · have hz : currentPairRate N C r.edge (commonRoutes N C H a) x y t ≠ 0 := by
      intro h
      exact hs ((currentPairRate_zero_iff_separated N C r.edge r.edge_pos _ x y t).mp h)
    simp [hz,hs]

/-- Exact COMMON probability germs identify the intrinsic coefficients without
requiring the observer to know original rates, a shared rate list or derivatives. -/
theorem actual_common_coefficients_eq_of_probability_germ (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (x y : X) {t ε : ℝ} (hε : 0 < ε)
    (hgap : EndpointGap N.graph C t ε) (hroot : t+ε ≤ C.age N.root)
    (d : ℝ →₀ ℝ) (heq : ∀ u : ℝ, 0 ≤ u → u < ε →
      commonSurvival N C H p r x y (t+u) = finiteExpSum d u) :
    commonGermCoefficients N C H p r x y t = d := by
  apply finite_coefficients_eq_of_right_germ _ _ hε
  intro u hu huε
  rw [← actual_common_probability_right_germ N C H p r x y hgap hu huε (by linarith)]
  exact heq u hu huε

lemma common_cooccupy_port_readout (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x y : X} {t : ℝ}
    (P : CurrentHybridPort N C H x t) (Q : CurrentHybridPort N C H y t)
    (a : CommonSeed N) :
    CoOccupy N (commonRoutes N C H a) C t x y ↔
      currentParentPosition P (a P.site) = currentParentPosition Q (a Q.site) :=
  native_coOccupy_iff_current_parents N C hcut H (fun _ h => a h) x y P.site Q.site
    P.exit_bridge Q.exit_bridge P.port Q.port P.below Q.below
    P.component Q.component P.lower P.upper Q.lower Q.upper

lemma commonSeedWeight_fair (N : RootedBinary V E X) (a : CommonSeed N) :
    commonSeedWeight N (fairParameters N) a =
      (GProgram.SourceForest.independentWeight (1/2) a : ℝ) := by
  unfold commonSeedWeight commonSeedPMF
  rw [original_common_fair_seed_PMF]
  simp only [GProgram.G5.OriginalCoinLaw.independentPMF,PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (GProgram.G5.OriginalCoinLaw.independentWeight_real_nonnegative
      (by norm_num : (0 : ℚ) ≤ 1/2) (by norm_num : (1/2 : ℚ) ≤ 1) a)

/-- The actual COMMON stopped-pair zero coefficient is the SAME fair selector
count complement on the safe stage. Original current-site distinctness is
DERIVED from SafeAt, and past survival weighting is removed by permanence. -/
theorem safe_common_zero_coefficient_eq_fair_selector_count (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ}
    (hsafe : SafeAt N C B t)
    (P : CurrentHybridPort N C H x t) (Q : CurrentHybridPort N C H y t) :
    commonGermCoefficients N C H (fairParameters N) r x y t 0 =
      1-(GProgram.G5.QuartetKernel.pairCount
        (GProgram.G5.OriginalCoinLaw.binaryPositions (currentParentPosition P))
        (GProgram.G5.OriginalCoinLaw.binaryPositions (currentParentPosition Q)) : ℝ)/4 := by
  have ht : t < C.age N.root := P.upper.trans_le (C.age_le_of_directed (N.rooted P.entry))
  rw [safe_actual_common_zero_coefficient N C H (fairParameters N) r B hx hy hne ht hsafe]
  have hs := safe_current_hybrid_sites_distinct N C H B hx hy hne hsafe P Q
  have hq := GProgram.G5.OriginalCoinLaw.fair_source_meeting_weight hs
    (currentParentPosition P) (currentParentPosition Q)
  have hreal : (∑ a : CommonSeed N, commonSeedWeight N (fairParameters N) a *
      (if currentParentPosition P (a P.site) = currentParentPosition Q (a Q.site) then 1 else 0)) =
      (GProgram.G5.QuartetKernel.pairCount
        (GProgram.G5.OriginalCoinLaw.binaryPositions (currentParentPosition P))
        (GProgram.G5.OriginalCoinLaw.binaryPositions (currentParentPosition Q)) : ℝ)/4 := by
    simp_rw [commonSeedWeight_fair]
    have hh := congrArg (fun z : ℚ => (z : ℝ)) hq
    push_cast at hh
    simpa only [apply_ite,Rat.cast_one,Rat.cast_zero] using hh
  have hsum : commonSeparationMass N C H (fairParameters N) x y t +
      (∑ a : CommonSeed N, commonSeedWeight N (fairParameters N) a *
        (if currentParentPosition P (a P.site) = currentParentPosition Q (a Q.site) then 1 else 0)) = 1 := by
    rw [commonSeparationMass,← Finset.sum_add_distrib]
    convert UnifiedLean.Source.SourceEpochSemigroup.pmf_sum_real
      (commonSeedPMF N (fairParameters N)) using 1
    apply Finset.sum_congr rfl
    intro a _
    rw [common_cooccupy_port_readout N C hcut H P Q a]
    split_ifs <;> simp_all [commonSeedWeight]
  rw [hreal] at hsum
  linarith

/-- The zero-rate current information agrees in BOTH original inheritance
modes at safe stages even when their positive rate assignments differ. This
is coefficient equality, not an assumed equality of their entire pair laws. -/
theorem safe_common_independent_zero_coefficients (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (rCommon rIndependent : PositivePairRates E)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ}
    (hsafe : SafeAt N C B t)
    (P : CurrentHybridPort N C H x t) (Q : CurrentHybridPort N C H y t) :
    commonGermCoefficients N C H (fairParameters N) rCommon x y t 0 =
      UnifiedLean.Source.NativeSafePastGerm.nativeGermCoefficients N C H
        (fairParameters N) rIndependent x y t 0 := by
  rw [safe_common_zero_coefficient_eq_fair_selector_count N C hcut H rCommon B hx hy hne hsafe P Q,
    safe_native_zero_coefficient_eq_fair_selector_count N C hcut H rIndependent B hx hy hne hsafe P Q]

#print axioms actual_common_coefficients_eq_of_probability_germ
#print axioms safe_common_zero_coefficient_eq_fair_selector_count
#print axioms safe_common_independent_zero_coefficients
#print axioms actual_common_survival_mass
#print axioms below_root_common_pair_probability
#print axioms actual_common_probability_right_germ
#print axioms actual_common_probability_positive_right_window
#print axioms safe_actual_common_zero_coefficient
end UnifiedLean.Source.NativeCommonPairGerm
