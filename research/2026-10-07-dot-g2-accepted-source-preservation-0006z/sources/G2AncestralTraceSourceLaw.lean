import G2FiniteAncestralTrace
import G2LiteralEpochLaw
import UnifiedLean.Source.SourceEventualCompletionLimit
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Actual random-cover ancestral endpoint and original completion law

Contributor: dot (OpenAI), 2026-10-06. New reconstruction. The finite original
clock vector, complete random-cover trace, source rates and completionKernel
are unchanged. Empty carriers are treated explicitly.

The finite-measure indicator helper below adapts the proof in Mathlib's
MeasureTheory/Integral/Indicator.lean (Kalle Kytölä, copyright 2023,
Apache 2.0), at pinned Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.
Its two prerequisite modules have authenticated artifacts; the Indicator
module itself is not silently imported from an unbound artifact. This
standard measure-theory argument is attributed prior work, not a novelty claim.
-/

namespace GProgram.G2.AncestralTraceSourceLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceEventualCompletionLimit
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.LiteralEpochLaw
open GProgram.G2.FiniteAncestralTrace
open scoped Classical NNReal ENNReal Topology

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.LiteralMarkedClockTrace.choiceOptionMeasurable

/-- Standard finite-measure dominated convergence for eventually equal set
indicators; proof adapted from the attributed Mathlib Indicator source. -/
lemma finite_measure_indicator_limit {A : Type*} [MeasurableSpace A]
    {I : Type*} (L : Filter I) [IsCountablyGenerated L]
    (μ : Measure A) [IsFiniteMeasure μ] (B : Set A) (Bs : I → Set A)
    (hB : MeasurableSet B) (hBs : ∀ i, MeasurableSet (Bs i))
    (he : ∀ x, ∀ᶠ i in L, x ∈ Bs i ↔ x ∈ B) :
    Tendsto (fun i => μ (Bs i)) L (𝓝 (μ B)) := by
  simp_rw [← lintegral_indicator_one hB,← lintegral_indicator_one (hBs _)]
  refine tendsto_lintegral_filter_of_dominated_convergence
    (Set.univ.indicator (1 : A → ℝ≥0∞)) (Eventually.of_forall ?_) ?_ ?_ ?_
  · exact fun i => Measurable.indicator measurable_const (hBs i)
  · exact Eventually.of_forall (fun i => Eventually.of_forall (fun x => by
      by_cases hx : x ∈ Bs i <;> simp [hx]))
  · rw [lintegral_indicator_one MeasurableSet.univ]
    exact measure_ne_top μ Set.univ
  · have hae : ∀ᵐ x ∂μ, ∀ᶠ i in L, x ∈ Bs i ↔ x ∈ B := Eventually.of_forall he
    simpa only [Pi.one_def,tendsto_indicator_const_apply_iff_eventually] using hae

lemma original_clock_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    IsProbabilityMeasure (currentPairClockMeasure N r s) := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  unfold currentPairClockMeasure
  infer_instance

noncomputable def completeEndpoint (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (c : Choice N s → ℝ) : Option (Code N sample) :=
  decodedEndpoint N (Fintype.card Copy) s (completeAncestralTrace N s c)

lemma complete_endpoint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Measurable (completeEndpoint N s) :=
  (decoded_endpoint_measurable N (Fintype.card Copy) s).comp
    (complete_ancestral_trace_measurable N s)

lemma complete_endpoint_clock_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (completeAncestralTraceLaw N r s).map (decodedEndpoint N (Fintype.card Copy) s) =
      (currentPairClockMeasure N r s).map (completeEndpoint N s) := by
  rw [completeAncestralTraceLaw,Measure.map_map
    (decoded_endpoint_measurable N (Fintype.card Copy) s)
    (complete_ancestral_trace_measurable N s)]
  rfl

lemma complete_endpoint_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    IsProbabilityMeasure ((completeAncestralTraceLaw N r s).map
      (decodedEndpoint N (Fintype.card Copy) s)) := by
  letI := complete_ancestral_trace_probability N r s
  exact Measure.isProbabilityMeasure_map
    (decoded_endpoint_measurable N (Fintype.card Copy) s).aemeasurable

/-- Deterministic horizons eventually give the complete endpoint on EACH
same original vector, including raw exceptional/failing vectors. -/
lemma literal_endpoint_eventually_complete (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (c : Choice N s → ℝ) :
    ∀ᶠ t : ℝ≥0 in atTop,
      literalClockEndpoint N (Fintype.card Copy) t s c = completeEndpoint N s c := by
  filter_upwards [eventually_ge_atTop (clockCover N s c)] with t ht
  calc
    literalClockEndpoint N (Fintype.card Copy) t s c =
        decodedEndpoint N (Fintype.card Copy) s
          (literalMarkedTrace N (Fintype.card Copy) t s c) :=
      (marked_trace_endpoint_eq N (Fintype.card Copy) s t c).symm
    _ = completeEndpoint N s c := by
      rw [complete_ancestral_trace_stable N s c t ht]
      rfl

lemma complete_endpoint_mass_tendsto (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (z : Option (Code N sample)) :
    Tendsto (fun t : ℝ≥0 => actualEndpointLaw N r (Fintype.card Copy) s t {z}) atTop
      (𝓝 (((completeAncestralTraceLaw N r s).map
        (decodedEndpoint N (Fintype.card Copy) s)) {z})) := by
  letI := original_clock_probability N r s
  have hlim := finite_measure_indicator_limit atTop (currentPairClockMeasure N r s)
    {c | completeEndpoint N s c = z}
    (fun t : ℝ≥0 => {c | literalClockEndpoint N (Fintype.card Copy) t s c = z})
    (measurableSet_eq_fun (complete_endpoint_measurable N s) measurable_const)
    (fun t => measurableSet_eq_fun
      (literal_endpoint_measurable N (Fintype.card Copy) s t) measurable_const)
    (fun c => (literal_endpoint_eventually_complete N s c).mono
      (fun t he => by simp only [Set.mem_setOf_eq,he]))
  have hf : (fun t : ℝ≥0 => actualEndpointLaw N r (Fintype.card Copy) s t {z}) =
      (fun t : ℝ≥0 => currentPairClockMeasure N r s
        {c | literalClockEndpoint N (Fintype.card Copy) t s c = z}) := by
    funext t
    rw [actual_endpoint_eq_literal_clock_pushforward,
      Measure.map_apply (literal_endpoint_measurable N (Fintype.card Copy) s t) (by trivial)]
    rfl
  have hg : ((completeAncestralTraceLaw N r s).map
      (decodedEndpoint N (Fintype.card Copy) s)) {z} =
      currentPairClockMeasure N r s {c | completeEndpoint N s c = z} := by
    rw [complete_endpoint_clock_law,
      Measure.map_apply (complete_endpoint_measurable N s) (by trivial)]
    rfl
  rw [hf,hg]
  exact hlim

/-- Failure mass vanishes at the random cover by the actual fixed-horizon
failure law and the proved finite-measure limit, without conditioning. -/
theorem complete_endpoint_failure_null (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    ((completeAncestralTraceLaw N r s).map
      (decodedEndpoint N (Fintype.card Copy) s)) {none} = 0 := by
  have hlim := complete_endpoint_mass_tendsto N r s none
  have hf : (fun t : ℝ≥0 => actualEndpointLaw N r (Fintype.card Copy) s t {none}) =
      (fun _ : ℝ≥0 => (0 : ℝ≥0∞)) := by
    funext t
    exact actual_endpoint_failure_null N r (Fintype.card Copy) s t
      (Finset.card_le_univ s.val.live)
  have hz : Tendsto (fun t : ℝ≥0 => actualEndpointLaw N r (Fintype.card Copy) s t {none})
      atTop (𝓝 0) := by rw [hf]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hz

/-- Limit uniqueness binds every genuine endpoint mass to the ORIGINAL
completion PMF. Finite masses justify toReal continuity and injectivity. -/
theorem complete_endpoint_mass_eq_completion [Nonempty Copy]
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (s d : Code N sample) (hs : AncestralRoot N s) :
    ((completeAncestralTraceLaw N r s).map
      (decodedEndpoint N (Fintype.card Copy) s)) {some d} = completionKernel N r s d := by
  letI := complete_endpoint_probability N r s
  have hlim := (ENNReal.tendsto_toReal (measure_ne_top
    ((completeAncestralTraceLaw N r s).map (decodedEndpoint N (Fintype.card Copy) s))
    {some d})).comp (complete_endpoint_mass_tendsto N r s (some d))
  have hf : (fun t : ℝ≥0 => (actualEndpointLaw N r (Fintype.card Copy) s t {some d}).toReal) =
      (fun t : ℝ≥0 => (sourceTimeKernel N r t s d).toReal) := by
    funext t
    rw [actual_endpoint_mass_eq_source_kernel N r (Fintype.card Copy) s d t
      (Finset.card_le_univ s.val.live)]
  change Tendsto (fun t : ℝ≥0 =>
    (actualEndpointLaw N r (Fintype.card Copy) s t {some d}).toReal) atTop _ at hlim
  rw [hf] at hlim
  have he := tendsto_nhds_unique hlim (actual_ancestral_kernel_tendsto_completion N r s d hs)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (PMF.apply_ne_top _ _)).mp he

/-- Empty copies are handled directly: the actual catalogue is empty,
the complete endpoint is the same state, and completionKernel is pure. -/
lemma complete_ancestral_endpoint_law_empty [IsEmpty Copy]
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (s : Code N sample) :
    (completeAncestralTraceLaw N r s).map (decodedEndpoint N (Fintype.card Copy) s) =
      (completionKernel N r s).toMeasure.map some := by
  letI := original_clock_probability N r s
  have hcard : liveCard s ≤ 1 := by
    have h := Finset.card_le_univ s.val.live
    have hz : Fintype.card Copy = 0 := by simp
    change s.val.live.card ≤ 1
    omega
  letI := choice_empty_of_terminal_card N s hcard
  have hpoint : completeEndpoint N s = (fun _ => some s) := by
    funext c
    unfold completeEndpoint completeAncestralTrace
    rw [marked_trace_endpoint_eq]
    have hstop : ∀ p : Choice N s, (clockCover N s c : ℝ) < c p := fun p => isEmptyElim p
    cases Fintype.card Copy <;> simp [literalClockEndpoint,hstop]
  have hm : Measurable (some : Code N sample → Option (Code N sample)) := by
    intro A _; trivial
  rw [complete_endpoint_clock_law,hpoint,completion_terminal N r s hcard,
    PMF.toMeasure_pure,Measure.map_const,Measure.map_dirac' hm]
  simp

/-- Primary unchanged-source endpoint law, including empty/singleton
carriers. The actual random-cover trace is not replaced by a truncation. -/
theorem complete_ancestral_endpoint_source_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) :
    (completeAncestralTraceLaw N r s).map (decodedEndpoint N (Fintype.card Copy) s) =
      (completionKernel N r s).toMeasure.map some := by
  rcases isEmpty_or_nonempty Copy with h | h
  · letI := h
    exact complete_ancestral_endpoint_law_empty N r s
  · letI := h
    letI : MeasurableSingletonClass (Option (Code N sample)) := ⟨fun _ => by trivial⟩
    have hm : Measurable (some : Code N sample → Option (Code N sample)) := by
      intro A _; trivial
    apply Measure.ext_of_singleton
    intro z
    rw [Measure.map_apply hm (measurableSet_singleton z)]
    cases z with
    | none => rw [complete_endpoint_failure_null]; simp
    | some d =>
        rw [complete_endpoint_mass_eq_completion N r s d hs]
        have he : (some : Code N sample → Option (Code N sample)) ⁻¹' {some d} = {d} := by
          ext x; simp
        rw [he,PMF.toMeasure_apply_singleton _ _ (by trivial)]

lemma complete_ancestral_success_ae (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    ∀ᵐ z ∂completeAncestralTraceLaw N r s, z.1 = true := by
  have hm : MeasurableSet {z : Bool × ClockTrace N sample (Fintype.card Copy) | z.1 = true} :=
    measurableSet_eq_fun measurable_fst measurable_const
  rw [completeAncestralTraceLaw]
  apply (ae_map_iff (complete_ancestral_trace_measurable N s).aemeasurable hm).mpr
  filter_upwards [actual_current_clock_regular_ae N r s] with c hc
  exact marked_trace_success_on_regular N (Fintype.card Copy) s (clockCover N s c) c
    (Finset.card_le_univ s.val.live) hc

/-- The total state readout agrees with the decoded endpoint on the proved
full-measure success event; no exceptional endpoint is redefined. -/
theorem complete_ancestral_state_source_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) :
    (completeAncestralTraceLaw N r s).map
      (fun z => traceEndpoint N (Fintype.card Copy) s z.2) =
      (completionKernel N r s).toMeasure := by
  letI : MeasurableSingletonClass (Option (Code N sample)) := ⟨fun _ => by trivial⟩
  have hm : Measurable (fun z : Option (Code N sample) => z.getD s) := measurable_of_countable _
  have hsome : Measurable (some : Code N sample → Option (Code N sample)) := by
    intro A _; trivial
  calc
    _ = (completeAncestralTraceLaw N r s).map
        (fun z => (decodedEndpoint N (Fintype.card Copy) s z).getD s) := by
      apply Measure.map_congr
      filter_upwards [complete_ancestral_success_ae N r s] with z hz
      simp [decodedEndpoint,hz]
    _ = ((completeAncestralTraceLaw N r s).map
        (decodedEndpoint N (Fintype.card Copy) s)).map (fun z => z.getD s) :=
      (Measure.map_map hm (decoded_endpoint_measurable N (Fintype.card Copy) s)).symm
    _ = ((completionKernel N r s).toMeasure.map some).map (fun z => z.getD s) := by
      rw [complete_ancestral_endpoint_source_law N r s hs]
    _ = (completionKernel N r s).toMeasure := by
      rw [Measure.map_map hm hsome]
      simpa only [Function.comp_def,Option.getD_some] using
        (Measure.map_id' (μ := (completionKernel N r s).toMeasure))

#print axioms finite_measure_indicator_limit
#print axioms original_clock_probability
#print axioms complete_endpoint_measurable
#print axioms complete_endpoint_clock_law
#print axioms complete_endpoint_probability
#print axioms literal_endpoint_eventually_complete
#print axioms complete_endpoint_mass_tendsto
#print axioms complete_endpoint_failure_null
#print axioms complete_endpoint_mass_eq_completion
#print axioms complete_ancestral_endpoint_law_empty
#print axioms complete_ancestral_endpoint_source_law
#print axioms complete_ancestral_success_ae
#print axioms complete_ancestral_state_source_law

end GProgram.G2.AncestralTraceSourceLaw
