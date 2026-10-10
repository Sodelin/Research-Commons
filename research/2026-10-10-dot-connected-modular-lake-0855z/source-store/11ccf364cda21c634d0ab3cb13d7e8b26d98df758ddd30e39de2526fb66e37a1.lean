import G5ObservedCompletedBins

/-! Exact SAME-RECORD original observed unranked forest and age-bin matrix.
The reader exposes no register, population, genealogy order or raw Code.
Contributor: dot / OpenAI, 9 October 2026. -/
namespace GProgram.G5.ObservedForestBins
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.ControlledTraceAssembly
open GProgram.G2.ActualTimedAllPanelLaw GProgram.G2.CalendarFirstAge
open GProgram.G2.JointTimedObservation GProgram.G2.FaithfulTimedOutput
open GProgram.G2.ChronologicalPathReadout GProgram.G2.CompleteDecoration
open GProgram.G2.CompletedPathProjection
open GProgram.G5.HiddenRegisterTimedProjectivity GProgram.G5.ObservedBinHistory
open CloudG3.ActualCalendarCutContext CloudG3.CompleteCalendarBinReadout CloudG3.ActualCutJointLaw
open CloudG6.NaturalPastCompleteObservation CloudG6.NaturalCalendarPastAdmission
open scoped Classical NNReal
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
  GProgram.G2.CalendarHistoryBinding.joinedMeasurable

/-- Total observable reader. The empty fallback on a missing terminal value
is irrelevant under the actual law, whose same-record theorem gives `some`.
It is not success conditioning. -/
noncomputable def observedForestBins (bin : ℝ → Tag) (o : TimedObservation Copy) :
    Finset (UnrankedTree Copy) × (Copy → Copy → Tag) :=
  (o.1.getD ∅, observedAgeBins bin o)

noncomputable def completedForestBins (N : RootedBinary V E X) {sample : Copy → X}
    (q : TaggedEndpoint (Tag := Tag) N sample) :
    Finset (UnrankedTree Copy) × (Copy → Copy → Tag) :=
  (sourceUnrankedForest (state q.1) Finset.univ,q.2)

lemma observed_forest_bins_measurable (bin : ℝ → Tag) (hbin : Measurable bin) :
    Measurable (observedForestBins (Copy := Copy) bin) := by
  have hf : Measurable (fun o : Option (Finset (UnrankedTree Copy)) => o.getD ∅) :=
    measurable_of_countable _
  exact (hf.comp measurable_fst).prodMk (observed_age_bins_measurable bin hbin)

lemma completed_forest_bins_measurable (N : RootedBinary V E X) (sample : Copy → X) :
    Measurable (completedForestBins (Tag := Tag) N (sample := sample)) :=
  measurable_of_countable _

/-- The JOINT identity uses the same complete record for both coordinates.
It is not inferred by combining two marginal distribution identities. -/
theorem actual_original_observed_forest_bins (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (reg : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (bin : ℝ → Tag) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample reg),
      observedForestBins bin ((fullReadout N C sample Finset.univ
        (compiledCalendarProgram N C H gamma common) (reg,z)).2) =
      completedForestBins N (completeReadout N bin (compiledCalendarProgram N C H gamma common)
        (initialCode N sample reg) (firstOriginalDate N C)
        (fun x y => bin (C.age (N.leaf (sample x)))) z) := by
  filter_upwards [actual_original_faithful_output N C sample reg H gamma common r Finset.univ,
    actual_original_observed_age_bins N C sample reg H gamma common r bin] with z hz hb
  apply Prod.ext
  · change (timedObservation N C sample Finset.univ
      (chronologicalPath N (compiledCalendarProgram N C H gamma common)
        (observeCompleted N (fun d => joinedProjection N Finset.univ (.inl d))
          (compiledCalendarProgram N C H gamma common) (initialCode N sample reg) z))).1.getD ∅ = _
    rw [hz]
    rfl
  · exact hb

/-- Exact ordinary unranked-forest/finite-bin joint law, mixed once with the
original register. Its output type is independent of the source graph. -/
theorem actual_observed_completed_forest_bins (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin) :
    (naturalObservedFullLaw N C sample H p common r).map (observedForestBins bin) =
      ((naturalCompletedJoint N C sample p r bin hbin
        (compiledCalendarProgram N C H (originalGamma p) common)).map
          (completedForestBins N)).toMeasure := by
  have hm := observed_forest_bins_measurable (Copy := Copy) bin hbin
  have hr := completed_forest_bins_measurable (Tag := Tag) N sample
  unfold naturalObservedFullLaw naturalCompletedJoint
  rw [PMF.map_bind]
  rw [Measure.map_map hm erase_register_measurable,
    Measure.map_map (hm.comp erase_register_measurable)
      (full_readout_measurable N C sample Finset.univ _)]
  apply registered_map_of_row_law
  · exact (hm.comp erase_register_measurable).comp
      (full_readout_measurable N C sample Finset.univ _)
  · intro reg
    rw [←PMF.toMeasure_map _ _ hr,completed_joint_toMeasure,
      Measure.map_map hr (complete_readout_measurable N bin hbin _ _ _ _)]
    exact Measure.map_congr
      (actual_original_observed_forest_bins N C sample reg H (originalGamma p) common r bin)

theorem actual_observed_completed_forest_bins_extended (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin) (duration : ℝ≥0) :
    (naturalObservedFullLaw N C sample H p common r).map (observedForestBins bin) =
      ((naturalCompletedJoint N C sample p r bin hbin
        (compiledCalendarProgram N C H (originalGamma p) common ++ [.interval duration])).map
          (completedForestBins N)).toMeasure := by
  rw [actual_observed_completed_forest_bins N C sample H p common r bin hbin,
    UnifiedLean.G6.NaturalAncestralCutExtension.natural_completed_append_interval N C sample p r bin hbin _ duration]

/-- The exact G6 finite-reader use-site, without importing an unverified
source-image module. The reader sees only ordinary topology and age bins. -/
theorem actual_observed_finite_forest_bin_reader {O : Type*} [MeasurableSpace O]
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : (Finset (UnrankedTree Copy) × (Copy → Copy → Tag)) → O) :
    (naturalObservedFullLaw N C sample H p common r).map
      (reader ∘ observedForestBins bin) =
      ((naturalCompletedJoint N C sample p r bin hbin
        (compiledCalendarProgram N C H (originalGamma p) common)).map
          (reader ∘ completedForestBins N)).toMeasure := by
  have hr : Measurable reader := measurable_of_countable _
  rw [← Measure.map_map hr (observed_forest_bins_measurable bin hbin),
    actual_observed_completed_forest_bins N C sample H p common r bin hbin,
    PMF.toMeasure_map _ _ hr,PMF.map_comp]

#print axioms actual_original_observed_forest_bins
#print axioms actual_observed_completed_forest_bins
#print axioms actual_observed_completed_forest_bins_extended
#print axioms actual_observed_finite_forest_bin_reader
end GProgram.G5.ObservedForestBins
