import G5ObservedBinHistory
import NaturalAncestralCutExtension

/-! Direct observation binding for the already constructed natural completed
joint law, reusable under its exact same-source ancestral interval extension. -/
namespace GProgram.G5.ObservedCompletedBins
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.ControlledTraceAssembly
open GProgram.G2.ActualTimedAllPanelLaw GProgram.G2.CalendarFirstAge
open GProgram.G5.HiddenRegisterTimedProjectivity GProgram.G5.ObservedBinHistory
open CloudG3.ActualCalendarCutContext CloudG6.NaturalPastCompleteObservation
open CloudG6.NaturalCalendarPastAdmission
open scoped Classical NNReal
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
  GProgram.G2.CalendarHistoryBinding.joinedMeasurable

theorem actual_observed_completed_bins (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin) :
    (naturalObservedFullLaw N C sample H p common r).map (observedAgeBins bin) =
      ((naturalCompletedJoint N C sample p r bin hbin
        (compiledCalendarProgram N C H (originalGamma p) common)).map Prod.snd).toMeasure := by
  have hm := observed_age_bins_measurable (Copy := Copy) bin hbin
  unfold naturalObservedFullLaw naturalCompletedJoint
  rw [PMF.map_bind]
  rw [Measure.map_map hm erase_register_measurable,
    Measure.map_map (hm.comp erase_register_measurable)
      (full_readout_measurable N C sample Finset.univ _)]
  apply registered_map_of_row_law
  · exact (hm.comp erase_register_measurable).comp
      (full_readout_measurable N C sample Finset.univ _)
  · intro reg
    rw [←PMF.toMeasure_map _ _ measurable_snd,completed_joint_toMeasure,
      Measure.map_map measurable_snd (complete_readout_measurable N bin hbin _ _ _ _)]
    exact Measure.map_congr
      (actual_original_observed_age_bins N C sample reg H (originalGamma p) common r bin)

/-- Exposing extra time in the same ancestral source leaves the actual
hidden timed observation's finite-bin law unchanged. -/
theorem actual_observed_completed_bins_extended (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin) (duration : ℝ≥0) :
    (naturalObservedFullLaw N C sample H p common r).map (observedAgeBins bin) =
      ((naturalCompletedJoint N C sample p r bin hbin
        (compiledCalendarProgram N C H (originalGamma p) common ++ [.interval duration])).map Prod.snd).toMeasure := by
  rw [actual_observed_completed_bins N C sample H p common r bin hbin,
    UnifiedLean.G6.NaturalAncestralCutExtension.natural_completed_append_interval N C sample p r bin hbin _ duration]

#print axioms actual_observed_completed_bins
#print axioms actual_observed_completed_bins_extended
end GProgram.G5.ObservedCompletedBins
