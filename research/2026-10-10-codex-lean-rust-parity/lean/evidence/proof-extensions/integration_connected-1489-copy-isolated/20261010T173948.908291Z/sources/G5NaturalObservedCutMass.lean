import G5NaturalCutConsumer

/-! Original hidden-register timed observation supplies actual joint cut-event
masses. Contributor: dot / OpenAI, 9 October 2026. No posterior law is assumed. -/
namespace GProgram.G5.NaturalObservedCutMass
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceCuts
open GProgram.G2.ActualCalendarTrace GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.PairBirthFold GProgram.G2.PairBirthThreshold
open GProgram.G2.WholeMatrixAges GProgram.G2.AncestralAgeCertificate
open GProgram.G2.CalendarDecoration GProgram.G2.CompleteDecoration
open GProgram.G2.ActualPairCoalescence GProgram.G2.CalendarFirstAge
open GProgram.G2.SourcePairMatrixReadout GProgram.G2.FaithfulTimedOutput
open GProgram.G2.JointTimedObservation GProgram.G2.ChronologicalPathReadout
open GProgram.G2.CompletedPathProjection GProgram.G2.CompleteEpochPath
open GProgram.G5.SelectedDiscreteSurvival GProgram.G5.TriplePartitionReadout
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
  GProgram.G2.CalendarHistoryBinding.joinedMeasurable


open GProgram.G2.ControlledTraceAssembly GProgram.G2.ActualTimedAllPanelLaw
open GProgram.G2.RegisteredPathProjection GProgram.G5.HiddenRegisterTimedProjectivity
open GProgram.G5.TimedCutReadout
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization


open GProgram.G5.NaturalCutConsumer

/-- The authorized hidden-register observation determines the actual source
joint survival-at-t / partition-at-u mass. For a selected triple, apply this
on the actual selected source provided by inherited all-panel projectivity. -/
theorem actual_observed_joint_cut_mass (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (e : Fin 3 → Copy) (he : Function.Injective e) (t u : ℝ≥0) (gene : Fin 5) :
    naturalObservedFullLaw N C sample H p common r
      {o | TimedNoMerger Finset.univ (firstOriginalDate N C + (t:ℝ)) o ∧
        timedPartitionAt e (firstOriginalDate N C + (u:ℝ)) o = gene} =
    originalTimedTraceLaw N C sample H p common r
      {z | DiscreteView Finset.univ (selectedView (state (registeredCutState N sample
          (compiledCalendarProgram N C H (originalGamma p) common) z t)) Finset.univ) ∧
        ancestorPartition (fun i => (state (registeredCutState N sample
          (compiledCalendarProgram N C H (originalGamma p) common) z u)).ancestor (e i)) = gene} := by
  have hset : MeasurableSet {o : TimedObservation Copy |
      TimedNoMerger Finset.univ (firstOriginalDate N C + (t:ℝ)) o ∧
      timedPartitionAt e (firstOriginalDate N C + (u:ℝ)) o = gene} :=
    (timed_no_merger_measurable _ _).inter
      (measurableSet_eq_fun (timed_partition_at_measurable e _) measurable_const)
  unfold naturalObservedFullLaw
  rw [Measure.map_map erase_register_measurable (full_readout_measurable N C sample Finset.univ _),
    Measure.map_apply (erase_register_measurable.comp (full_readout_measurable N C sample Finset.univ _)) hset]
  apply measure_congr
  filter_upwards [actual_natural_timed_cut_readouts N C sample H p common r Finset.univ e he
    (fun _ => Finset.mem_univ _)] with z hz
  apply propext
  change (TimedNoMerger Finset.univ (firstOriginalDate N C + (t:ℝ))
      ((fullReadout N C sample Finset.univ (compiledCalendarProgram N C H (originalGamma p) common) z).2) ∧
      timedPartitionAt e (firstOriginalDate N C + (u:ℝ))
      ((fullReadout N C sample Finset.univ (compiledCalendarProgram N C H (originalGamma p) common) z).2) = gene) ↔ _
  exact and_congr (hz t).1 (congrArg (fun q => q = gene) (hz u).2).to_iff


theorem actual_observed_survival_cut_mass (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (e : Fin 3 → Copy) (he : Function.Injective e) (t : ℝ≥0) :
    naturalObservedFullLaw N C sample H p common r
      {o | TimedNoMerger Finset.univ (firstOriginalDate N C + (t:ℝ)) o} =
    originalTimedTraceLaw N C sample H p common r
      {z | DiscreteView Finset.univ (selectedView (state (registeredCutState N sample
          (compiledCalendarProgram N C H (originalGamma p) common) z t)) Finset.univ)} := by
  unfold naturalObservedFullLaw
  rw [Measure.map_map erase_register_measurable (full_readout_measurable N C sample Finset.univ _),
    Measure.map_apply (erase_register_measurable.comp (full_readout_measurable N C sample Finset.univ _))
      (timed_no_merger_measurable _ _)]
  apply measure_congr
  filter_upwards [actual_natural_timed_cut_readouts N C sample H p common r Finset.univ e he
    (fun _ => Finset.mem_univ _)] with z hz
  apply propext
  exact (hz t).1

#print axioms actual_observed_survival_cut_mass
#print axioms actual_observed_joint_cut_mass
end GProgram.G5.NaturalObservedCutMass
