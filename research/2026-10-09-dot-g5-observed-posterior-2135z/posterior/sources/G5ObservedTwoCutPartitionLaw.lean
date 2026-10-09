import G5ActualTwoCutPartitionLaw

namespace GProgram.G5.ObservedTwoCutPartitionLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeIndependentPairMixture
open GProgram.G2.CalendarFirstAge GProgram.G2.ChronologicalPathReadout
open GProgram.G5.HiddenRegisterTimedProjectivity GProgram.G5.ObservedBinHistory
open GProgram.G5.TwoCutSourceWord GProgram.G5.TwoCutPartitionDecoder
open GProgram.G5.ActualTwoCutPartitionLaw GProgram.G5.OriginalProgramSurvival
open GProgram.G5.EnumeratedTripleRow
attribute [local instance] GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Original hidden timed observation, decoded at two cuts of one actual
ordinary interval, is exactly the genuine prefix/future partition joint law. -/
theorem actual_observed_two_cut_partition_law (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common =
      pre ++ .interval (a+(b+c)) :: post) (i : Fin 3 ≃ Copy) :
    let left := firstOriginalDate N C + (programDuration N pre : ℝ) + (a:ℝ)
    let right := left + (b:ℝ)
    (naturalObservedFullLaw N C sample H p common r).map
      (fun o => let B := observedAgeBins (twoCutBin left right) o
        (binPartition i 0 B,binPartition i 1 B)) =
    ((originalProgramLaw N sample p r (pre ++ [.interval a])).bind (fun d =>
      (sourceProgram N r [.interval b] d).map (fun e =>
        (indexedPartition N i d,indexedPartition N i e)))).toMeasure := by
  dsimp only
  let left := firstOriginalDate N C + (programDuration N pre : ℝ) + (a:ℝ)
  let right := left + (b:ℝ)
  have hb := observed_age_bins_measurable (Copy := Copy) (twoCutBin left right)
    (two_cut_bin_measurable left right)
  have hr : Measurable (fun B : Copy → Copy → Fin 3 =>
      (binPartition i 0 B,binPartition i 1 B)) := measurable_of_countable _
  change (naturalObservedFullLaw N C sample H p common r).map
    ((fun B => (binPartition i 0 B,binPartition i 1 B)) ∘
      observedAgeBins (twoCutBin left right)) = _
  rw [← Measure.map_map hr hb]
  rw [actual_natural_observed_two_cut_law N C sample H p common r pre post a b c hwhole]
  rw [PMF.toMeasure_map _ _ hr]
  congr 1
  exact actual_natural_two_cut_partition_pmf N C sample H p common r pre post a b c
    hwhole i (firstOriginalDate N C) (fun x _ => C.age (N.leaf (sample x)))

#print axioms actual_observed_two_cut_partition_law
end GProgram.G5.ObservedTwoCutPartitionLaw
