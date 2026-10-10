import G5TwoCutCompletedSource
import G5HiddenRegisterTimedProjectivity
import G5TimedCutReadout

/-! Coarsening the actual hidden-register observation uses the already proved
original same-record matrix/tag identity. dot / OpenAI,9 October2026. -/
namespace GProgram.G5.ObservedBinHistory
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


open CloudG3.CompleteCalendarBinReadout GProgram.G5.TwoCutSourceWord

noncomputable def observedAgeBins {Tag : Type*} (bin : ℝ → Tag) (o : TimedObservation Copy) :
    Copy → Copy → Tag := fun x y => bin (o.2 x y).2

lemma observed_age_bins_measurable {Tag : Type*} [MeasurableSpace Tag]
    (bin : ℝ → Tag) (hbin : Measurable bin) :
    Measurable (observedAgeBins (Copy := Copy) bin) := by
  apply measurable_pi_lambda
  intro x
  apply measurable_pi_lambda
  intro y
  exact hbin.comp (((measurable_pi_apply y).comp
    ((measurable_pi_apply x).comp measurable_snd)).snd)

/-- No new binned observation law is postulated: the ordinary timed output
and the actual complete record have identical age bins almost surely. -/
theorem actual_original_observed_age_bins {Tag : Type*}
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (reg : V → Bool) (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (bin : ℝ → Tag) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample reg),
      observedAgeBins bin ((fullReadout N C sample Finset.univ
        (compiledCalendarProgram N C H gamma common) (reg,z)).2) =
      completeTags N bin (compiledCalendarProgram N C H gamma common) (initialCode N sample reg)
        (firstOriginalDate N C) (fun x y => bin (C.age (N.leaf (sample x)))) z := by
  filter_upwards [actual_original_faithful_output N C sample reg H gamma common r Finset.univ]
    with z hz
  change observedAgeBins bin (timedObservation N C sample Finset.univ
    (chronologicalPath N (compiledCalendarProgram N C H gamma common)
      (observeCompleted N (fun d => joinedProjection N Finset.univ (.inl d))
        (compiledCalendarProgram N C H gamma common) (initialCode N sample reg) z))) = _
  unfold observedAgeBins
  rw [hz]
  simpa only [matrixObservation,Finset.mem_univ,and_self,if_true] using
    map_complete_matrix N bin (compiledCalendarProgram N C H gamma common)
      (initialCode N sample reg) (firstOriginalDate N C)
      (fun x _ => C.age (N.leaf (sample x))) z

open GProgram.G5.TwoCutCompletedSource
open GProgram.G2.SourceFiniteHistory
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualTailBinRow CloudG3.CompleteCalendarJointLaw

noncomputable def twoCutTagKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) : PMF (Copy → Copy → Fin 3) :=
  let left := offset + (programDuration N pre : ℝ) + (a:ℝ)
  let right := left + (b:ℝ)
  (((sourceHistoryLaw N r (physicalOps N (twoCutWord N pre post a b c)) s).map
    (endpointHistoryReadout N (twoCutWord N pre post a b c) s
      (fun x y => twoCutBin left right (M x y)))).bind
    (jointTailKernel N r (2 : Fin 3))).map Prod.snd

theorem actual_observed_two_cut_row (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (reg : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (hwhole : compiledCalendarProgram N C H gamma common = pre ++ .interval (a+(b+c)) :: post) :
    let left := firstOriginalDate N C + (programDuration N pre : ℝ) + (a:ℝ)
    let right := left + (b:ℝ)
    (completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample reg)).map
      (fun z => observedAgeBins (twoCutBin left right)
        ((fullReadout N C sample Finset.univ (compiledCalendarProgram N C H gamma common) (reg,z)).2)) =
      (twoCutTagKernel N r pre post a b c (initialCode N sample reg) (firstOriginalDate N C)
        (fun x _ => C.age (N.leaf (sample x)))).toMeasure := by
  dsimp only
  let left := firstOriginalDate N C + (programDuration N pre : ℝ) + (a:ℝ)
  let right := left + (b:ℝ)
  have hc := actual_initialized_two_cut_completed_law N C sample reg H gamma common r
    pre post a b c hwhole (fun x _ => C.age (N.leaf (sample x)))
  dsimp only at hc
  rw [←hwhole] at hc
  have hs := congrArg (fun mu => Measure.map Prod.snd mu) hc
  rw [Measure.map_map measurable_snd
    (complete_joint_bin_readout_measurable N (twoCutBin left right) (two_cut_bin_measurable left right)
      (compiledCalendarProgram N C H gamma common) (initialCode N sample reg)
      (firstOriginalDate N C) (fun x _ => C.age (N.leaf (sample x))))] at hs
  unfold twoCutTagKernel
  rw [←PMF.toMeasure_map _ _ measurable_snd]
  apply Eq.trans (Measure.map_congr (actual_original_observed_age_bins N C sample reg H gamma common r
    (twoCutBin left right)))
  exact hs

/-- The ordinary hidden-register observed two-cut bin law is the explicitly
constructed finite source-history/completion law with ONE original register
mixture. No desired law or posterior equation is a hypothesis. -/
theorem actual_natural_observed_two_cut_law (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common =
      pre ++ .interval (a+(b+c)) :: post) :
    let left := firstOriginalDate N C + (programDuration N pre : ℝ) + (a:ℝ)
    let right := left + (b:ℝ)
    (naturalObservedFullLaw N C sample H p common r).map
      (observedAgeBins (twoCutBin left right)) =
      ((originalRegisterPMF N p).bind (fun reg =>
        twoCutTagKernel N r pre post a b c (initialCode N sample reg) (firstOriginalDate N C)
          (fun x _ => C.age (N.leaf (sample x))))).toMeasure := by
  dsimp only
  let left := firstOriginalDate N C + (programDuration N pre : ℝ) + (a:ℝ)
  let right := left + (b:ℝ)
  have hm := observed_age_bins_measurable (Copy := Copy) (twoCutBin left right)
    (two_cut_bin_measurable left right)
  unfold naturalObservedFullLaw
  rw [Measure.map_map hm erase_register_measurable,
    Measure.map_map (hm.comp erase_register_measurable)
      (full_readout_measurable N C sample Finset.univ _)]
  apply registered_map_of_row_law
  · exact (hm.comp erase_register_measurable).comp
      (full_readout_measurable N C sample Finset.univ _)
  · intro reg
    exact actual_observed_two_cut_row N C sample reg H (originalGamma p) common r pre post a b c hwhole

#print axioms actual_natural_observed_two_cut_law
#print axioms actual_observed_two_cut_row
#print axioms observed_age_bins_measurable
#print axioms actual_original_observed_age_bins
end GProgram.G5.ObservedBinHistory
