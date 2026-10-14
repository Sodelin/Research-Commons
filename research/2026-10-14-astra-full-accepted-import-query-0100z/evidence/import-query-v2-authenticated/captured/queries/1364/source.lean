import G5TimedCutReadout
import G5HiddenRegisterTimedProjectivity

/-! Actual once-drawn-register assembly of the already proved same-record cut
readout identities. Contributor: dot / OpenAI, 9 October 2026.
This is a formal use-site of accepted natural-register and timed-output laws. -/
namespace GProgram.G5.NaturalCutConsumer
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

lemma registered_ae_of_rows (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (rho : PMF (V → Bool))
    (P : RegisteredRecord N sample ops → Prop)
    (h : ∀ reg, ∀ᵐ z ∂completeCalendarTraceLaw N r ops (initialCode N sample reg), P (reg,z)) :
    ∀ᵐ z ∂registeredTraceLaw N sample r ops rho, P z := by
  rw [registeredTraceLaw, ae_finsetSum_measure_iff]
  intro reg _
  apply Measure.ae_smul_measure
  exact (measurableEmbedding_prodMk_left reg).ae_map_iff.mpr (h reg)

noncomputable def registeredCutState (N : RootedBinary V E X) (sample : Copy → X)
    (ops : List (ProgramStep N)) (z : RegisteredRecord N sample ops) (t : ℝ≥0) :
    Code N sample :=
  GProgram.G2.CalendarFirstAge.recordPath N ops (initialCode N sample z.1)
    z.2.2.1 z.2.2.2.2 t

/-- One full-mass set for all cuts, under the actual once-drawn register law.
No posterior independence or hidden-register observation is assumed. -/
theorem actual_natural_timed_cut_readouts (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (keep : Finset Copy) (e : Fin 3 → Copy) (he : Function.Injective e)
    (hk : ∀ i, e i ∈ keep) :
    ∀ᵐ z ∂originalTimedTraceLaw N C sample H p common r,
      ∀ t : ℝ≥0,
      (TimedNoMerger keep (firstOriginalDate N C + (t:ℝ))
        ((fullReadout N C sample keep (compiledCalendarProgram N C H (originalGamma p) common) z).2) ↔
        DiscreteView keep (selectedView (state (registeredCutState N sample
          (compiledCalendarProgram N C H (originalGamma p) common) z t)) keep)) ∧
      timedPartitionAt e (firstOriginalDate N C + (t:ℝ))
        ((fullReadout N C sample keep (compiledCalendarProgram N C H (originalGamma p) common) z).2) =
        ancestorPartition (fun i => (state (registeredCutState N sample
          (compiledCalendarProgram N C H (originalGamma p) common) z t)).ancestor (e i)) := by
  apply registered_ae_of_rows
  intro reg
  filter_upwards [actual_timed_survival_is_cut_discreteness N C sample reg H
    (originalGamma p) common r keep,
    actual_timed_partition_is_cut_partition N C sample reg H (originalGamma p) common r keep e he hk]
    with z hz hp
  intro t
  exact ⟨hz t, hp t⟩

#print axioms registered_ae_of_rows
#print axioms actual_natural_timed_cut_readouts
end GProgram.G5.NaturalCutConsumer
