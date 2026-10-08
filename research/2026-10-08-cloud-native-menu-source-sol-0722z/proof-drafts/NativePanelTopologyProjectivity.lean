import NaturalCompletedAllPairs
import UnifiedLean.Source.SourceUnrankedAllPanels

/-!
Cloud Sol /root/source_backend_review_sol, 8 October 2026.
Authored SOURCE/HAND, compiler UNCHECKED/outside179/181.
The ACTUAL tagged complete endpoint marginal is the original completion law.
Compose with the source-derived ALL-panel unranked copy-projectivity theorem.
This proves topology-only smaller-source equality; joint physical pair-bin or
menu projectivity is deliberately left as a separate chronological obligation.
-/
namespace CloudG6.NativePanelTopologyProjectivity

open MeasureTheory ProbabilityTheory Filter Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceCompletedUnrankedTree UnifiedLean.Source.SourceUnrankedAllPanels
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceUnrankedCopyProjectivity
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.AncestralTraceSourceLaw
open GProgram.G2.FiniteAncestralTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompleteDecoration
open CloudG3.ActualCutJointLaw CloudG3.ActualCalendarCutContext
open CloudG6.ActualFiniteObservableRecord CloudG6.ActualPanelForestReadout
open CloudG6.NaturalPastCompleteObservation CloudG6.NaturalCompletedAllPairs
open CloudG6.ActualSourceCorruptionClasses CloudG6.ActualObservationCorruption
open scoped Classical

universe u v w x y
variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

/-- Actual unconditional success on every complete-record fibre. No success
conditioning, fallback replacement or desired completed endpoint law. -/
theorem complete_records_success_ae (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s, z.2.2.1 = true := by
  rw [completeCalendarTraceLaw, ae_finsetSum_measure_iff]
  intro d _
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have hi : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d, z)) :=
    measurable_const.prodMk measurable_id
  have hm : MeasurableSet {z : CompleteCalendarRecord N sample ops | z.2.2.1 = true} :=
    measurableSet_eq_fun measurable_snd.snd.fst measurable_const
  apply (ae_map_iff hi.aemeasurable hm).mpr
  apply (Measure.ae_prod_iff_ae_ae (hm.preimage hi)).mpr
  exact Eventually.of_forall (fun _ => complete_ancestral_success_ae N r d)

/-- The full actual initialized calendar supplies root support in the
original endpoint law. Total raw endpoint agrees on the derived success event. -/
theorem initialized_raw_completed_endpoint_source (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    (completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register)).map
        (completeEnd N (compiledCalendarProgram N C H gamma common)) =
      ((sourceProgram N r (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register)).bind (completionKernel N r)).toMeasure := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  have hg : Measurable (fun z : Option (Code N sample) => z.getD s) := measurable_of_countable _
  have hsome : Measurable (some : Code N sample → Option (Code N sample)) := measurable_of_countable _
  calc
    _ = (completeCalendarTraceLaw N r ops s).map
        ((fun z : Option (Code N sample) => z.getD s) ∘ completedCalendarEndpoint N ops) := by
      apply Measure.map_congr
      filter_upwards [complete_records_success_ae N r ops s] with z hz
      simp [Function.comp_def, completeEnd, completedCalendarEndpoint, decodedEndpoint, hz]
    _ = ((completeCalendarTraceLaw N r ops s).map (completedCalendarEndpoint N ops)).map
        (fun z : Option (Code N sample) => z.getD s) :=
      (Measure.map_map hg (completed_calendar_endpoint_measurable N ops)).symm
    _ = (((sourceProgram N r ops s).bind (completionKernel N r)).toMeasure.map some).map
        (fun z : Option (Code N sample) => z.getD s) := by
      rw [original_completed_calendar_endpoint_law N C sample register H gamma common r]
    _ = ((sourceProgram N r ops s).bind (completionKernel N r)).toMeasure := by
      rw [Measure.map_map hg hsome]
      simpa only [Function.comp_def, Option.getD_some] using
        (Measure.map_id' (μ := ((sourceProgram N r ops s).bind (completionKernel N r)).toMeasure))

/-- Forget ONLY carried tags from the ACTUAL initialized joint physical row. -/
theorem initialized_completed_joint_endpoint (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) :
    (completedJoint N r bin hbin (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register) (firstOriginalDate N C)
      (fun a b => bin (leafAgeMatrix N C sample a b))).map Prod.fst =
      (sourceProgram N r (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register)).bind (completionKernel N r) := by
  letI : MeasurableSingletonClass (Code N sample) := ⟨fun _ => by trivial⟩
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ measurable_fst, completed_joint_toMeasure,
    Measure.map_map measurable_fst (complete_readout_measurable N bin hbin
      (compiledCalendarProgram N C H gamma common) (initialCode N sample register)
      (firstOriginalDate N C) (fun a b => bin (leafAgeMatrix N C sample a b)))]
  change (completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
    (initialCode N sample register)).map
      (completeEnd N (compiledCalendarProgram N C H gamma common)) = _
  exact initialized_raw_completed_endpoint_source N C sample register H gamma common r

/-- The SAME once-drawn original register bind gives the actual completed
endpoint law; no register independence, fitted prior or terminal law is input. -/
theorem natural_completed_joint_endpoint (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) :
    (naturalCompletedJoint N C sample p r bin hbin
      (compiledCalendarProgram N C H (originalGamma p) common)).map Prod.fst =
      naturalCompletedLaw N C sample H p common r := by
  unfold naturalCompletedJoint naturalCompletedLaw naturalCalendarLaw
  rw [PMF.map_bind, PMF.bind_bind]
  congr 1
  funext register
  exact initialized_completed_joint_endpoint N C sample register H (originalGamma p) common r bin hbin

/-- Genuine separately initialized selected-source TOPOLOGY comparison for
ALL panels, empty included. Graph/ages/rates/parents/mode and register prior are
the original ones. This theorem does not compare joint physical bin tables. -/
theorem native_panel_topology_smaller_source (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    {sample : Copy → X} (s : OriginalParameters.{u,v,w,x} Copy X sample) (keep : Finset Copy) :
    (nativeFiniteLaw mode bin hbin s).map (fun a => (finitePanelReadout keep a).val.1) =
      (naturalCompletedUnrankedLaw s.original.network s.original.calendar
        (selectedSample sample keep) s.registry s.inheritance (fun _ => mode) s.rates).map
        (fun F => F.image (mapUnranked Subtype.val)) := by
  calc
    _ = (((nativeFiniteLaw mode bin hbin s).map (finitePanelReadout keep)).map
        Subtype.val).map Prod.fst := by
      rw [PMF.map_comp, PMF.map_comp]
      rfl
    _ = ((naturalCompletedJoint s.original.network s.original.calendar sample s.inheritance
        s.rates bin hbin (compiledCalendarProgram s.original.network s.original.calendar s.registry
          (originalGamma s.inheritance) (fun _ => mode))).map
        (endpointPanelReadout s.original.network keep)).map Prod.fst := by
      rw [native_finite_panel_source]
    _ = ((naturalCompletedJoint s.original.network s.original.calendar sample s.inheritance
        s.rates bin hbin (compiledCalendarProgram s.original.network s.original.calendar s.registry
          (originalGamma s.inheritance) (fun _ => mode))).map Prod.fst).map
        (fun d => sourceUnrankedForest (state d) keep) := by
      rw [PMF.map_comp, PMF.map_comp]
      rfl
    _ = (naturalCompletedLaw s.original.network s.original.calendar sample s.registry
        s.inheritance (fun _ => mode) s.rates).map (fun d => sourceUnrankedForest (state d) keep) := by
      rw [natural_completed_joint_endpoint]
    _ = _ := actual_complete_unranked_all_panel_projectivity s.original.network
      s.original.calendar sample keep s.registry s.inheritance (fun _ => mode) s.rates

end CloudG6.NativePanelTopologyProjectivity
