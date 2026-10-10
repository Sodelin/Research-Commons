import G2ActualTimedAllPanelLaw

/-!
Forgetting the faithful timed output recovers the previously accepted original
completed unranked law, including exact fixed-ID controls.
Contributor: dot (OpenAI), 6 October 2026.
-/
namespace GProgram.G2.TimedOutputForgetting
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.UnrankedGenealogyObservation UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.OriginalFixedIDControls UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G2.JointTimedObservation GProgram.G2.ActualTimedAllPanelLaw
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.ControlledTraceAssembly
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.FiniteAncestralTrace
open GProgram.G2.CompleteDecoration GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteTerminalReadout GProgram.G2.EventualPathReadout
open GProgram.G2.RegisteredPathProjection GProgram.G2.ChronologicalPathReadout
open GProgram.G2.CompletedPathProjection
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.CalendarHistoryBinding.joinedMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.LiteralMarkedClockTrace.choiceOptionMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable

noncomputable def forgetOutput (o : (V → Bool) × TimedObservation Copy) : Finset (UnrankedTree Copy) :=
  o.2.1.getD ∅

lemma forget_output_measurable : Measurable (forgetOutput (V := V) (Copy := Copy)) :=
  (measurable_of_countable (fun o : Option (Finset (UnrankedTree Copy)) => o.getD ∅)).comp measurable_snd.fst

lemma actual_completed_endpoint_some (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s,
      completedCalendarEndpoint N ops z = some (completeEnd N ops z) := by
  have hm := measurableSet_eq_fun (completed_calendar_endpoint_measurable N ops)
    ((measurable_of_countable (some : Code N sample → Option (Code N sample))).comp (complete_end_measurable N ops))
  rw [completeCalendarTraceLaw,ae_finsetSum_measure_iff]
  intro d _
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have hmap : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) := measurable_const.prodMk measurable_id
  apply (ae_map_iff hmap.aemeasurable hm).mpr
  apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
  apply Filter.Eventually.of_forall
  intro past
  rw [completeAncestralTraceLaw]
  have hin : Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) => (d,past,z)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  apply (ae_map_iff (complete_ancestral_trace_measurable N d).aemeasurable (hm.preimage hin)).mpr
  filter_upwards [actual_current_clock_regular_ae N r d] with c hc
  have hg := marked_trace_success_on_regular N (Fintype.card Copy) d (clockCover N d c : ℝ)
    c (Finset.card_le_univ d.val.live) hc
  change decodedEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d c) = _
  simp only [decodedEndpoint,completeAncestralTrace,hg,if_true,Function.comp_apply,completeEnd]

noncomputable def forgetRegisteredTrace (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (z : RegisteredRecord N sample ops) : Finset (UnrankedTree Copy) :=
  (registeredTraceEndpoint N ops z).elim ∅ (fun s => sourceUnrankedForest (state s) Finset.univ)

lemma forget_registered_trace_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) : Measurable (forgetRegisteredTrace N (sample := sample) ops) :=
  (measurable_of_countable (fun o : Option (Code N sample) =>
    o.elim ∅ (fun s => sourceUnrankedForest (state s) Finset.univ))).comp (registered_endpoint_measurable N ops)

theorem actual_registered_output_forgets (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (ρ : PMF (V → Bool)) :
    ∀ᵐ z ∂registeredTraceLaw N sample r ops ρ,
      forgetOutput (fullReadout N C sample Finset.univ ops z) = forgetRegisteredTrace N ops z := by
  have hm := measurableSet_eq_fun
    (forget_output_measurable.comp (full_readout_measurable N C sample Finset.univ ops))
    (forget_registered_trace_measurable N ops)
  rw [registeredTraceLaw,ae_finsetSum_measure_iff]
  intro reg _
  apply Measure.ae_smul_measure
  apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hm).mpr
  filter_upwards [actual_terminal_readout N r ops (initialCode N sample reg)
    (fun d => joinedProjection N Finset.univ (.inl d)),
    actual_completed_endpoint_some N r ops (initialCode N sample reg)] with z ht he
  change ((terminalPath (chronologicalPath N ops (observeCompleted N
    (fun d => joinedProjection N Finset.univ (.inl d)) ops (initialCode N sample reg) z))).map
      (fun q => unrankedForest q.val)).getD ∅ =
    (completedCalendarEndpoint N ops z).elim ∅ (fun s => sourceUnrankedForest (state s) Finset.univ)
  rw [ht,he]
  rfl

/-- Exact time-forgetting consistency for the natural physical source. -/
theorem actual_natural_timed_output_forgets (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    ((originalTimedTraceLaw N C sample H p common r).map
      (fullReadout N C sample Finset.univ (compiledCalendarProgram N C H (originalGamma p) common))).map forgetOutput =
      (naturalCompletedUnrankedLaw N C sample H p common r).toMeasure := by
  rw [Measure.map_map forget_output_measurable (full_readout_measurable N C sample Finset.univ _)]
  exact (Measure.map_congr (actual_registered_output_forgets N C sample r _ (originalRegisterPMF N p))).trans
    (original_timed_trace_forgets_to_unranked N C sample H p common r)

/-- Exact time-forgetting consistency with the old fixed-ID controlled law. -/
theorem actual_controlled_timed_output_forgets (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) (mask : OriginalMask N) :
    ((controlledTimedTraceLaw N C sample H p common r mask).map
      (fullReadout N C sample Finset.univ (controlledCalendarProgram N C H p common mask))).map forgetOutput =
      (controlledCompletedUnrankedLaw N C sample H p common r mask).toMeasure := by
  rw [Measure.map_map forget_output_measurable (full_readout_measurable N C sample Finset.univ _)]
  exact (Measure.map_congr (actual_registered_output_forgets N C sample r _ (originalRegisterPMF N p))).trans
    (controlled_timed_trace_forgets_to_unranked N C sample H p common r mask)

#print axioms actual_natural_timed_output_forgets
#print axioms actual_controlled_timed_output_forgets
end GProgram.G2.TimedOutputForgetting
