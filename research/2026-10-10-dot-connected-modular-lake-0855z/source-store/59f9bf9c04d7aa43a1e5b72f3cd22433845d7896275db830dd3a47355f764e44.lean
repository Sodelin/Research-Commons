import G2TimedOutputForgetting

/-!
Explicit full-mass support of the actual timed output on faithful complete
chronological source trees. Empty and singleton carriers are included.
Contributor: dot (OpenAI), 6 October 2026.
-/
namespace GProgram.G2.RootedTimedOutputSupport
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.OriginalFixedIDControls UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.CompleteTimedSupport GProgram.G2.CompleteDecoration
open GProgram.G2.ActualCalendarTrace GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.FiniteAncestralTrace GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.TimedOutputForgetting GProgram.G2.FaithfulTimedOutput
open GProgram.G2.ActualTimedAllPanelLaw GProgram.G2.JointTimedObservation
open GProgram.G2.ControlledTraceAssembly GProgram.G2.ChronologicalPathReadout
open GProgram.G2.RegisteredPathProjection GProgram.G2.CompletedPathProjection
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

lemma actual_original_complete_root_card (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common) (initialCode N sample register),
      liveCard (completeEnd N (compiledCalendarProgram N C H gamma common) z) ≤ 1 := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  have hm : MeasurableSet {z : CompleteCalendarRecord N sample ops | liveCard (completeEnd N ops z) ≤ 1} :=
    ((measurable_of_countable (fun d : Code N sample => liveCard d ≤ 1)).comp (complete_end_measurable N ops)).setOf
  rw [completeCalendarTraceLaw,ae_finsetSum_measure_iff]
  intro d _
  by_cases hd : sourceProgram N r ops s d = 0
  · have hz : (actualCalendarTraceLaw N r ops s).restrict {z | calendarEnd N ops s z = d} = 0 :=
      Measure.restrict_eq_zero.mpr ((calendar_end_fibre_mass N r ops s d).trans hd)
    dsimp only [ops,s] at hz
    simp [hz]
  · have hr := initialized_original_calendar_ancestral_support N C sample register H gamma common r
      ((PMF.mem_support_iff _ _).mpr hd)
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
    obtain ⟨e,he,_,hcard⟩ := complete_ancestral_trace_terminal N d c hr hc
    have hg := marked_trace_success_on_regular N (Fintype.card Copy) d (clockCover N d c : ℝ)
      c (Finset.card_le_univ d.val.live) hc
    have he' : traceEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d c).2 = e := by
      simpa only [decodedEndpoint,completeAncestralTrace,hg,if_true,Option.some.injEq] using he
    change liveCard (traceEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d c).2) ≤ 1
    rw [he']
    exact hcard

/-- A valid source carrier witnesses the complete rooted shape; the same
observed matrix faithfully decorates every actual live genealogy with strict
parent/child ages and the original leaf dates. -/
noncomputable def RootedTimedOutput (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (o : TimedObservation Copy) : Prop :=
  ∃ s : Code N sample, liveCard s ≤ 1 ∧
    o.1 = some (sourceUnrankedForest (state s) Finset.univ) ∧
    (∀ x y, (o.2 x y).1 = true) ∧
    HasTimedBound (fun x => C.age (N.leaf (sample x))) (fun x y => (o.2 x y).2) (state s)

lemma rooted_timed_output_measurable (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) : MeasurableSet {o | RootedTimedOutput N C sample o} := by
  apply Measurable.setOf
  apply Measurable.exists
  intro s
  apply Measurable.and measurable_const
  apply Measurable.and (measurable_fst.eq measurable_const)
  apply Measurable.and
  · apply Measurable.forall
    intro x
    apply Measurable.forall
    intro y
    exact (((measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_snd)).fst).eq measurable_const
  · have hm : Measurable (fun o : TimedObservation Copy => fun x y => (o.2 x y).2) := by
      apply measurable_pi_lambda
      intro x
      apply measurable_pi_lambda
      intro y
      exact ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_snd)).snd
    exact (has_timed_bound_joint_measurable N (fun x => C.age (N.leaf (sample x)))).comp
      (measurable_const.prodMk hm)

/-- Full-mass faithful rooted chronological support on the actual initialized
physical source, without conditioning away failures or empty panels. -/
theorem actual_registered_rooted_timed_support (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (ρ : PMF (V → Bool)) :
    ∀ᵐ o ∂(registeredTraceLaw N sample r (compiledCalendarProgram N C H gamma common) ρ).map
      (fullReadout N C sample Finset.univ (compiledCalendarProgram N C H gamma common)),
      RootedTimedOutput N C sample o.2 := by
  let ops := compiledCalendarProgram N C H gamma common
  have hm : MeasurableSet {o : (V → Bool) × TimedObservation Copy | RootedTimedOutput N C sample o.2} :=
    (rooted_timed_output_measurable N C sample).preimage measurable_snd
  apply (ae_map_iff (full_readout_measurable N C sample Finset.univ ops).aemeasurable hm).mpr
  have hev := hm.preimage (full_readout_measurable N C sample Finset.univ ops)
  rw [registeredTraceLaw,ae_finsetSum_measure_iff]
  intro reg _
  apply Measure.ae_smul_measure
  apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hev).mpr
  filter_upwards [actual_original_faithful_output N C sample reg H gamma common r Finset.univ,
    actual_original_complete_root_card N C sample reg H gamma common r,
    actual_original_complete_timed_support N C sample reg H gamma common r] with z ho hr ht
  change RootedTimedOutput N C sample (timedObservation N C sample Finset.univ
    (chronologicalPath N ops (observeCompleted N _ ops (initialCode N sample reg) z)))
  change RootedTimedOutput N C sample (timedObservation N C sample Finset.univ
    (chronologicalPath N (compiledCalendarProgram N C H gamma common) (observeCompleted N _ _ _ z)))
  rw [ho]
  refine ⟨completeEnd N ops z,hr,rfl,?_,?_⟩
  · intro x y
    simp [matrixObservation]
  · simpa only [matrixObservation,Finset.mem_univ,and_self,if_true,Set.mem_setOf_eq,ops] using ht

#print axioms actual_registered_rooted_timed_support
end GProgram.G2.RootedTimedOutputSupport
