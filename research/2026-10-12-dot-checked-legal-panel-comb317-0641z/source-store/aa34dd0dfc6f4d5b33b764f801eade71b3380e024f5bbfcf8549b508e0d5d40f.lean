import G2ActualCalendarTrace
import G2AncestralTraceSourceLaw
import UnifiedLean.Source.SourceInitializedCalendar
import UnifiedLean.Source.UnrankedGenealogyObservation

/-!
Actual finite calendar records with their same-source random-cover ancestral
trace attached on the exact terminal-state fibre. Contributor: dot (OpenAI),
6 October 2026. This new reconstruction derives the completed endpoint law;
it does not assert the later physical all-time or timed observation transport.
-/
namespace GProgram.G2.CompleteCalendarAttachment
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.LiteralEpochLaw
open UnifiedLean.Source.SourceCompletionHarmonic
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.FiniteAncestralTrace GProgram.G2.AncestralTraceSourceLaw
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

/-- Discrete observation sigma algebra on the countable unranked forest type. -/
noncomputable def unrankedForestMeasurable : MeasurableSpace (Finset (UnrankedTree Copy)) := ⊤

abbrev CompleteCalendarRecord (N : RootedBinary V E X) (sample : Copy → X)
    (ops : List (ProgramStep N)) :=
  Code N sample × ((Fin ops.length → SegmentRecord N sample) ×
    (Bool × ClockTrace N sample (Fintype.card Copy)))

noncomputable def completeCalendarTraceLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    Measure (CompleteCalendarRecord N sample ops) :=
  ∑ d : Code N sample,
    (((actualCalendarTraceLaw N r ops s).restrict {z | calendarEnd N ops s z = d}).prod
      (completeAncestralTraceLaw N r d)).map (fun z => (d,z))

noncomputable def completedCalendarEndpoint (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (z : CompleteCalendarRecord N sample ops) :
    Option (Code N sample) := decodedEndpoint N (Fintype.card Copy) z.1 z.2.2

lemma completed_calendar_endpoint_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (ops : List (ProgramStep N)) :
    Measurable (completedCalendarEndpoint N (sample := sample) ops) := by
  have hm : Measurable (fun z : Code N sample ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) =>
      decodedEndpoint N (Fintype.card Copy) z.1 z.2) :=
    measurable_from_prod_countable_right (fun d => decoded_endpoint_measurable N _ d)
  exact hm.comp (measurable_fst.prodMk measurable_snd.snd)

/-- The ancestral measure is a probability before any root-support hypothesis;
the calendar fibres retain their original, generally unnormalized masses. -/
theorem complete_calendar_trace_probability (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (s : Code N sample) : IsProbabilityMeasure (completeCalendarTraceLaw N r ops s) := by
  letI := actual_calendar_trace_probability N r ops s
  have he (d : Code N sample) :
      (((((actualCalendarTraceLaw N r ops s).restrict {z | calendarEnd N ops s z = d}).prod
        (completeAncestralTraceLaw N r d)).map (fun z => (d,z))) univ) =
      sourceProgram N r ops s d := by
    letI := complete_ancestral_trace_probability N r d
    have ht : (completeAncestralTraceLaw N r d) univ = 1 := measure_univ
    have hmap : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
        (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) :=
      measurable_const.prodMk measurable_id
    rw [Measure.map_apply hmap MeasurableSet.univ,
      preimage_univ,← univ_prod_univ,Measure.prod_prod,ht,mul_one,
      Measure.restrict_apply MeasurableSet.univ,univ_inter,calendar_end_fibre_mass]
  constructor
  calc
    (completeCalendarTraceLaw N r ops s) univ =
        ∑ d : Code N sample, sourceProgram N r ops s d := by
      rw [completeCalendarTraceLaw,Measure.finsetSum_apply]
      exact Finset.sum_congr rfl (fun d _ => he d)
    _ = 1 := by simpa only [tsum_fintype] using PMF.tsum_coe (sourceProgram N r ops s)

/-- Direct pushforward of one actual terminal fibre and its actual tail. -/
theorem complete_branch_endpoint_map (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s d : Code N sample) :
    (((((actualCalendarTraceLaw N r ops s).restrict {z | calendarEnd N ops s z = d}).prod
      (completeAncestralTraceLaw N r d)).map (fun z => (d,z))).map
        (completedCalendarEndpoint N ops)) =
      sourceProgram N r ops s d •
        ((completeAncestralTraceLaw N r d).map (decodedEndpoint N (Fintype.card Copy) d)) := by
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have hmap : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) :=
    measurable_const.prodMk measurable_id
  rw [Measure.map_map (completed_calendar_endpoint_measurable N ops) hmap]
  change ((((actualCalendarTraceLaw N r ops s).restrict {z | calendarEnd N ops s z = d}).prod
    (completeAncestralTraceLaw N r d)).map ((decodedEndpoint N (Fintype.card Copy) d) ∘ Prod.snd)) = _
  rw [← Measure.map_map (decoded_endpoint_measurable N _ d) measurable_snd,
    Measure.map_snd_prod,Measure.map_smul,Measure.restrict_apply MeasurableSet.univ,
    univ_inter,calendar_end_fibre_mass]

/-- The source-support premise concerns actual root location only. The
completion PMF equality itself is derived from the proved random-cover law. -/
theorem completed_calendar_endpoint_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (hs : ∀ d ∈ (sourceProgram N r ops s).support, AncestralRoot N d) :
    (completeCalendarTraceLaw N r ops s).map (completedCalendarEndpoint N ops) =
      ((sourceProgram N r ops s).bind (completionKernel N r)).toMeasure.map some := by
  rw [completeCalendarTraceLaw,
    Measure.map_finset_sum' (completed_calendar_endpoint_measurable N ops).aemeasurable]
  simp_rw [complete_branch_endpoint_map]
  have he (d : Code N sample) : sourceProgram N r ops s d •
      ((completeAncestralTraceLaw N r d).map (decodedEndpoint N (Fintype.card Copy) d)) =
      sourceProgram N r ops s d • ((completionKernel N r d).toMeasure.map some) := by
    by_cases hd : sourceProgram N r ops s d = 0
    · simp [hd]
    · rw [complete_ancestral_endpoint_source_law N r d (hs d ((PMF.mem_support_iff _ _).mpr hd))]
  simp_rw [he]
  have hsome : Measurable (some : Code N sample → Option (Code N sample)) :=
    measurable_of_countable _
  apply Measure.ext
  intro A hA
  rw [Measure.finsetSum_apply,Measure.map_apply hsome hA,
    PMF.toMeasure_bind_apply _ _ _ (hsome hA),tsum_fintype]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.map_apply hsome hA]

/-- The original calendar supplies the required root support from its own
routing theorem, with original register, source and boundary programme. -/
theorem original_completed_calendar_endpoint_law (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    (completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register)).map
      (completedCalendarEndpoint N (compiledCalendarProgram N C H gamma common)) =
      ((sourceProgram N r (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register)).bind (completionKernel N r)).toMeasure.map some := by
  apply completed_calendar_endpoint_law
  intro d hd
  exact initialized_original_calendar_ancestral_support N C sample register H gamma common r hd

#print axioms completed_calendar_endpoint_measurable
#print axioms complete_calendar_trace_probability
#print axioms complete_branch_endpoint_map
#print axioms completed_calendar_endpoint_law
#print axioms original_completed_calendar_endpoint_law
end GProgram.G2.CompleteCalendarAttachment
