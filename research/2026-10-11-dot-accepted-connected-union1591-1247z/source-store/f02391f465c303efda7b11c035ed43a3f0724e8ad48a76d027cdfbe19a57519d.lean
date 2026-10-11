import G2CompleteCalendarAttachment
import UnifiedLean.Source.ControlledUnrankedSourceProjectivity

/-!
Once-drawn original registers and the actual completed calendar records.
Contributor: dot (OpenAI), 7 October 2026. The original fixed-ID controls alter
only their admitted programme and retain the original register distribution.
Time-forgetting is derived from the actual random-cover completion law.
-/
namespace GProgram.G2.ControlledTraceAssembly
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.CompleteCalendarAttachment
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable

abbrev RegisteredRecord (N : RootedBinary V E X) (sample : Copy → X)
    (ops : List (ProgramStep N)) := (V → Bool) × CompleteCalendarRecord N sample ops

noncomputable def registeredTraceLaw (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (ρ : PMF (V → Bool)) :
    Measure (RegisteredRecord N sample ops) :=
  ∑ reg : V → Bool, ρ reg •
    (completeCalendarTraceLaw N r ops (initialCode N sample reg)).map (fun z => (reg,z))

noncomputable def registeredTraceEndpoint (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (z : RegisteredRecord N sample ops) : Option (Code N sample) :=
  completedCalendarEndpoint N ops z.2

lemma registered_endpoint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) : Measurable (registeredTraceEndpoint N (sample := sample) ops) :=
  (completed_calendar_endpoint_measurable N ops).comp measurable_snd

lemma registered_trace_probability (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (ρ : PMF (V → Bool)) :
    IsProbabilityMeasure (registeredTraceLaw N sample r ops ρ) := by
  have hm (reg : V → Bool) :
      ((completeCalendarTraceLaw N r ops (initialCode N sample reg)).map (fun z => (reg,z))) univ = 1 := by
    letI := complete_calendar_trace_probability N r ops (initialCode N sample reg)
    have hi : Measurable (fun z : CompleteCalendarRecord N sample ops => (reg,z)) :=
      measurable_const.prodMk measurable_id
    rw [Measure.map_apply hi MeasurableSet.univ,preimage_univ,measure_univ]
  constructor
  rw [registeredTraceLaw,Measure.finsetSum_apply]
  simp only [Measure.smul_apply,smul_eq_mul,hm,mul_one]
  simpa only [tsum_fintype] using PMF.tsum_coe ρ

/-- Finite register assembly helper. The concrete rows below come from the
proved actual completed-clock law, rather than a fitted output kernel. -/
lemma registered_map_of_row_law (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (ρ : PMF (V → Bool))
    {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (F : RegisteredRecord N sample ops → S) (hF : Measurable F)
    (K : (V → Bool) → PMF S)
    (hrow : ∀ reg, (completeCalendarTraceLaw N r ops (initialCode N sample reg)).map
      (fun z => F (reg,z)) = (K reg).toMeasure) :
    (registeredTraceLaw N sample r ops ρ).map F = (ρ.bind K).toMeasure := by
  have he (reg : V → Bool) :
      ((completeCalendarTraceLaw N r ops (initialCode N sample reg)).map (fun z => (reg,z))).map F =
        (K reg).toMeasure := by
    have hi : Measurable (fun z : CompleteCalendarRecord N sample ops => (reg,z)) :=
      measurable_const.prodMk measurable_id
    rw [Measure.map_map hF hi]
    exact hrow reg
  rw [registeredTraceLaw,Measure.map_finset_sum' hF.aemeasurable]
  simp_rw [Measure.map_smul,he]
  apply Measure.ext
  intro A hA
  rw [Measure.finsetSum_apply,PMF.toMeasure_bind_apply _ _ _ hA,tsum_fintype]
  simp only [Measure.smul_apply,smul_eq_mul]

noncomputable def originalTimedTraceLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    Measure (RegisteredRecord N sample (compiledCalendarProgram N C H (originalGamma p) common)) :=
  registeredTraceLaw N sample r (compiledCalendarProgram N C H (originalGamma p) common)
    (originalRegisterPMF N p)

noncomputable def controlledTimedTraceLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (mask : OriginalMask N) :
    Measure (RegisteredRecord N sample (controlledCalendarProgram N C H p common mask)) :=
  registeredTraceLaw N sample r (controlledCalendarProgram N C H p common mask)
    (originalRegisterPMF N p)

noncomputable def registeredForest (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (z : RegisteredRecord N sample ops) : Finset (UnrankedTree Copy) :=
  (registeredTraceEndpoint N ops z).elim ∅ (fun s => sourceUnrankedForest (state s) Finset.univ)

lemma registered_forest_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) : Measurable (registeredForest N (sample := sample) ops) :=
  (measurable_of_countable (fun o : Option (Code N sample) =>
    o.elim ∅ (fun s => sourceUnrankedForest (state s) Finset.univ))).comp
    (registered_endpoint_measurable N ops)

lemma completed_forest_row_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (hs : ∀ d ∈ (sourceProgram N r ops s).support, AncestralRoot N d) :
    (completeCalendarTraceLaw N r ops s).map
      (fun z => (completedCalendarEndpoint N ops z).elim ∅
        (fun d => sourceUnrankedForest (state d) Finset.univ)) =
      (((sourceProgram N r ops s).bind (completionKernel N r)).map
        (fun d => sourceUnrankedForest (state d) Finset.univ)).toMeasure := by
  have ho : Measurable (fun o : Option (Code N sample) =>
      o.elim ∅ (fun d => sourceUnrankedForest (state d) Finset.univ)) := measurable_of_countable _
  change (completeCalendarTraceLaw N r ops s).map
    ((fun o : Option (Code N sample) => o.elim ∅
      (fun d => sourceUnrankedForest (state d) Finset.univ)) ∘ completedCalendarEndpoint N ops) = _
  rw [← Measure.map_map ho (completed_calendar_endpoint_measurable N ops),
    completed_calendar_endpoint_law N r ops s hs,
    Measure.map_map ho (measurable_of_countable (some : Code N sample → Option (Code N sample)))]
  exact PMF.toMeasure_map _ _ (measurable_of_countable _)

/-- The whole original register mixture forgets to its actual old source
calendar/completion PMF, including the empty original copy carrier. -/
theorem registered_trace_forgets_to_unranked (N : RootedBinary V E X)
    (sample : Copy → X) (r : PositivePairRates E) (ops : List (ProgramStep N))
    (ρ : PMF (V → Bool))
    (hs : ∀ reg d, d ∈ (sourceProgram N r ops (initialCode N sample reg)).support → AncestralRoot N d) :
    (registeredTraceLaw N sample r ops ρ).map (registeredForest N ops) =
      (((ρ.bind (fun reg => sourceProgram N r ops (initialCode N sample reg))).bind
        (completionKernel N r)).map (fun d => sourceUnrankedForest (state d) Finset.univ)).toMeasure := by
  have h := registered_map_of_row_law N sample r ops ρ (registeredForest N ops)
    (registered_forest_measurable N ops)
    (fun reg => ((sourceProgram N r ops (initialCode N sample reg)).bind (completionKernel N r)).map
      (fun d => sourceUnrankedForest (state d) Finset.univ))
    (fun reg => completed_forest_row_law N r ops (initialCode N sample reg) (hs reg))
  rw [PMF.bind_bind,PMF.map_bind] 
  exact h

/-- Natural original-source instance with root support supplied by its own
calendar compiler, not by a new admission predicate. -/
theorem original_timed_trace_forgets_to_unranked (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    (originalTimedTraceLaw N C sample H p common r).map
      (registeredForest N (compiledCalendarProgram N C H (originalGamma p) common)) =
      (naturalCompletedUnrankedLaw N C sample H p common r).toMeasure := by
  unfold originalTimedTraceLaw naturalCompletedUnrankedLaw naturalCompletedLaw naturalCalendarLaw
  change (registeredTraceLaw N sample r _ _).map (registeredForest N _) = _
  apply registered_trace_forgets_to_unranked
  intro reg d hd
  exact initialized_original_calendar_ancestral_support N C sample reg H (originalGamma p) common r hd

theorem controlled_timed_trace_forgets_to_unranked (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (mask : OriginalMask N) :
    (controlledTimedTraceLaw N C sample H p common r mask).map
      (registeredForest N (controlledCalendarProgram N C H p common mask)) =
      (controlledCompletedUnrankedLaw N C sample H p common r mask).toMeasure := by
  unfold controlledTimedTraceLaw controlledCompletedUnrankedLaw controlledCompletedLaw controlledCalendarLaw
  apply registered_trace_forgets_to_unranked
  intro reg d hd
  exact initialized_original_calendar_ancestral_support N C sample reg H
    (controlledGamma p mask) (controlledMode common mask) r hd

#print axioms registered_endpoint_measurable
#print axioms registered_trace_probability
#print axioms registered_map_of_row_law
#print axioms registered_forest_measurable
#print axioms completed_forest_row_law
#print axioms registered_trace_forgets_to_unranked
#print axioms original_timed_trace_forgets_to_unranked
#print axioms controlled_timed_trace_forgets_to_unranked
end GProgram.G2.ControlledTraceAssembly
