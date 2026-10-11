import G7CompletedUnrankedRelabelling
import G2CompleteCalendarAttachment

/-! Readout composition of the inherited actual complete-clock attachment.
This adds no clock model or completion assumption. Contributor: dot,2026-10-09.
-/
namespace GProgram.G7.ActualClockUnrankedRelabelling
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.LiteralMarkedClockTrace
open GProgram.G7.OriginalRelabelling GProgram.G7.CalendarNodeRelabelling
open GProgram.G7.CompletedUnrankedRelabelling
open scoped Classical BigOperators ENNReal
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]
attribute [local instance] codeMeasurable codeOptionMeasurable

/-- A finite readout composition of the existing actual complete trace endpoint
law. The sole source support gate is already discharged by the inherited
original-calendar theorem. -/
theorem conditional_readout {O : Type*} [MeasurableSpace (Option O)]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (reg : V → Bool) (H : OriginalParentRegistry N) (g : Hybrid N → unitInterval)
    (c : Hybrid N → Bool) (r : PositivePairRates E) (read : Code N sample → O) :
    (completeCalendarTraceLaw N r (compiledCalendarProgram N C H g c)
      (initialCode N sample reg)).map
      (Option.map read ∘ completedCalendarEndpoint N (compiledCalendarProgram N C H g c)) =
    (((sourceProgram N r (compiledCalendarProgram N C H g c) (initialCode N sample reg)).bind
      (completionKernel N r)).map (fun d => some (read d))).toMeasure := by
  have hm : Measurable (Option.map read : Option (Code N sample) → Option O) := measurable_of_countable _
  have hs : Measurable (some : Code N sample → Option (Code N sample)) := measurable_of_countable _
  rw [← Measure.map_map hm (completed_calendar_endpoint_measurable N _),
    original_completed_calendar_endpoint_law,Measure.map_map hm hs]
  exact PMF.toMeasure_map (fun d => some (read d)) _ (measurable_of_countable _)

noncomputable def forestMeasurable : MeasurableSpace (Option (Finset (UnrankedTree Copy))) := ⊤
attribute [local instance] forestMeasurable

/-- The inherited complete original clock trace, mixed by the inherited
once-drawn original register, then forgetting times and reading its final
unranked genealogy. None is retained as the source endpoint-failure symbol. -/
noncomputable def actualClockUnrankedLaw (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (c : Hybrid N → Bool) (r : PositivePairRates E) :
    Measure (Option (Finset (UnrankedTree Copy))) :=
  ∑ reg : V → Bool, originalRegisterPMF N p reg •
    (completeCalendarTraceLaw N r (compiledCalendarProgram N C H (originalGamma p) c)
      (initialCode N sample reg)).map
      (Option.map (fun d => sourceUnrankedForest (state d) Finset.univ) ∘
        completedCalendarEndpoint N (compiledCalendarProgram N C H (originalGamma p) c))

theorem actual_clock_eq_unranked (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (c : Hybrid N → Bool) (r : PositivePairRates E) :
    actualClockUnrankedLaw N C sample H p c r =
      ((naturalCompletedUnrankedLaw N C sample H p c r).map some).toMeasure := by
  unfold actualClockUnrankedLaw naturalCompletedUnrankedLaw naturalCompletedLaw naturalCalendarLaw
  rw [PMF.map_comp,PMF.bind_bind,PMF.map_bind]
  simp_rw [conditional_readout]
  apply Measure.ext
  intro S hS
  rw [PMF.toMeasure_bind_apply _ _ _ hS,tsum_fintype,Measure.finsetSum_apply]
  simp only [Measure.smul_apply,smul_eq_mul]
  rfl

/-- Actual complete-clock UNRANKED endpoint observation is invariant under
original graph relabelling. No full timed-path equality is asserted. -/
theorem actual_clock_unranked_relabel (N : RootedBinary V E X)
    (v : V ≃ W) (e : E ≃ F) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (c : Hybrid N → Bool) (r : PositivePairRates E) :
    actualClockUnrankedLaw N C sample H p c r =
      actualClockUnrankedLaw (network N v e) (calendar N v e C) sample (registry N v e H)
        (inheritance N v e p) (common N v e c) (rates e r) := by
  rw [actual_clock_eq_unranked,actual_clock_eq_unranked,
    natural_completed_unranked N v e C sample H p c r]

#print axioms conditional_readout
#print axioms actual_clock_eq_unranked
#print axioms actual_clock_unranked_relabel
end GProgram.G7.ActualClockUnrankedRelabelling
