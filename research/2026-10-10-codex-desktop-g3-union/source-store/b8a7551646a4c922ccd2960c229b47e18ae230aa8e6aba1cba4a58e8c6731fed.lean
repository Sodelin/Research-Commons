import G5TwoCutSourceWord
import UnifiedLean.Source.SourceInitializedCalendar

/-! The constructed two-cut word consumes the existing original initialized
whole-calendar completion law. dot / OpenAI,9 October2026. -/
namespace GProgram.G5.TwoCutCompletedSource
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.ActualCalendarTrace GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.CompleteDecoration GProgram.G2.ChronologicalPathReadout
open GProgram.G2.SourceFiniteHistory
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualObservationCutRefinement
open CloudG3.ActualCalendarCutContext CloudG3.CompleteCalendarJointLaw
open CloudG3.CompleteCalendarBinReadout CloudG3.ActualTailBinRow
open GProgram.G5.TwoCutSourceWord
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

theorem actual_initialized_two_cut_completed_law (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (reg : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (hwhole : compiledCalendarProgram N C H gamma common = pre ++ .interval (a+(b+c)) :: post)
    (M : Copy → Copy → ℝ) :
    let ops := pre ++ .interval (a+(b+c)) :: post
    let s := initialCode N sample reg
    let offset := firstOriginalDate N C
    let left := offset + (programDuration N pre : ℝ) + (a:ℝ)
    let right := left + (b:ℝ)
    (completeCalendarTraceLaw N r ops s).map
      (fun z => (completeEnd N ops z,
        completeTags N (twoCutBin left right) ops s offset
          (fun x y => twoCutBin left right (M x y)) z)) =
      (((sourceHistoryLaw N r (physicalOps N (twoCutWord N pre post a b c)) s).map
        (endpointHistoryReadout N (twoCutWord N pre post a b c) s
          (fun x y => twoCutBin left right (M x y)))).bind
        (jointTailKernel N r (2 : Fin 3))).toMeasure := by
  dsimp only
  have hroot : ∀ d ∈ (sourceProgram N r (pre ++ .interval (a+(b+c)) :: post)
      (initialCode N sample reg)).support, AncestralRoot N d := by
    rw [←hwhole]
    intro d hd
    exact initialized_original_calendar_ancestral_support N C sample reg H gamma common r hd
  have hoff : firstOriginalDate N C + (programDuration N pre : ℝ) + (a:ℝ) + (b:ℝ) ≤
      firstOriginalDate N C + (programDuration N (pre ++ .interval (a+(b+c)) :: post) : ℝ) := by
    simp only [program_duration_append,programDuration,NNReal.coe_add]
    have hc := c.coe_nonneg
    have hp := (programDuration N post).coe_nonneg
    linarith
  rw [actual_complete_joint_source_law N r _ (two_cut_bin_measurable _ _) _ _ hroot _ _ (2 : Fin 3) hoff]
  · rw [actual_two_cut_source_joint]
  · intro x hx
    have hh : firstOriginalDate N C + (programDuration N pre : ℝ) + (a:ℝ) < x := by
      have hb := b.coe_nonneg
      linarith
    simp [twoCutBin,not_le_of_gt hh,not_le_of_gt hx]

#print axioms actual_initialized_two_cut_completed_law
end GProgram.G5.TwoCutCompletedSource
