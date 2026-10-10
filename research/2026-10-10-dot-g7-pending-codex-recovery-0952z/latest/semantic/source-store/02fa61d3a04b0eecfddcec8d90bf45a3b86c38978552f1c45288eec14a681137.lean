import G7CalendarAgendaRelabelling

/-! Exact relabelling of the actually generated original calendar endpoint law,
including its once-drawn original register. Contributor: dot,2026-10-09.
Tied boundaries use separately proved phase-wise commutation. No calendar law
or source likelihood equality is assumed. -/
namespace GProgram.G7.NaturalCalendarRelabelling
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.OriginalRelabelling GProgram.G7.CalendarNodeRelabelling
open GProgram.G7.CalendarAgendaRelabelling GProgram.G7.ProgramRelabelling
open GProgram.G7.SnapshotRelabelling GProgram.G7.NaturalWordRelabelling
open GProgram.G7.BoundaryPhasePermutation
open scoped Classical
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]

theorem tail_agenda (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (g : Hybrid N → unitInterval)
    (c : Hybrid N → Bool) (r : PositivePairRates F) (a : ℝ) (ds : List ℝ)
    {sample : Copy → X} (s : Code (network N v e) sample) :
    sourceProgram (network N v e) r
      ((calendarTail N C H g c a ds).map (programStep N v e)) s =
    sourceProgram (network N v e) r
      (calendarTail (network N v e) (calendar N v e C) (registry N v e H)
        (gamma N v e g) (common N v e c) a ds) s := by
  induction ds generalizing a s with
  | nil => rfl
  | cons b bs ih =>
    simp only [calendarTail,List.map_cons,List.map_append,programStep,sourceProgram]
    congr 1
    funext d
    rw [program_append,program_append,boundary_agenda]
    congr 1
    funext z
    exact ih b z

theorem compiled_agenda (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (g : Hybrid N → unitInterval)
    (c : Hybrid N → Bool) (r : PositivePairRates F)
    {sample : Copy → X} (s : Code (network N v e) sample) :
    sourceProgram (network N v e) r
      ((compiledCalendarProgram N C H g c).map (programStep N v e)) s =
    sourceProgram (network N v e) r
      (compiledCalendarProgram (network N v e) (calendar N v e C) (registry N v e H)
        (gamma N v e g) (common N v e c)) s := by
  unfold compiledCalendarProgram
  rw [sorted_dates]
  cases h : sortedOriginalDates N C with
  | nil => rfl
  | cons a ds =>
    simp only [List.map_append]
    rw [program_append,program_append,boundary_agenda]
    congr 1
    funext d
    exact tail_agenda N v e C H g c r a ds d

theorem conditional_calendar (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (g : Hybrid N → unitInterval)
    (c : Hybrid N → Bool) (r : PositivePairRates E)
    {sample : Copy → X} (s : Code N sample) :
    (sourceProgram N r (compiledCalendarProgram N C H g c) s).map (code N v e) =
    sourceProgram (network N v e) (rates e r)
      (compiledCalendarProgram (network N v e) (calendar N v e C) (registry N v e H)
        (gamma N v e g) (common N v e c)) (code N v e s) := by
  rw [program,compiled_agenda]

/-- Actual natural original-calendar endpoint PMF; the original shared physical
bank and once-drawn latent register are transported together across every row. -/
theorem natural_calendar (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (c : Hybrid N → Bool) (r : PositivePairRates E) :
    (naturalCalendarLaw N C sample H p c r).map (code N v e) =
      naturalCalendarLaw (network N v e) (calendar N v e C) sample (registry N v e H)
        (inheritance N v e p) (common N v e c) (rates e r) := by
  unfold naturalCalendarLaw
  rw [initialized_word]
  congr 1
  funext reg
  exact compiled_agenda N v e C H (originalGamma p) c (rates e r) _

#print axioms compiled_agenda
#print axioms conditional_calendar
#print axioms natural_calendar
end GProgram.G7.NaturalCalendarRelabelling
