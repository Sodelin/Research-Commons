import G2CalendarFirstAge
import G2RegisteredPathProjection

/-!
Original calendar offset for the proved same-record numerical age interface.
Contributor: dot (OpenAI), 7 October 2026.
This module joins the accepted numerical reader and registered path-law
interfaces needed by the unchanged joint-observation consumer. The result
is a specialization of the numerical theorem, not a new desired-law premise.
-/
namespace GProgram.G2.OriginalAbsoluteAges
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open GProgram.G2.CalendarFirstAge GProgram.G2.AncestralAgeCertificate
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompleteDecoration
open GProgram.G2.ActualPairCoalescence GProgram.G2.RationalAgeReadout
open scoped ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Physical absolute ages use the unchanged original initial calendar date.
The actual support certificate and initial separation are explicit. -/
theorem complete_age_at_original_offset (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (M : Copy → Copy → ℝ)
    (z : CompleteCalendarRecord N sample ops) (x y : Copy)
    (hz : CompleteAgeCertificate N
      (fun d => sameBlock (selectedView (state d) Finset.univ) x y) ops s z)
    (hs : ¬ sameBlock (selectedView (state s) Finset.univ) x y) :
    ∃ a : ℝ, 0 ≤ a ∧
      completeMatrix N ops s (firstOriginalDate N C) M z x y = firstOriginalDate N C+a ∧
      rationalAge (fun d => sameBlock (selectedView (state d) Finset.univ) x y)
        (recordPath N ops s z.2.1 z.2.2.2) = ENNReal.ofReal a :=
  complete_matrix_first_age N ops s (firstOriginalDate N C) M z x y hz hs

#print axioms complete_age_at_original_offset
end GProgram.G2.OriginalAbsoluteAges
