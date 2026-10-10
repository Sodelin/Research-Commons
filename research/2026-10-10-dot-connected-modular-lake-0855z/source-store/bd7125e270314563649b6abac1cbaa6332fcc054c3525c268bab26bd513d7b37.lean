import G5TwoCutCompletedSource
import UnifiedLean.Source.SourceEpochSemigroup

namespace GProgram.G5.TwoCutProgramSupport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceEpochSemigroup UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem original_two_cut_program_eq (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (s : Code N sample) :
    sourceProgram N r (pre ++ .interval (a+(b+c)) :: post) s =
      sourceProgram N r (pre ++ .interval a :: .interval b :: .interval c :: post) s := by
  rw [sourceProgram_append,sourceProgram_append]
  congr 1
  funext d
  simp only [sourceProgram,sourceProgramStep]
  rw [actual_source_time_add N r a (b+c),PMF.bind_bind]
  congr 1
  funext e
  rw [actual_source_time_add N r b c,PMF.bind_bind]

/-- Every supported three-phase branch of the subdivided actual calendar
enters genuine ancestral completion. No branch-wise root-support oracle. -/
theorem actual_three_phase_ancestral_support (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (reg : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (hwhole : compiledCalendarProgram N C H gamma common = pre ++ .interval (a+(b+c)) :: post)
    (d e f : Code N sample)
    (hd : d ∈ (sourceProgram N r (pre ++ [.interval a]) (initialCode N sample reg)).support)
    (he : e ∈ (sourceProgram N r [.interval b] d).support)
    (hf : f ∈ (sourceProgram N r (.interval c :: post) e).support) : AncestralRoot N f := by
  have hs : f ∈ (sourceProgram N r
      ((pre ++ [.interval a]) ++ ([.interval b] ++ (.interval c :: post)))
      (initialCode N sample reg)).support := by
    rw [sourceProgram_append]
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨d,hd,?_⟩
    rw [sourceProgram_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨e,he,hf⟩
  have hs' : f ∈ (sourceProgram N r
      (pre ++ .interval a :: .interval b :: .interval c :: post)
      (initialCode N sample reg)).support := by simpa [List.append_assoc] using hs
  rw [←original_two_cut_program_eq N r pre post a b c,←hwhole] at hs'
  exact initialized_original_calendar_ancestral_support N C sample reg H gamma common r hs'

#print axioms original_two_cut_program_eq
#print axioms actual_three_phase_ancestral_support
end GProgram.G5.TwoCutProgramSupport
