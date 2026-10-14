import G1OriginalCompletedForestReconstruction
import G1OriginalCalendarDecomposition

/-! Actual initialized-calendar/root support for the completed K-only future
is derived from the literal original compiler decomposition.
Contributor: dot, 2026-10-03. No ancestral-support field is assumed. -/
namespace G1CanonicalCompletedFutureRootAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion
open G1ActualTwoPortBlob G1InitializedFrontierPrefix G1CanonicalComponentSegment
open G1OriginalCalendarDecomposition G1SameOriginalExteriorContinuation
open scoped Classical
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Every REAL original initialized frontier/phase support state, followed by
the SAME actual original future (including remaining A0 exits/node operations),
reaches the original ancestral population for ALL original copies. -/
theorem actual_canonical_completed_future_root_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    {s : Code N sample}
    (hs : s ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
      (initialCode N sample register)).support)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r (componentAgenda N C b A H gamma common) s).support)
    {z : Code N sample} (hz : z ∈ (sourceProgram N r (originalFuture N C b A H gamma common) d).support) :
    AncestralRoot N z := by
  have hfull : z ∈ (sourceProgram N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register)).support := by
    rw [actual_full_calendar_component_decomposition N C b A H gamma common,
      List.append_assoc,actual_source_program_append]
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨s,hs,?_⟩
    rw [actual_source_program_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨d,hd,hz⟩
  exact initialized_original_calendar_ancestral_support N C sample register H gamma common r hfull

#print axioms actual_canonical_completed_future_root_support
end G1CanonicalCompletedFutureRootAdmission
