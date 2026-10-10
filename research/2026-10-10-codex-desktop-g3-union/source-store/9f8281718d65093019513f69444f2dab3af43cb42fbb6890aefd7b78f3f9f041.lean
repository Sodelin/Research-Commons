import G1CanonicalOriginalDateGapRoles

/-! Actual adjacent ORIGINAL epochs connect the real source admissions used
by the runtime boundary batches. These are literal prefix decompositions and
source-support conclusions, with original durations/rates unchanged. -/
namespace G1CanonicalOriginalAdjacentSourceSupport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1InitializedFrontierPrefix G1CanonicalComponentSegment
open G1CanonicalThreeEpochList G1CanonicalOriginalDateGapRoles G1ActualBeforeExitActorSupport
open G1SameOriginalExteriorContinuation G1OriginalCalendarDecomposition
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- No original boundary is skipped or duplicated between adjacent dates. -/
theorem actual_before_adjacent_original_date_append (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (first next : O.Vertex) (hlt : O.calendar.age first < O.calendar.age next) (later : List ℝ)
    (heq : afterDate O.network O.calendar (O.calendar.age first) = O.calendar.age next :: later) :
    beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age next) =
      beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age first) ++
      boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age first) ++
      [.interval (Real.toNNReal (O.calendar.age next - O.calendar.age first))] := by
  rw [actual_before_boundary_window_append O H gamma common first next hlt,heq]
  simp only [stopBeforeTail,ite_true,actualFrontierProgram,boundaryOperations,nodeOperations,List.append_assoc]

/-- Canonical adjacent epoch input/output states belong to the exact genuine
initialized original prefixes used in the next boundary batch theorem. -/
theorem actual_adjacent_original_epoch_reaches_real_prefix (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (first next : O.Vertex) (hlt : O.calendar.age first < O.calendar.age next) (later : List ℝ)
    (heq : afterDate O.network O.calendar (O.calendar.age first) = O.calendar.age next :: later)
    {s d z : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age first))
      (initialCode O.network sample register)).support)
    (hd : d ∈ (sourceProgram O.network r
      (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age first)) s).support)
    (hz : z ∈ (sourceProgram O.network r
      [.interval (Real.toNNReal (O.calendar.age next - O.calendar.age first))] d).support) :
    z ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age next))
      (initialCode O.network sample register)).support := by
  rw [actual_before_adjacent_original_date_append O H gamma common first next hlt later heq,
    actual_source_program_append,actual_source_program_append]
  exact (PMF.mem_support_bind_iff _ _ _).mpr
    ⟨d,(PMF.mem_support_bind_iff _ _ _).mpr ⟨s,hs,hd⟩,hz⟩

#print axioms actual_adjacent_original_epoch_reaches_real_prefix
end G1CanonicalOriginalAdjacentSourceSupport
