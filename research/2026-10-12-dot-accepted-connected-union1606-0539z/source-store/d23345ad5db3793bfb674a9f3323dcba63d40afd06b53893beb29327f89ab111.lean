import G1OriginalSpanClosingSourceRow

/-! Exact original full compiler = initialized frontier ++ precise closing
span phase ++ SAME original future. Contributor: dot, 2026-10-03. -/
namespace G1OriginalClosingCalendarBinding
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1OriginalSpanClosingPhase G1OriginalSpanCalendarDecomposition
open G1CanonicalThreeEpochList G1CanonicalComponentSegment G1CanonicalEpochSpecialization
open G1OriginalCalendarDecomposition G1InitializedFrontierPrefix
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalClosingFuture (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (edge : O.Edge) : List (ProgramStep O.network) :=
  ((originalExits O.network O.calendar (O.calendar.age (O.network.graph.source edge))).dropWhile
    (fun f => decide (f ≠ edge))).tail.map (fun e => .boundary (.exit e)) ++
    nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
      (O.calendar.age (O.network.graph.source edge)) ++
    calendarTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
      (O.calendar.age (O.network.graph.source edge)) (afterDate O.network O.calendar (O.calendar.age (O.network.graph.source edge)))

/-- The unmodified original compiler has this literal decomposition. No
program/source-law equality is supplied as an input. -/
theorem actual_original_closing_calendar_decomposition (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (a b : O.Vertex) (edge : O.Edge) (hb : O.network.graph.source edge = b)
    (hab : O.calendar.age a < O.calendar.age b) :
    compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) =
      actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age a) ++
        closingSpanAgenda O H gamma common a b edge ++ originalClosingFuture O H gamma common edge := by
  have hstart := actual_compiled_calendar_date_cut O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
    (O.calendar.age a) (original_date_scheduled O.network O.calendar a)
  have htail := actual_calendar_tail_cut O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
    (afterDate O.network O.calendar (O.calendar.age a)) (original_after_ordered _ _ _)
    (O.calendar.age b) (original_after_member _ _ _ b hab) (O.calendar.age a)
  have hf : (afterDate O.network O.calendar (O.calendar.age a)).filter (fun t => decide (O.calendar.age b < t)) =
      afterDate O.network O.calendar (O.calendar.age b) := filter_after_filter hab _
  rw [hf] at htail
  have he : edge ∈ originalExits O.network O.calendar (O.calendar.age b) :=
    Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg O.calendar.age hb⟩)
  have hexits := original_exit_list_cut (originalExits O.network O.calendar (O.calendar.age b)) edge he
  have hmaps := congrArg (fun es => es.map (fun e : O.Edge => (ProgramStep.boundary (.exit e) : ProgramStep O.network))) hexits
  rw [List.map_append,List.map_append,List.map_singleton] at hmaps
  unfold afterDate at htail
  rw [hstart,htail]
  unfold actualFrontierProgram closingSpanAgenda canonicalEpochBlock closingExits originalClosingFuture
  rw [hb]
  have hbatch (d : ℝ) : boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) d =
      (originalExits O.network O.calendar d).map (fun e => .boundary (.exit e)) ++
      nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) d := rfl
  rw [hbatch,hbatch]
  conv_lhs => rw [hmaps]
  simp only [afterDate,originalExits,List.map_append,List.map_singleton,List.append_assoc]

end G1OriginalClosingCalendarBinding
