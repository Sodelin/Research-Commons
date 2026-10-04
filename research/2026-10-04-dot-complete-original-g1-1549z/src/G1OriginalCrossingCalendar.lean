import G1ActiveCoreBridgeCohorts

/-! Exact three original chronological windows for crossing bridge actors.
No exterior time is duplicated, and partial same-date exits stay in the SAME
original future. Contributor: dot, 2026-10-03. -/
namespace G1OriginalCrossingCalendar
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1OriginalSpanCalendarDecomposition G1OriginalSpanClosingPhase
open G1OriginalClosingCalendarBinding G1CanonicalEpochSpecialization G1OriginalCalendarDecomposition
open G1InitializedFrontierPrefix G1CanonicalThreeEpochList G1CanonicalComponentSegment
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def remainingClosingExits (O : Source X) (edge : O.Edge) : List (ProgramStep O.network) :=
  ((originalExits O.network O.calendar (O.calendar.age (O.network.graph.source edge))).dropWhile
    (fun f => decide (f ≠ edge))).tail.map (fun e => .boundary (.exit e))

lemma actual_full_batch_span_closing_cut (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (a b : O.Vertex) (edge : O.Edge)
    (hb : O.network.graph.source edge = b) :
    fullSpanAgenda O.network O.calendar H gamma common a b =
      closingSpanAgenda O H gamma common a b edge ++ remainingClosingExits O edge := by
  have he : edge ∈ originalExits O.network O.calendar (O.calendar.age b) :=
    Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg O.calendar.age hb⟩)
  have hcut := original_exit_list_cut (originalExits O.network O.calendar (O.calendar.age b)) edge he
  have hm := congrArg (fun es => es.map (fun e : O.Edge => (ProgramStep.boundary (.exit e) : ProgramStep O.network))) hcut
  simp only [List.map_append,List.map_singleton] at hm
  unfold fullSpanAgenda closingSpanAgenda canonicalEpochBlock closingExits remainingClosingExits
  rw [hb]
  conv_lhs => rw [hm]
  simp only [List.map_append,List.map_singleton,List.append_assoc]

/-- The real initialized B frontier is the real initialized A frontier plus
ONE literal original A-to-B calendar window. No prefix equality is supplied. -/
theorem actual_frontier_original_window_append (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (a b : O.Vertex) (hab : O.calendar.age a < O.calendar.age b) :
    actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age b) =
      actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age a) ++
        fullSpanAgenda O.network O.calendar H gamma common a b := by
  have hA := actual_compiled_calendar_date_cut O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
    (O.calendar.age a) (original_date_scheduled O.network O.calendar a)
  have hB := actual_compiled_calendar_date_cut O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
    (O.calendar.age b) (original_date_scheduled O.network O.calendar b)
  have hTail := actual_calendar_tail_cut O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
    (afterDate O.network O.calendar (O.calendar.age a)) (original_after_ordered _ _ _)
    (O.calendar.age b) (original_after_member _ _ _ b hab) (O.calendar.age a)
  have hf : (afterDate O.network O.calendar (O.calendar.age a)).filter (fun t => decide (O.calendar.age b < t)) =
    afterDate O.network O.calendar (O.calendar.age b) := filter_after_filter hab _
  rw [hf] at hTail
  let future := nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age b) ++
    calendarTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age b)
      (afterDate O.network O.calendar (O.calendar.age b))
  have batch (t : ℝ) : boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) t =
      (originalExits O.network O.calendar t).map (fun e => .boundary (.exit e)) ++
        nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) t := rfl
  have hAFinal : compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) =
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age a) ++
        fullSpanAgenda O.network O.calendar H gamma common a b) ++ future := by
    unfold afterDate at hTail
    rw [hA,hTail,batch,batch]
    simp only [actualFrontierProgram,fullSpanAgenda,canonicalEpochBlock,future,originalExits,afterDate,List.append_assoc]
  have hBFinal : compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) =
      actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age b) ++ future := by
    rw [hB,batch]
    simp only [actualFrontierProgram,future,originalExits,afterDate,List.append_assoc]
  exact List.append_cancel_right (hBFinal.symm.trans hAFinal)

noncomputable def crossingPrefix (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (a b : O.Vertex) :=
  fullSpanAgenda O.network O.calendar H gamma common a b

noncomputable def crossingConcurrent (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (b c : O.Vertex) (firstCut : O.Edge) :=
  closingSpanAgenda O H gamma common b c firstCut

noncomputable def crossingSuffix (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (c d : O.Vertex)
    (firstCut lastCut : O.Edge) :=
  remainingClosingExits O firstCut ++ closingSpanAgenda O H gamma common c d lastCut

theorem actual_first_crossing_phase (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (a b c : O.Vertex) (firstCut : O.Edge)
    (hab : O.calendar.age a < O.calendar.age b) (hbc : O.calendar.age b < O.calendar.age c) :
    closingSpanAgenda O H gamma common a c firstCut =
      crossingPrefix O H gamma common a b ++ crossingConcurrent O H gamma common b c firstCut :=
  actual_closing_span_agenda_append O H gamma common a b c firstCut hab hbc

theorem actual_second_crossing_phase (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (b c d : O.Vertex)
    (firstCut lastCut : O.Edge) (hfirst : O.network.graph.source firstCut = c)
    (hbc : O.calendar.age b < O.calendar.age c) (hcd : O.calendar.age c < O.calendar.age d) :
    closingSpanAgenda O H gamma common b d lastCut =
      crossingConcurrent O H gamma common b c firstCut ++ crossingSuffix O H gamma common c d firstCut lastCut := by
  rw [actual_closing_span_agenda_append O H gamma common b c d lastCut hbc hcd,
    actual_full_batch_span_closing_cut O H gamma common b c firstCut hfirst]
  simp only [crossingConcurrent,crossingSuffix,List.append_assoc]

theorem actual_whole_crossing_original_calendar (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (a b c d : O.Vertex) (firstCut lastCut : O.Edge)
    (hfirst : O.network.graph.source firstCut = c) (hlast : O.network.graph.source lastCut = d)
    (hab : O.calendar.age a < O.calendar.age b) (hbc : O.calendar.age b < O.calendar.age c)
    (hcd : O.calendar.age c < O.calendar.age d) :
    compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) =
      actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age a) ++
        crossingPrefix O H gamma common a b ++ crossingConcurrent O H gamma common b c firstCut ++
        crossingSuffix O H gamma common c d firstCut lastCut ++ originalClosingFuture O H gamma common lastCut := by
  rw [actual_original_closing_calendar_decomposition O H gamma common a d lastCut hlast (hab.trans (hbc.trans hcd)),
    actual_closing_span_agenda_append O H gamma common a b d lastCut hab (hbc.trans hcd),
    actual_second_crossing_phase O H gamma common b c d firstCut lastCut hfirst hbc hcd]
  simp only [crossingPrefix,List.append_assoc]

#print axioms actual_whole_crossing_original_calendar
#print axioms actual_frontier_original_window_append
end G1OriginalCrossingCalendar
