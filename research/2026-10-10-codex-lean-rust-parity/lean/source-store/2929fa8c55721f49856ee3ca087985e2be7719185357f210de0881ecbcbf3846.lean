import G1OriginalPrivateWindowBounds

/-! Literal original tagged calendar = real entering frontier, exact component
phase through its original last cut, and the SAME remaining original future.
Interval endpoints survive, so private active-epoch selection is source-bound. -/
namespace G1OriginalClosingEventDecomposition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1TaggedOriginalCalendar G1InitializedFrontierPrefix
open G1OriginalCalendarDecomposition G1CanonicalThreeEpochList G1CanonicalComponentSegment
open G1OriginalEventCalendarCuts G1OriginalSpanClosingPhase G1CanonicalEpochSpecialization
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalNodeEvents (O : Source.{u,v,w} X) (date : ℝ) :=
  (Finset.univ.filter (fun node : O.Vertex => O.calendar.age node = date)).toList.map OriginalEvent.node

noncomputable def openingFrontierEvents (O : Source.{u,v,w} X) (node : O.Vertex) :=
  beforeBoundaryEvents O (O.calendar.age node) ++
    (originalExits O.network O.calendar (O.calendar.age node)).map OriginalEvent.exit

noncomputable def closingSpanEvents (O : Source.{u,v,w} X) (first last : O.Vertex) (edge : O.Edge) :=
  originalNodeEvents O (O.calendar.age first) ++
    stopBeforeEventTail O (O.calendar.age last) (O.calendar.age first) (afterDate O.network O.calendar (O.calendar.age first)) ++
    (closingExits O edge).map OriginalEvent.exit

noncomputable def originalClosingEventFuture (O : Source.{u,v,w} X) (edge : O.Edge) :=
  ((originalExits O.network O.calendar (O.calendar.age (O.network.graph.source edge))).dropWhile
    (fun f => decide (f ≠ edge))).tail.map OriginalEvent.exit ++
    originalNodeEvents O (O.calendar.age (O.network.graph.source edge)) ++
    originalEventTail O (O.calendar.age (O.network.graph.source edge))
      (afterDate O.network O.calendar (O.calendar.age (O.network.graph.source edge)))

theorem actual_original_closing_event_decomposition (O : Source.{u,v,w} X)
    (first last : O.Vertex) (edge : O.Edge) (he : O.network.graph.source edge = last)
    (hlt : O.calendar.age first < O.calendar.age last) :
    originalEvents O = openingFrontierEvents O first ++ closingSpanEvents O first last edge ++
      originalClosingEventFuture O edge := by
  have hstart := actual_whole_original_event_date_cut O (O.calendar.age first)
    (original_date_scheduled O.network O.calendar first)
  have htail := actual_original_event_tail_cut O (afterDate O.network O.calendar (O.calendar.age first))
    (original_after_ordered _ _ _) (O.calendar.age last) (original_after_member _ _ _ last hlt) (O.calendar.age first)
  have hf : (afterDate O.network O.calendar (O.calendar.age first)).filter (fun date => decide (O.calendar.age last < date)) =
      afterDate O.network O.calendar (O.calendar.age last) := filter_after_filter hlt _
  rw [hf] at htail
  have hm : edge ∈ originalExits O.network O.calendar (O.calendar.age last) :=
    Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg O.calendar.age he⟩)
  have hexits := original_exit_list_cut (originalExits O.network O.calendar (O.calendar.age last)) edge hm
  have hmap := congrArg (fun es : List O.Edge => es.map (OriginalEvent.exit (O := O))) hexits
  rw [List.map_append,List.map_append,List.map_singleton] at hmap
  rw [hstart,htail]
  unfold openingFrontierEvents closingSpanEvents closingExits originalClosingEventFuture
  rw [he]
  have hboundary (date : ℝ) : originalBoundaryEvents O date =
      (originalExits O.network O.calendar date).map OriginalEvent.exit ++ originalNodeEvents O date := rfl
  rw [hboundary,hboundary]
  conv_lhs => rw [hmap]
  simp only [List.map_append,List.map_singleton,List.append_assoc]

/-- The exact source operation phase is recovered from its original event
dates/sites. No injected desired word or timing equality is assumed. -/
theorem actual_closing_span_event_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (first last : O.Vertex) (edge : O.Edge) :
    (closingSpanEvents O first last edge).map (eraseEvent O H gamma common) =
      closingSpanAgenda O H gamma common first last edge := by
  simp only [closingSpanEvents,List.map_append,actual_stopped_event_tail_erasure,
    originalNodeEvents,List.map_map,Function.comp_def,eraseEvent,closingSpanAgenda,canonicalEpochBlock,nodeOperations]

#print axioms actual_original_closing_event_decomposition
end G1OriginalClosingEventDecomposition
