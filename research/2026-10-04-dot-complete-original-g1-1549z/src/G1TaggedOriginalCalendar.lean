import G1RootBlobRetainedBaseOwnership

/-! The exact original compiler with its original operation sites retained.
Equal dates use one boundary batch; every original exit precedes every node
at that date, in the SAME original finite-list order. -/
namespace G1TaggedOriginalCalendar
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

inductive OriginalEvent (O : Source.{u,v,w} X)
  | interval (lower upper : ℝ)
  | exit (population : O.Edge)
  | node (site : O.Vertex)

noncomputable def eraseEvent (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) : OriginalEvent O → ProgramStep O.network
  | .interval a b => .interval (Real.toNNReal (b-a))
  | .exit e => .boundary (.exit e)
  | .node v => .boundary (originalNodeOperation O.network H (fun h => gamma h.val) (fun h => common h.val) v)

noncomputable def originalBoundaryEvents (O : Source.{u,v,w} X) (date : ℝ) : List (OriginalEvent O) :=
  (Finset.univ.filter (fun e : O.Edge => O.calendar.age (O.network.graph.source e) = date)).toList.map OriginalEvent.exit ++
    (Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = date)).toList.map OriginalEvent.node

noncomputable def originalEventTail (O : Source.{u,v,w} X) : ℝ → List ℝ → List (OriginalEvent O)
  | _,[] => []
  | a,b::bs => .interval a b :: (originalBoundaryEvents O b ++ originalEventTail O b bs)

noncomputable def originalEvents (O : Source.{u,v,w} X) : List (OriginalEvent O) :=
  match sortedOriginalDates O.network O.calendar with
  | [] => []
  | a::as => originalBoundaryEvents O a ++ originalEventTail O a as

lemma actual_boundary_event_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (date : ℝ) :
    (originalBoundaryEvents O date).map (eraseEvent O H gamma common) =
      boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) date := by
  simp only [originalBoundaryEvents,List.map_append,List.map_map,Function.comp_def,eraseEvent]
  rfl

lemma actual_event_tail_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (dates : List ℝ) (a : ℝ) :
    (originalEventTail O a dates).map (eraseEvent O H gamma common) =
      calendarTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) a dates := by
  induction dates generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp only [originalEventTail,List.map_cons,List.map_append,eraseEvent,calendarTail]
      rw [actual_boundary_event_erasure,ih]

/-- This erasure is the literal full ORIGINAL compiler, including equal-date
exit order, pulse sites, register identity and original epoch durations. -/
theorem actual_full_original_event_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) :
    (originalEvents O).map (eraseEvent O H gamma common) =
      compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) := by
  unfold originalEvents compiledCalendarProgram
  cases sortedOriginalDates O.network O.calendar with
  | nil => rfl
  | cons a as => rw [List.map_append,actual_boundary_event_erasure,actual_event_tail_erasure]

lemma actual_boundary_exit_event (O : Source.{u,v,w} X) (e : O.Edge) (date : ℝ) :
    OriginalEvent.exit e ∈ originalBoundaryEvents O date ↔ O.calendar.age (O.network.graph.source e) = date := by
  simp only [originalBoundaryEvents,List.mem_append,List.mem_map]
  constructor
  · rintro (⟨f,hf,hfe⟩ | ⟨v,hv,hve⟩)
    · cases hfe
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hf)).2
    · cases hve
  · intro h
    exact Or.inl ⟨e,Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩),rfl⟩

lemma actual_boundary_node_event (O : Source.{u,v,w} X) (v : O.Vertex) (date : ℝ) :
    OriginalEvent.node v ∈ originalBoundaryEvents O date ↔ O.calendar.age v = date := by
  simp only [originalBoundaryEvents,List.mem_append,List.mem_map]
  constructor
  · rintro (⟨f,hf,hfe⟩ | ⟨t,ht,htv⟩)
    · cases hfe
    · cases htv
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp ht)).2
  · intro h
    exact Or.inr ⟨v,Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩),rfl⟩

#print axioms actual_full_original_event_erasure
end G1TaggedOriginalCalendar
