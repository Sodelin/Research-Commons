import G1CanonicalActivePrivateEventWord

/-! Exact cuts of the ORIGINAL event calendar retain the actual interval
endpoints, source sites and parallel exit identities. These bind the private
runtime word to a graph component's chronological window without inferring
timestamps from equal numerical interval durations. -/
namespace G1OriginalEventCalendarCuts
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming
open G1ActualGraphNormalization G1TaggedOriginalCalendar G1InitializedFrontierPrefix
open G1OriginalCalendarDecomposition G1CanonicalThreeEpochList
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def stopBeforeEventTail (O : Source.{u,v,w} X) (stop : ℝ) : ℝ → List ℝ → List (OriginalEvent O)
  | _,[] => []
  | lower,next::later => if next = stop then [.interval lower next]
      else .interval lower next :: (originalBoundaryEvents O next ++ stopBeforeEventTail O stop next later)

noncomputable def beforeBoundaryEvents (O : Source.{u,v,w} X) (stop : ℝ) : List (OriginalEvent O) :=
  match sortedOriginalDates O.network O.calendar with
  | [] => []
  | date::dates => if date = stop then []
      else originalBoundaryEvents O date ++ stopBeforeEventTail O stop date dates

lemma actual_stopped_event_tail_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (stop lower : ℝ) (dates : List ℝ) :
    (stopBeforeEventTail O stop lower dates).map (eraseEvent O H gamma common) =
      stopBeforeTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) stop lower dates := by
  induction dates generalizing lower with
  | nil => rfl
  | cons next dates ih =>
    by_cases hn : next = stop
    · simp [stopBeforeEventTail,stopBeforeTail,hn,eraseEvent]
    · simp only [stopBeforeEventTail,stopBeforeTail,if_neg hn,List.map_cons,List.map_append,eraseEvent]
      rw [actual_boundary_event_erasure,ih]

lemma actual_before_boundary_events_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (stop : ℝ) :
    (beforeBoundaryEvents O stop).map (eraseEvent O H gamma common) =
      beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) stop := by
  unfold beforeBoundaryEvents beforeBoundaryProgram
  cases sortedOriginalDates O.network O.calendar with
  | nil => rfl
  | cons date dates =>
    by_cases hd : date = stop
    · simp [hd]
    · simp only [if_neg hd,List.map_append]
      rw [actual_boundary_event_erasure,actual_stopped_event_tail_erasure]

theorem actual_original_event_tail_cut (O : Source.{u,v,w} X) (dates : List ℝ)
    (horder : dates.Pairwise (· < ·)) (stop : ℝ) (hstop : stop ∈ dates) (lower : ℝ) :
    originalEventTail O lower dates = stopBeforeEventTail O stop lower dates ++
      originalBoundaryEvents O stop ++ originalEventTail O stop (dates.filter (fun c => decide (stop < c))) := by
  induction dates generalizing lower with
  | nil => exact False.elim (List.not_mem_nil hstop)
  | cons next dates ih =>
    have hp := List.pairwise_cons.mp horder
    by_cases hn : next = stop
    · subst next
      rw [filter_after_head hp.1]
      simp [originalEventTail,stopBeforeEventTail,List.append_assoc]
    · have hm : stop ∈ dates := (List.mem_cons.mp hstop).resolve_left (Ne.symm hn)
      have hlt := hp.1 _ hm
      have hfilter : (next::dates).filter (fun d => decide (stop < d)) = dates.filter (fun d => decide (stop < d)) :=
        by simp [not_lt_of_gt hlt]
      rw [hfilter]
      simp only [originalEventTail,stopBeforeEventTail,if_neg hn,List.cons_append]
      rw [ih hp.2 hm next]
      simp only [List.append_assoc]

/-- Literal whole event calendar cut at an actual original node boundary.
All interval endpoints and source-site labels survive the cut. -/
theorem actual_whole_original_event_date_cut (O : Source.{u,v,w} X) (stop : ℝ)
    (hm : stop ∈ sortedOriginalDates O.network O.calendar) :
    originalEvents O = beforeBoundaryEvents O stop ++ originalBoundaryEvents O stop ++
      originalEventTail O stop (afterDate O.network O.calendar stop) := by
  have hne : sortedOriginalDates O.network O.calendar ≠ [] := by
    intro he; rw [he] at hm; exact List.not_mem_nil hm
  obtain ⟨date,dates,he⟩ := List.exists_cons_of_ne_nil hne
  have ho := original_dates_strict O.network O.calendar
  rw [he] at ho hm
  have hp := List.pairwise_cons.mp ho
  by_cases hd : date = stop
  · subst date
    simp [originalEvents,beforeBoundaryEvents,afterDate,he,filter_after_head hp.1]
  · have hs : stop ∈ dates := (List.mem_cons.mp hm).resolve_left (Ne.symm hd)
    have hlt := hp.1 _ hs
    simp only [originalEvents,beforeBoundaryEvents,he,if_neg hd]
    rw [actual_original_event_tail_cut O dates hp.2 stop hs date]
    simp [afterDate,he,not_lt_of_gt hlt,List.append_assoc]

#print axioms actual_whole_original_event_date_cut
end G1OriginalEventCalendarCuts
