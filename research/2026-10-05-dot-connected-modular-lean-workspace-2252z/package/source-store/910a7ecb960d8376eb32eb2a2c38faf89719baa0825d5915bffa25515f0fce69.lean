import G1OriginalActorTemporalFootprint
import Mathlib.Data.List.Nodup

/-! Every literal original node/exit site occurs exactly once in the tagged
full calendar, including coincident dates and parallel original edge IDs. -/
namespace G1OriginalEventSiteUniqueness
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1TaggedOriginalCalendar
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def boundarySite (O : Source.{u,v,w} X) : OriginalEvent O → Option (OriginalEvent O)
  | .interval _ _ => none
  | .exit e => some (.exit e)
  | .node v => some (.node v)

noncomputable def originalBoundaryTrace (O : Source.{u,v,w} X) :=
  (originalEvents O).filterMap (boundarySite O)

lemma actual_boundary_sites_only (O : Source.{u,v,w} X) (date : ℝ) :
    (originalBoundaryEvents O date).filterMap (boundarySite O) = originalBoundaryEvents O date := by
  simp [originalBoundaryEvents,List.filterMap_map,boundarySite]

lemma actual_tail_boundary_trace (O : Source.{u,v,w} X) (dates : List ℝ) (a : ℝ) :
    (originalEventTail O a dates).filterMap (boundarySite O) = dates.flatMap (originalBoundaryEvents O) := by
  induction dates generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp only [originalEventTail,List.filterMap_cons,boundarySite,List.filterMap_append,List.flatMap_cons]
      change (originalBoundaryEvents O b).filterMap (boundarySite O) ++
        (originalEventTail O b bs).filterMap (boundarySite O) = _
      rw [actual_boundary_sites_only,ih]

lemma actual_full_boundary_trace (O : Source.{u,v,w} X) :
    originalBoundaryTrace O = (sortedOriginalDates O.network O.calendar).flatMap (originalBoundaryEvents O) := by
  unfold originalBoundaryTrace originalEvents
  cases sortedOriginalDates O.network O.calendar with
  | nil => rfl
  | cons a as => rw [List.filterMap_append,actual_boundary_sites_only,actual_tail_boundary_trace,List.flatMap_cons]

lemma actual_boundary_batch_nodup (O : Source.{u,v,w} X) (date : ℝ) :
    (originalBoundaryEvents O date).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(Finset.nodup_toList _).map (fun _ _ h => OriginalEvent.exit.inj h),
    (Finset.nodup_toList _).map (fun _ _ h => OriginalEvent.node.inj h),?_⟩
  intro a ha b hb heq
  obtain ⟨e,he,h⟩ := List.mem_map.mp ha
  obtain ⟨v,hv,h'⟩ := List.mem_map.mp hb
  have himpossible : (OriginalEvent.exit e : OriginalEvent O) = OriginalEvent.node v := h.trans (heq.trans h'.symm)
  cases himpossible

lemma actual_boundary_event_date (O : Source.{u,v,w} X) (date : ℝ) (event : OriginalEvent O)
    (h : event ∈ originalBoundaryEvents O date) :
    match event with
    | .interval _ _ => False
    | .exit e => O.calendar.age (O.network.graph.source e) = date
    | .node v => O.calendar.age v = date := by
  cases event with
  | interval a b =>
      simp only [originalBoundaryEvents,List.mem_append,List.mem_map] at h
      rcases h with ⟨e,he,h⟩ | ⟨v,hv,h⟩ <;> cases h
  | exit e => exact (actual_boundary_exit_event O e date).mp h
  | node v => exact (actual_boundary_node_event O v date).mp h

lemma actual_distinct_date_batches_disjoint (O : Source.{u,v,w} X) {a b : ℝ} (hne : a ≠ b) :
    List.Disjoint (originalBoundaryEvents O a) (originalBoundaryEvents O b) := by
  intro event ha hb
  have hdA := actual_boundary_event_date O a event ha
  have hdB := actual_boundary_event_date O b event hb
  cases event with
  | interval _ _ => exact hdA
  | exit _ => exact hne (hdA.symm.trans hdB)
  | node _ => exact hne (hdA.symm.trans hdB)

/-- No source event is duplicated when same-date actor opens/closes coexist.
Parallel original edges remain distinct literal exit sites. -/
theorem actual_original_boundary_sites_nodup (O : Source.{u,v,w} X) :
    (originalBoundaryTrace O).Nodup := by
  rw [actual_full_boundary_trace]
  apply List.nodup_flatMap.mpr
  exact ⟨fun a _ => actual_boundary_batch_nodup O a,
    (original_dates_ordered O.network O.calendar).2.imp (fun h => actual_distinct_date_batches_disjoint O h)⟩

theorem actual_every_original_node_site (O : Source.{u,v,w} X) (v : O.Vertex) :
    OriginalEvent.node v ∈ originalBoundaryTrace O := by
  rw [actual_full_boundary_trace]
  exact List.mem_flatMap.mpr ⟨O.calendar.age v,original_date_scheduled O.network O.calendar v,
    (actual_boundary_node_event O v _).mpr rfl⟩

theorem actual_every_original_exit_site (O : Source.{u,v,w} X) (e : O.Edge) :
    OriginalEvent.exit e ∈ originalBoundaryTrace O := by
  rw [actual_full_boundary_trace]
  exact List.mem_flatMap.mpr ⟨O.calendar.age (O.network.graph.source e),
    original_date_scheduled O.network O.calendar _,(actual_boundary_exit_event O e _).mpr rfl⟩

#print axioms actual_original_boundary_sites_nodup
#print axioms actual_every_original_exit_site
end G1OriginalEventSiteUniqueness
