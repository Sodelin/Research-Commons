import G1ActorInterfaceUniqueness
import Mathlib.Data.List.Pairwise

/-! Lifecycle order derives from the ACTUAL original chronological list.
An actor opens before its one close even when OTHER actor dates coincide.
No arbitrary-family schedule legality is an assumed field. -/
namespace G1OriginalActorLifecycleOrder
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1TaggedOriginalCalendar G1OriginalEventSiteUniqueness
open G1CanonicalActorLifecycleCompiler G1ActorInterfaceUniqueness
open G1OriginalSpanCalendarDecomposition G1OriginalSpanClosingPhase G1OriginatedClosingSourceAdmission
open G1OriginalSpanBridgeBookends G1OriginatedBridgeBookends
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def siteDate (O : Source.{u,v,w} X) : OriginalEvent O → ℝ
  | .interval _ b => b
  | .exit e => O.calendar.age (O.network.graph.source e)
  | .node v => O.calendar.age v

lemma actual_batch_site_date (O : Source.{u,v,w} X) (date : ℝ) (event : OriginalEvent O)
    (h : event ∈ originalBoundaryEvents O date) : siteDate O event = date := by
  have hd := actual_boundary_event_date O date event h
  cases event with
  | interval _ _ => exact False.elim hd
  | exit _ => exact hd
  | node _ => exact hd

lemma actual_boundary_trace_chronological (O : Source.{u,v,w} X) :
    (originalBoundaryTrace O).Pairwise (fun a b => siteDate O a ≤ siteDate O b) := by
  rw [actual_full_boundary_trace]
  apply List.pairwise_flatMap.mpr
  constructor
  · intro date hdate
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    rw [actual_batch_site_date O date a ha,actual_batch_site_date O date b hb]
  · exact (original_dates_ordered O.network O.calendar).1.imp (fun hab a ha b hb => by
      rw [actual_batch_site_date O _ a ha,actual_batch_site_date O _ b hb]
      exact hab)

lemma strict_key_index_order {A : Type*} [DecidableEq A] (key : A → ℝ) (trace : List A)
    (order : trace.Pairwise (fun a b => key a ≤ key b)) (a b : A)
    (ha : a ∈ trace) (hb : b ∈ trace) (hlt : key a < key b) : trace.idxOf a < trace.idxOf b := by
  have haLen := List.idxOf_lt_length_of_mem ha
  have hbLen := List.idxOf_lt_length_of_mem hb
  let ia : Fin trace.length := ⟨trace.idxOf a,haLen⟩
  let ib : Fin trace.length := ⟨trace.idxOf b,hbLen⟩
  have haGet : trace.get ia = a := List.getElem_idxOf haLen
  have hbGet : trace.get ib = b := List.getElem_idxOf hbLen
  by_contra h
  have hba : ib ≤ ia := Nat.le_of_not_gt h
  letI : Std.Refl (fun a b : A => key a ≤ key b) := ⟨fun _ => le_rfl⟩
  have hle := order.rel_get_of_le hba
  rw [haGet,hbGet] at hle
  exact (not_le_of_gt hlt) hle

/-- Both interfaces occur in the literal original chronology, with strict
own-port time order derived from the original span. Other actors may share
any opening/closing dates; their finite batch order is kept unchanged. -/
theorem actual_actor_open_before_close (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    (originalBoundaryTrace O).idxOf (.node (actorInput O D actor)) <
      (originalBoundaryTrace O).idxOf (.exit (actorCut O H D hD actor)) := by
  apply strict_key_index_order (siteDate O) (originalBoundaryTrace O) (actual_boundary_trace_chronological O)
    _ _ (actual_every_original_node_site O _) (actual_every_original_exit_site O _)
  have hc := actual_original_last_cut O (bridgeSpan O T D actor.val actor.property)
    (actual_bridge_span_bookends O T D actor.val actor.property (actual_originated_recipes_bookended O H D hD actor.val)).2
  change O.calendar.age (actorInput O D actor) < O.calendar.age (O.network.graph.source (actorCut O H D hD actor))
  have hsource := hc.2.1
  change O.network.graph.source (actorCut O H D hD actor) = _ at hsource
  rw [hsource]
  exact actual_span_dates_strict O.network O.calendar (bridgeSpan O T D actor.val actor.property)

#print axioms actual_actor_open_before_close
end G1OriginalActorLifecycleOrder
