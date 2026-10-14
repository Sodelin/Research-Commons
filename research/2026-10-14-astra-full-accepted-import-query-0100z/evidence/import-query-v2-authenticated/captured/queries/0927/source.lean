import G1CanonicalWholePrivateSourceWord

/-! The exact whole private source word is selected from the ORIGINAL event
calendar, with every interval's real lower/upper dates retained. Only active
epochs contribute; private boundary selection is the physical owner predicate.
This prevents a hidden replay of exterior-only time in a bridge label. -/
namespace G1CanonicalActivePrivateEventWord
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalOriginalNodeAsyncStep
open G1CanonicalBoundaryPrivateWordBinding G1CanonicalWholePrivateSourceWord G1TaggedOriginalCalendar
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def ownedActiveEvent (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) : OriginalEvent O → Bool
  | .interval lower _ => decide (actor ∈ canonicalDateActors T lower)
  | event => decide (eventActor O H D hD event = some actor)

lemma actual_boundary_active_filter (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) (date : ℝ) :
    (originalBoundaryEvents O date).filter (ownedActiveEvent O H D hD actor) =
      (originalBoundaryEvents O date).filter (fun event => decide (eventActor O H D hD event = some actor)) := by
  apply List.filter_congr
  intro event hm
  cases event with
  | interval a b => simp [originalBoundaryEvents] at hm
  | exit e => rfl
  | node v => rfl

/-- Exact chronological source word grammar, including all real active
intervals, and no inactive epochs before opening or after physical close. -/
theorem actual_active_private_event_suffix_word (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (date : ℝ) (dates : List ℝ) :
    originalActorSourceSuffix O H D hD actor gamma common date dates =
      ((originalBoundaryEvents O date ++ originalEventTail O date dates).filter (ownedActiveEvent O H D hD actor)).map
        (eraseEvent O H gamma common) := by
  induction dates generalizing date with
  | nil =>
    simp only [originalActorSourceSuffix,originalEventTail,List.append_nil,
      actual_boundary_active_filter,originalBoundaryPrivateWord]
  | cons next dates ih =>
    rw [originalActorSourceSuffix,ih]
    simp only [originalEventTail,List.filter_append,List.filter_cons,ownedActiveEvent,List.map_append]
    rw [actual_boundary_active_filter]
    by_cases hm : actor ∈ canonicalDateActors T date <;>
      simp [hm,eraseEvent,originalBoundaryPrivateWord,List.append_assoc,actual_boundary_active_filter]

theorem actual_whole_active_private_event_word (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) :
    originalActorSourceWord O H D hD actor gamma common =
      ((originalEvents O).filter (ownedActiveEvent O H D hD actor)).map (eraseEvent O H gamma common) := by
  unfold originalActorSourceWord originalEvents
  cases sortedOriginalDates O.network O.calendar with
  | nil => rfl
  | cons date dates => exact actual_active_private_event_suffix_word O H D hD actor gamma common date dates

#print axioms actual_whole_active_private_event_word
end G1CanonicalActivePrivateEventWord
