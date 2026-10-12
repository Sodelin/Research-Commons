import G1ActualRootRecordedStageTrace
import G1CanonicalExtractedPrivateKWord

/-! The runtime's derived boundary owner is EXACTLY the original span's
private source-operation predicate. This supplies source-private-word syntax
alignment, rather than an assumed actor-kernel/source-law equality. -/
namespace G1ActualActorOwnedPrivateSyntax
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceBoundaryLocations
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1PrivateActorLifetimeAdmission
open G1OriginalSpanRegion G1OriginalRecipePopulationOwnership G1TaggedOriginalCalendar
open G1ActualPrivateOriginalWordExtraction G1OriginalNodeBatchBinding
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_original_exit_owner_iff_private_region (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (edge : O.Edge) :
    eventActor O H D hD (.exit edge) = some actor ↔
      edge ∈ edgeRegion O (bridgeSpan O T D actor.val actor.property) := by
  constructor
  · exact actual_owned_exit_member O H D hD edge actor
  · intro he
    have hp : edge ∈ recipePopulations O (D.recipe actor.val) := by
      rw [←actual_bridge_span_populations]; exact he
    have ho := actual_population_owner_unique O H D hD edge actor.val hp
    have hb : T.network.graph.IsBridge (populationOwner O H D hD edge) := ho ▸ actor.property
    have ha : (⟨populationOwner O H D hD edge,hb⟩ : BridgeActor T) = actor := Subtype.ext ho.symm
    simp only [eventActor,dif_pos hb,ha]

noncomputable def ownedPrivateEvent (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) : OriginalEvent O → Bool
  | .interval _ _ => true
  | event => decide (eventActor O H D hD event = some actor)

/-- Both private predicates are derived from the SAME original operation,
registry, gamma/mode and physical span. Parallel exit IDs remain distinct. -/
theorem actual_owned_private_event_is_original_span_predicate (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (event : OriginalEvent O) :
    privateStep O (bridgeSpan O T D actor.val actor.property) (eraseEvent O H gamma common event) =
      ownedPrivateEvent O H D hD actor event := by
  cases event with
  | interval lower upper => rfl
  | exit edge =>
    simp only [privateStep,eraseEvent,ownedPrivateEvent,G1ExteriorBoundarySilence.touchedPlace,SpanLocation]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (actual_original_exit_owner_iff_private_region O H D hD actor edge).symm
  | node node =>
    simp only [privateStep,eraseEvent,ownedPrivateEvent,eventActor,actual_node_touched_site,SpanLocation]
    have he : node ∈ nodeRegion O (bridgeSpan O T D actor.val actor.property) ↔ nodeActorOwner O H D hD node = some actor :=
      ⟨actual_node_actor_owner_of_member O H D hD node actor,actual_owned_node_member O H D hD node actor⟩
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact he

/-- Exact original private operation list extracted by runtime ownership.
Every original interval in the selected phase remains; outside boundaries
alone are removed from this private coordinate. The full source is unchanged. -/
theorem actual_owned_private_events_extract_original_ops (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (events : List (OriginalEvent O)) :
    privateOriginalOps O (bridgeSpan O T D actor.val actor.property) (events.map (eraseEvent O H gamma common)) =
      (events.filter (ownedPrivateEvent O H D hD actor)).map (eraseEvent O H gamma common) := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    have he := actual_owned_private_event_is_original_span_predicate O H D hD actor gamma common event
    have ht : List.filter (privateStep O (bridgeSpan O T D actor.val actor.property)) (events.map (eraseEvent O H gamma common)) =
        (events.filter (ownedPrivateEvent O H D hD actor)).map (eraseEvent O H gamma common) := ih
    simp only [privateOriginalOps,List.map_cons,List.filter_cons,he,ht]
    cases ownedPrivateEvent O H D hD actor event <;> simp

#print axioms actual_owned_private_events_extract_original_ops
end G1ActualActorOwnedPrivateSyntax
