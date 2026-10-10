import G1OriginalEventSiteUniqueness

/-! A source-derived finite actor lifecycle, with actual opening/closing
interfaces inserted around the SAME literal original operations. This is the
physical compiler/tagging layer; pending-K execution is proved separately. -/
namespace G1CanonicalActorLifecycleCompiler
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanRegion G1OriginalRecipePopulationOwnership
open G1ConstructedPopulationPartition G1OriginalActorOperationOwnership
open G1OriginalSpanBridgeBookends G1OriginatedBridgeBookends G1OriginalSpanClosingPhase G1OriginatedClosingSourceAdmission
open G1TaggedOriginalCalendar G1OriginalEventSiteUniqueness
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def actorInput (O : Source X) {T : Source X} (D : Decoration O T) (actor : BridgeActor T) :=
  D.vertex (T.network.graph.target actor.val)

noncomputable def actorCut (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :=
  originatedLastCut O H D hD actor.val actor.property

lemma actual_last_cut_in_region (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b)
    (e : O.Edge) (he : EndsAt O e word) : e ∈ edgeRegion O word := by
  induction word with
  | edge f _ => exact Finset.mem_singleton.mpr he.symm
  | bigon _ => exact False.elim he
  | append first last _ ih => exact Finset.mem_union_right _ (ih he)

lemma actual_actor_cut_in_region (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    actorCut O H D hD actor ∈ edgeRegion O (bridgeSpan O T D actor.val actor.property) :=
  actual_last_cut_in_region O _ _ (actual_original_last_cut O _
    (actual_bridge_span_bookends O T D actor.val actor.property (actual_originated_recipes_bookended O H D hD actor.val)).2).2.2

noncomputable def eventActor (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) : OriginalEvent O → Option (BridgeActor T)
  | .interval _ _ => none
  | .node v => nodeActorOwner O H D hD v
  | .exit e =>
      if hb : T.network.graph.IsBridge (populationOwner O H D hD e) then
        some ⟨populationOwner O H D hD e,hb⟩ else none

noncomputable def openingActor (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) : OriginalEvent O → Option (BridgeActor T)
  | .node v => match nodeActorOwner O H D hD v with
      | none => none
      | some actor => if v = actorInput O D actor then some actor else none
  | _ => none

noncomputable def closingActor (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) : OriginalEvent O → Option (BridgeActor T)
  | .exit e => match eventActor O H D hD (.exit e) with
      | none => none
      | some actor => if e = actorCut O H D hD actor then some actor else none
  | _ => none

lemma actual_input_opens_actor (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    openingActor O H D hD (.node (actorInput O D actor)) = some actor := by
  have hn := actual_node_actor_owner_of_member O H D hD (actorInput O D actor) actor (actual_span_input_in_region O _)
  simp [openingActor,hn]

lemma actual_cut_closes_actor (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    closingActor O H D hD (.exit (actorCut O H D hD actor)) = some actor := by
  have hp := actual_actor_cut_in_region O H D hD actor
  rw [actual_bridge_span_populations] at hp
  have ho := actual_population_owner_unique O H D hD _ actor.val hp
  have hb : T.network.graph.IsBridge (populationOwner O H D hD (actorCut O H D hD actor)) := ho ▸ actor.property
  have ha : (⟨populationOwner O H D hD (actorCut O H D hD actor),hb⟩ : BridgeActor T) = actor :=
    Subtype.ext ho.symm
  simp [closingActor,eventActor,dif_pos hb,ha]

inductive ActorInstruction (O : Source.{u,v,w} X) (T : Source.{u,v,w} X)
  | open (actor : BridgeActor T)
  | privateBoundary (actor : BridgeActor T) (event : OriginalEvent O)
  | close (actor : BridgeActor T)
  | baseBoundary (event : OriginalEvent O)
  | epoch (lower upper : ℝ)

noncomputable def compileEvent (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D) :
    OriginalEvent O → List (ActorInstruction O T)
  | .interval a b => [.epoch a b]
  | event =>
      (openingActor O H D hD event).toList.map ActorInstruction.open ++
      (match eventActor O H D hD event with
        | none => [ActorInstruction.baseBoundary event]
        | some actor => [ActorInstruction.privateBoundary actor event]) ++
      (closingActor O H D hD event).toList.map ActorInstruction.close

noncomputable def actorInstructions (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D) :=
  (originalEvents O).flatMap (compileEvent O H D hD)

noncomputable def eraseInstruction (O : Source.{u,v,w} X) {T : Source.{u,v,w} X}
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) :
    ActorInstruction O T → List (ProgramStep O.network)
  | .open _ => []
  | .close _ => []
  | .privateBoundary _ event => [eraseEvent O H gamma common event]
  | .baseBoundary event => [eraseEvent O H gamma common event]
  | .epoch a b => [.interval (Real.toNNReal (b-a))]

lemma actual_compile_event_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (event : OriginalEvent O) :
    (compileEvent O H D hD event).flatMap (eraseInstruction O H gamma common) = [eraseEvent O H gamma common event] := by
  cases event with
  | interval a b => rfl
  | node v =>
      simp only [compileEvent]
      cases eventActor O H D hD (.node v) <;>
        cases openingActor O H D hD (.node v) <;>
        simp [closingActor,eraseInstruction,List.flatMap_append]
  | exit e =>
      simp only [compileEvent]
      cases eventActor O H D hD (.exit e) <;>
        cases closingActor O H D hD (.exit e) <;>
        simp [openingActor,eraseInstruction,List.flatMap_append]

/-- Literal full compiler equality is derived for arbitrary many actors and
coincident dates. The source-law interpreter still needs its active-state
coordinate factorization before replacing these tags by pending K execution. -/
theorem actual_actor_instruction_full_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) :
    (actorInstructions O H D hD).flatMap (eraseInstruction O H gamma common) =
      UnifiedLean.Source.SourceCalendarCompiler.compiledCalendarProgram O.network O.calendar H
        (fun h => gamma h.val) (fun h => common h.val) := by
  rw [actorInstructions,List.flatMap_assoc]
  have hf : (fun ev => (compileEvent O H D hD ev).flatMap (eraseInstruction O H gamma common)) =
      (fun ev => [eraseEvent O H gamma common ev]) := by
    funext ev
    exact actual_compile_event_erasure O H D hD gamma common ev
  rw [hf]
  change (originalEvents O).flatMap (pure ∘ eraseEvent O H gamma common) = _
  rw [List.flatMap_pure_eq_map,actual_full_original_event_erasure]

#print axioms actual_actor_instruction_full_erasure
#print axioms actual_input_opens_actor
#print axioms actual_cut_closes_actor
end G1CanonicalActorLifecycleCompiler
