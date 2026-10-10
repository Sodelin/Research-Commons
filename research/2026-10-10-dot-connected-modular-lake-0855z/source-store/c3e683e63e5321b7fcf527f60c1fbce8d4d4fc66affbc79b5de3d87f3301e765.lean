import G1CanonicalActorLifecycleCompiler

/-! Every source-derived bridge actor opens and closes exactly once. These
facts cover arbitrary many actors and equal boundary dates; no manual actor
schedule, distinct-date premise or output-law assumption is supplied. -/
namespace G1ActorInterfaceUniqueness
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1TaggedOriginalCalendar G1OriginalEventSiteUniqueness
open G1CanonicalActorLifecycleCompiler
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_opening_actor_site_iff (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (event : OriginalEvent O) (actor : BridgeActor T) :
    openingActor O H D hD event = some actor ↔ event = .node (actorInput O D actor) := by
  constructor
  · intro h
    cases event with
    | interval _ _ => cases h
    | exit _ => cases h
    | node v =>
        simp only [openingActor] at h
        cases hn : nodeActorOwner O H D hD v with
        | none => rw [hn] at h; cases h
        | some owner =>
            rw [hn] at h
            dsimp only at h
            split_ifs at h with hv
            · have ha : owner = actor := Option.some.inj h
              subst owner
              exact congrArg OriginalEvent.node hv
  · rintro rfl
    exact actual_input_opens_actor O H D hD actor

lemma actual_closing_actor_site_iff (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (event : OriginalEvent O) (actor : BridgeActor T) :
    closingActor O H D hD event = some actor ↔ event = .exit (actorCut O H D hD actor) := by
  constructor
  · intro h
    cases event with
    | interval _ _ => cases h
    | node _ => cases h
    | exit e =>
        simp only [closingActor] at h
        cases he : eventActor O H D hD (.exit e) with
        | none => rw [he] at h; cases h
        | some owner =>
            rw [he] at h
            dsimp only at h
            split_ifs at h with hc
            · have ha : owner = actor := Option.some.inj h
              subst owner
              exact congrArg OriginalEvent.exit hc
  · rintro rfl
    exact actual_cut_closes_actor O H D hD actor

noncomputable def openingTrace (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) :=
  (originalBoundaryTrace O).filterMap (openingActor O H D hD)

noncomputable def closingTrace (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) :=
  (originalBoundaryTrace O).filterMap (closingActor O H D hD)

theorem actual_every_actor_opens_once (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) :
    (openingTrace O H D hD).Nodup ∧ ∀ actor : BridgeActor T, actor ∈ openingTrace O H D hD := by
  constructor
  · apply List.Nodup.filterMap _ (actual_original_boundary_sites_nodup O)
    intro a b actor ha hb
    have ha := (actual_opening_actor_site_iff O H D hD a actor).mp (Option.mem_def.mp ha)
    have hb := (actual_opening_actor_site_iff O H D hD b actor).mp (Option.mem_def.mp hb)
    exact ha.trans hb.symm
  · intro actor
    exact List.mem_filterMap.mpr ⟨.node (actorInput O D actor),actual_every_original_node_site O _,
      actual_input_opens_actor O H D hD actor⟩

theorem actual_every_actor_closes_once (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) :
    (closingTrace O H D hD).Nodup ∧ ∀ actor : BridgeActor T, actor ∈ closingTrace O H D hD := by
  constructor
  · apply List.Nodup.filterMap _ (actual_original_boundary_sites_nodup O)
    intro a b actor ha hb
    have ha := (actual_closing_actor_site_iff O H D hD a actor).mp (Option.mem_def.mp ha)
    have hb := (actual_closing_actor_site_iff O H D hD b actor).mp (Option.mem_def.mp hb)
    exact ha.trans hb.symm
  · intro actor
    exact List.mem_filterMap.mpr ⟨.exit (actorCut O H D hD actor),actual_every_original_exit_site O _,
      actual_cut_closes_actor O H D hD actor⟩

#print axioms actual_every_actor_opens_once
#print axioms actual_every_actor_closes_once
end G1ActorInterfaceUniqueness
