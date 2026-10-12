import G1CanonicalOriginalExitAsyncBatch

/-! All original-date openings execute in the original node-site order, after
all old exits and before any old node operation. Their saved opaque cohorts
are physically in base. The final slots are exactly the active core bridges. -/
namespace G1CanonicalOriginalOpeningAsyncBatch
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalOriginalActorOpening G1CanonicalOriginalActorClosing G1CanonicalFiniteActiveEpochAdmission
open G1ActiveCoreBridgeCohorts G1ActualOriginalPrivateAsyncStep G1ActualOriginalOpenCloseAsyncInterface
open G1ActorInterfaceUniqueness G1TaggedOriginalCalendar G1PendingActorInterfaceCommutation
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalExitCloseReplay G1CanonicalOriginalNodeAsyncBatch
open G1CanonicalOriginalNodeAsyncStep G1OriginalCalendarDecomposition
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalOriginalOpeningActors (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (date : ℝ) :=
  ((Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = date)).toList).filterMap
    (fun v => openingActor O H D hD (.node v))

lemma actual_original_opening_actor_membership (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (date : ℝ) (actor : BridgeActor T) :
    actor ∈ canonicalOriginalOpeningActors O H D hD date ↔ actor ∈ dateOpeningActors T date := by
  constructor
  · intro hm
    obtain ⟨v,hv,ho⟩ := List.mem_filterMap.mp hm
    have he : v = actorInput O D actor := OriginalEvent.node.inj ((actual_opening_actor_site_iff O H D hD (.node v) actor).mp ho)
    have hd := (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
    rw [he] at hd
    simpa only [dateOpeningActors,Finset.mem_filter,Finset.mem_univ,true_and,actorInput,D.calendar] using hd
  · intro hm
    have hd := (Finset.mem_filter.mp hm).2
    apply List.mem_filterMap.mpr
    refine ⟨actorInput O D actor,Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩),?_⟩
    · simpa only [actorInput,D.calendar] using hd
    · exact actual_input_opens_actor O H D hD actor

lemma actual_original_opening_actor_nodup (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (date : ℝ) :
    (canonicalOriginalOpeningActors O H D hD date).Nodup := by
  apply List.Nodup.filterMap _ (Finset.nodup_toList _)
  intro a b actor ha hb
  have ha := (actual_opening_actor_site_iff O H D hD (.node a) actor).mp (Option.mem_def.mp ha)
  have hb := (actual_opening_actor_site_iff O H D hD (.node b) actor).mp (Option.mem_def.mp hb)
  exact OriginalEvent.node.inj (ha.trans hb.symm)

noncomputable def canonicalOpeningBatchOps (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) :
    List (BridgeActor T) → List (BridgeActor T) → List (AsyncOperation (BridgeActor T)
      (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy) (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy))
  | _,[] => []
  | actors,actor::opening => .interface actor
      (originalOpenKernel (originalInsideCopies O sample (actorInput O D actor)) (activeOriginalBase O D sample actors)) ::
      canonicalOpeningBatchOps O D sample (actors ++ [actor]) opening

lemma actual_original_opening_list_replay (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (date : ℝ) (actors opening : List (BridgeActor T))
    (hnodup : (actors ++ opening).Nodup)
    (hactive : ∀ actor ∈ actors, T.calendar.Active date actor.val)
    (hopen : ∀ actor ∈ opening, T.calendar.age (T.network.graph.target actor.val) = date) :
    PMF.pure (originalAsyncProjection O (activeOriginalBase O D sample (actors ++ opening))
      (originalPendingSlots O D sample (actors ++ opening)) s) =
    asyncProgram (canonicalOpeningBatchOps O D sample actors opening)
      (originalAsyncProjection O (activeOriginalBase O D sample actors) (originalPendingSlots O D sample actors) s) := by
  induction opening generalizing actors with
  | nil => simp [canonicalOpeningBatchOps,asyncProgram]
  | cons actor opening ih =>
    have hd := hopen actor (List.mem_cons_self)
    have hnew : actor ∉ actors := by
      intro hm
      exact (List.nodup_append.mp hnodup).2.2 actor hm actor (List.mem_cons_self) rfl
    have hn' : ((actors ++ [actor]) ++ opening).Nodup := by
      simpa only [List.append_assoc,List.singleton_append] using hnodup
    have ha' : ∀ other ∈ actors ++ [actor], T.calendar.Active date other.val := by
      intro other hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hactive other hm
      · have he := List.mem_singleton.mp hm
        subst other; exact ⟨hd.le,hd ▸ T.calendar.edge_older actor.val⟩
    have hi := ih (actors ++ [actor]) hn' ha' (fun other hm => hopen other (List.mem_cons_of_mem actor hm))
    have ho := actual_canonical_original_actor_open_interface O H D hD s actors actor hnew
      (by simpa only [hd] using hactive)
    calc
      _ = asyncProgram (canonicalOpeningBatchOps O D sample (actors ++ [actor]) opening)
          (originalAsyncProjection O (activeOriginalBase O D sample (actors ++ [actor]))
            (originalPendingSlots O D sample (actors ++ [actor])) s) := by
        simpa only [List.append_assoc,List.singleton_append] using hi
      _ = (PMF.pure (originalAsyncProjection O (activeOriginalBase O D sample (actors ++ [actor]))
            (originalPendingSlots O D sample (actors ++ [actor])) s)).bind
          (asyncProgram (canonicalOpeningBatchOps O D sample (actors ++ [actor]) opening)) := (PMF.pure_bind _ _).symm
      _ = _ := by rw [ho]; rfl

/-- The literal original-site opening order reconstructs exactly the canonical
post-opening active slots. All close/open date coincidences are admitted. -/
theorem actual_canonical_original_opening_batch_replay (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (date : ℝ) (s : Code O.network sample) :
    PMF.pure (canonicalDateProjection O D date s) =
    asyncProgram (canonicalOpeningBatchOps O D sample
      (canonicalExitActors O H D hD date (originalExits O.network O.calendar date))
      (canonicalOriginalOpeningActors O H D hD date))
      (canonicalExitProjection O H D hD date (originalExits O.network O.calendar date) s) := by
  let actors := canonicalExitActors O H D hD date (originalExits O.network O.calendar date)
  let opening := canonicalOriginalOpeningActors O H D hD date
  have hactive : ∀ actor ∈ actors, T.calendar.Active date actor.val := by
    intro actor hm
    have ha := Finset.mem_toList.mp hm
    have he : actor ∈ afterOpeningActors T date := by
      rw [←actual_all_exits_then_openings_active_set O H D hD date]
      exact Finset.mem_union_left _ ha
    exact (Finset.mem_filter.mp he).2
  have hopen : ∀ actor ∈ opening, T.calendar.age (T.network.graph.target actor.val) = date := by
    intro actor hm
    exact (Finset.mem_filter.mp ((actual_original_opening_actor_membership O H D hD date actor).mp hm)).2
  have hn : (actors ++ opening).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.nodup_toList _,actual_original_opening_actor_nodup O H D hD date,?_⟩
    intro a ha b hb he
    subst b
    have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_toList.mp ha)).1).2.1
    exact (ne_of_lt hp) (hopen a hb)
  have hm : ∀ actor, actor ∈ canonicalDateActors T date ↔ actor ∈ actors ++ opening := by
    intro actor
    simp only [List.mem_append,canonicalDateActors,Finset.mem_toList]
    rw [←actual_all_exits_then_openings_active_set O H D hD date,Finset.mem_union]
    exact or_congr (Finset.mem_toList.symm) (actual_original_opening_actor_membership O H D hD date actor).symm
  unfold canonicalDateProjection
  rw [actual_original_actor_projection_membership O D _ _ hm]
  exact actual_original_opening_list_replay O H D hD s date actors opening hn hactive hopen

#print axioms actual_canonical_original_opening_batch_replay
end G1CanonicalOriginalOpeningAsyncBatch
