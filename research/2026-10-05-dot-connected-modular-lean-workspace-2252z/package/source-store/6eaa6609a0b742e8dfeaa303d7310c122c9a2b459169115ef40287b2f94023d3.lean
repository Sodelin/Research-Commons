import G1CanonicalOriginalExitAsyncStep

/-! A literal original exit and its immediate source-derived close replay on
changing runtime roles. Closing is after the true exit and before recording
its original post-cut checkpoint, including exits into the retained root blob. -/
namespace G1CanonicalOriginalExitCloseReplay
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalPendingBoundaryMembership G1CanonicalOriginalActorOpening G1CanonicalOriginalActorClosing
open G1CanonicalFiniteActiveEpochAdmission G1ActiveCoreBridgeCohorts G1ActualFinitePanelProgramTensor
open G1TaggedOriginalCalendar G1ActualOriginalPrivateAsyncStep G1ActualOriginalOpenCloseAsyncInterface
open G1PendingActorInterfaceCommutation G1CanonicalOriginalExitAsyncStep G1ActualJointProgram
open G1InitializedFrontierPrefix G1PrivateActorLifetimeAdmission
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_original_actor_projection_membership (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (first last : List (BridgeActor T)) (heq : ∀ actor, actor ∈ first ↔ actor ∈ last) :
    originalAsyncProjection O (sample := sample) (activeOriginalBase O D sample first) (originalPendingSlots O D sample first) =
      originalAsyncProjection O (sample := sample) (activeOriginalBase O D sample last) (originalPendingSlots O D sample last) := by
  have hp : panelUnion (activeOriginalPanels O D sample first) = panelUnion (activeOriginalPanels O D sample last) := by
    ext x
    constructor <;> intro hx
    · obtain ⟨keep,hk,hxk⟩ := (actual_panel_union_member _ x).mp hx
      obtain ⟨actor,hm,rfl⟩ := List.mem_map.mp hk
      exact (actual_panel_union_member _ x).mpr ⟨_,List.mem_map.mpr ⟨actor,(heq actor).mp hm,rfl⟩,hxk⟩
    · obtain ⟨keep,hk,hxk⟩ := (actual_panel_union_member _ x).mp hx
      obtain ⟨actor,hm,rfl⟩ := List.mem_map.mp hk
      exact (actual_panel_union_member _ x).mpr ⟨_,List.mem_map.mpr ⟨actor,(heq actor).mpr hm,rfl⟩,hxk⟩
  have hb : activeOriginalBase O D sample first = activeOriginalBase O D sample last := by
    unfold activeOriginalBase; rw [hp]
  have hs : originalPendingSlots O D sample first = originalPendingSlots O D sample last := by
    funext actor; simp only [originalPendingSlots,heq actor]
  rw [hb,hs]

lemma actual_closing_actor_identifies_cut (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (edge : O.Edge) (actor : BridgeActor T)
    (hclose : closingActor O H D hD (.exit edge) = some actor) : edge = actorCut O H D hD actor := by
  change (match eventActor O H D hD (.exit edge) with
    | none => none
    | some other => if edge = actorCut O H D hD other then some other else none) = some actor at hclose
  cases ho : eventActor O H D hD (.exit edge) with
  | none => simp [ho] at hclose
  | some other =>
    rw [ho] at hclose
    by_cases he : edge = actorCut O H D hD other
    · simp [he] at hclose; subst other; exact he
    · simp [he] at hclose

noncomputable def canonicalRuntimeExitOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (date : ℝ) (processed : List O.Edge) (edge : O.Edge) :=
  [canonicalExitAsyncOperation O H D hD sample gamma common r date processed edge] ++
    (closingActor O H D hD (.exit edge)).toList.map (fun actor =>
      AsyncOperation.interface actor (originalCloseKernel (originalInsideCopies O sample (actorInput O D actor))))

lemma actual_exit_close_projection_row (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) (processed : List O.Edge) (edge : O.Edge)
    (hprocessed : ∀ e ∈ processed, O.calendar.age (O.network.graph.source e) = O.calendar.age node)
    (hdate : O.calendar.age (O.network.graph.source edge) = O.calendar.age node) (hnew : edge ∉ processed)
    {initial : Code O.network sample}
    (hs : initial ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    {s : Code O.network sample}
    (hp : s ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) initial).support)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r [eraseEvent O H gamma common (.exit edge)] s).support) :
    PMF.pure (canonicalExitProjection O H D hD (O.calendar.age node) (processed ++ [edge]) d) =
      asyncProgram ((closingActor O H D hD (.exit edge)).toList.map (fun actor =>
        AsyncOperation.interface actor (originalCloseKernel (originalInsideCopies O sample (actorInput O D actor)))))
        (canonicalExitProjection O H D hD (O.calendar.age node) processed d) := by
  cases hc : closingActor O H D hD (.exit edge) with
  | none =>
    have hm : ∀ actor, actor ∈ canonicalExitActors O H D hD (O.calendar.age node) (processed ++ [edge]) ↔
        actor ∈ canonicalExitActors O H D hD (O.calendar.age node) processed := by
      intro actor
      have hn : edge ≠ actorCut O H D hD actor := by
        intro he
        have hyes := actual_cut_closes_actor O H D hD actor
        rw [←he,hc] at hyes; cases hyes
      simp [canonicalExitActors,afterExitActors,Ne.symm hn]
    simp only [hc,Option.toList_none,List.map_nil,asyncProgram]
    unfold canonicalExitProjection
    rw [actual_original_actor_projection_membership O D _ _ hm]
  | some actor =>
    have he := actual_closing_actor_identifies_cut O H D hD edge actor hc
    have hu : T.calendar.age (T.network.graph.source actor.val) = O.calendar.age node := by
      rw [he,actual_actor_cut_source] at hdate
      simpa only [D.calendar] using hdate
    have ho : eventActor O H D hD (.exit edge) = some actor := by
      unfold closingActor at hc
      cases hx : eventActor O H D hD (.exit edge) with
      | none => simp [hx] at hc
      | some other =>
        split at hc <;> simp_all
    have ha : actor ∈ canonicalExitActors O H D hD (O.calendar.age node) processed :=
      Finset.mem_toList.mpr (actual_original_owned_exit_is_pending O H D hD _ processed edge hprocessed hdate hnew actor ho)
    have hm : ∀ other, other ∈ canonicalExitActors O H D hD (O.calendar.age node) (processed ++ [edge]) ↔
        other ∈ (canonicalExitActors O H D hD (O.calendar.age node) processed).filter (fun other => decide (other ≠ actor)) := by
      intro other
      rw [he]
      simp only [canonicalExitActors,actual_pending_exit_close_set_update,Finset.mem_toList,Finset.mem_erase,
        List.mem_filter,decide_eq_true_eq]
      tauto
    simp only [hc,Option.toList_some,List.map_cons,List.map_nil,asyncProgram,PMF.bind_pure]
    unfold canonicalExitProjection
    rw [actual_original_actor_projection_membership O D _ _ hm]
    apply actual_canonical_original_actor_close_interface O H D hD actor _ ha _
      sample register gamma common r (initial := initial) _ processed _ (s := s) _ (d := d) _
    · intro other hm
      rw [hu]
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).1
    · rw [←D.calendar,hu]
      exact hs
    · exact he ▸ hnew
    · exact hp
    · simpa only [eraseEvent,he] using hd

/-- Genuine full source row for one old exit plus its immediate physical
close, with actual current-role/base reconstruction and source-derived kernels. -/
theorem actual_real_original_exit_close_replay (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) (processed : List O.Edge) (edge : O.Edge)
    (hprocessed : ∀ e ∈ processed, O.calendar.age (O.network.graph.source e) = O.calendar.age node)
    (hdate : O.calendar.age (O.network.graph.source edge) = O.calendar.age node) (hnew : edge ∉ processed)
    {initial : Code O.network sample}
    (hs : initial ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    {s : Code O.network sample}
    (hp : s ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) initial).support) :
    (sourceProgram O.network r [eraseEvent O H gamma common (.exit edge)] s).map
      (canonicalExitProjection O H D hD (O.calendar.age node) (processed ++ [edge])) =
    asyncProgram (canonicalRuntimeExitOps O H D hD sample gamma common r (O.calendar.age node) processed edge)
      (canonicalExitProjection O H D hD (O.calendar.age node) processed s) := by
  let closes : List (AsyncOperation (BridgeActor T)
      (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy) (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) := (closingActor O H D hD (.exit edge)).toList.map (fun actor =>
    AsyncOperation.interface actor (originalCloseKernel (originalInsideCopies O sample (actorInput O D actor))))
  calc
    _ = (sourceProgram O.network r [eraseEvent O H gamma common (.exit edge)] s).bind (fun d =>
        asyncProgram closes (canonicalExitProjection O H D hD (O.calendar.age node) processed d)) := by
      unfold PMF.map
      apply bind_eq_of_eq_on_support
      exact fun d hd => actual_exit_close_projection_row O H D hD sample register gamma common r node processed edge
        hprocessed hdate hnew hs hp hd
    _ = ((sourceProgram O.network r [eraseEvent O H gamma common (.exit edge)] s).map
        (canonicalExitProjection O H D hD (O.calendar.age node) processed)).bind (asyncProgram closes) := by
      rw [PMF.bind_map]; rfl
    _ = _ := by
      rw [actual_real_partial_original_exit_async_step O H D hD sample register gamma common r node processed edge
        hprocessed hdate hnew hs hp]
      simp only [canonicalRuntimeExitOps,asyncProgram,List.cons_append,List.nil_append,PMF.pure_bind]
      rfl

#print axioms actual_real_original_exit_close_replay
end G1CanonicalOriginalExitCloseReplay
