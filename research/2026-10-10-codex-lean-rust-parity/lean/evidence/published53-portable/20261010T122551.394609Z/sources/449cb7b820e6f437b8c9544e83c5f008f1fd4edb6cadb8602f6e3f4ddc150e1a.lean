import G1CanonicalOriginalActorClosing

/-! No private actor survives the final original root-date exit/open batch.
All original labels/populations/SAME register are back in base before the
retained original root operation and actual ancestral completion. -/
namespace G1CanonicalPendingRootTerminal
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCalendarTiming
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalFiniteActiveEpochAdmission G1ActualFinitePanelProgramTensor
open G1CanonicalOriginalActorOpening G1ActualOriginalPrivateAsyncStep G1OriginalWholeCausalView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- Source rootedness and strict original edge ages exclude every private
bridge at root date, regardless of overlapping/coincident lower dates. -/
theorem actual_after_root_actor_set_empty (T : Source.{u,v,w} X) :
    afterOpeningActors T (T.calendar.age T.network.root) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro actor ha
  have hp := (Finset.mem_filter.mp ha).2
  have hupper : T.calendar.age (T.network.graph.source actor.val) ≤ T.calendar.age T.network.root :=
    T.calendar.age_le_of_directed (T.network.rooted _)
  exact (not_lt_of_ge hupper) hp.2

theorem actual_root_batch_closes_all_source_actors (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D) :
    afterExitActors O H D hD (T.calendar.age T.network.root)
      (G1OriginalCalendarDecomposition.originalExits O.network O.calendar (T.calendar.age T.network.root)) ∪
      dateOpeningActors T (T.calendar.age T.network.root) = ∅ := by
  rw [actual_all_exits_then_openings_active_set,actual_after_root_actor_set_empty]

lemma actual_empty_actor_base_all_original (O : Source X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) :
    activeOriginalBase O D sample [] = Finset.univ := by
  simp [activeOriginalBase,activeOriginalPanels,panelUnion]

/-- Once the source-derived root actor set is empty, the pending base is
literally the complete original causal view, ready for SAME root/completion.
This terminal interface is not itself a whole-calendar replay assertion. -/
theorem actual_pending_empty_base_whole_original (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X} (s : Code O.network sample) :
    (originalAsyncProjection O (activeOriginalBase O D sample []) (originalPendingSlots O D sample []) s).1 =
      wholeOriginalView O.network s := by
  rw [actual_empty_actor_base_all_original]
  rfl

#print axioms actual_root_batch_closes_all_source_actors
#print axioms actual_pending_empty_base_whole_original
end G1CanonicalPendingRootTerminal
