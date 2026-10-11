import G1CanonicalOriginalNodeAsyncBatch

/-! Every literal original same-date exit executes its true private/base
async row on the actors whose own cuts have not yet been processed. Real
partial-batch source support supplies every retained private region. -/
namespace G1CanonicalOriginalExitAsyncStep
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalPendingBoundaryMembership G1CanonicalOriginalActorOpening G1CanonicalOriginalActorClosing
open G1CanonicalFiniteActiveEpochAdmission G1ActiveCoreBridgeCohorts
open G1TaggedOriginalCalendar G1ActualOriginalPrivateAsyncStep G1ActualOriginalBaseAsyncStep
open G1ActualOriginalUnrankedLocalKernel G1PendingActorInterfaceCommutation G1OriginalSpanRegion
open G1ActualBeforeExitActorSupport G1InitializedFrontierPrefix
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalExitActors (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (date : ℝ) (processed : List O.Edge) :=
  (afterExitActors O H D hD date processed).toList

noncomputable def canonicalExitProjection (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (date : ℝ) (processed : List O.Edge) (s : Code O.network sample) :=
  originalAsyncProjection O (activeOriginalBase O D sample (canonicalExitActors O H D hD date processed))
    (originalPendingSlots O D sample (canonicalExitActors O H D hD date processed)) s

noncomputable def canonicalExitAsyncOperation (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (date : ℝ) (processed : List O.Edge) (edge : O.Edge) :=
  let actors := canonicalExitActors O H D hD date processed
  let slots := originalPendingSlots O D sample actors
  match eventActor O H D hD (.exit edge) with
  | some actor => AsyncOperation.localStep actor
      (originalLocalRow O.network sample r (slots actor) [eraseEvent O H gamma common (.exit edge)])
  | none => AsyncOperation.exterior
      (originalLocalRow O.network sample r (activeOriginalBase O D sample actors) [eraseEvent O H gamma common (.exit edge)])

/-- The complete original exit row, before its possible immediate close.
Coincident closing dates use literal original cut identity and actual source
order. Every input-region and original-cohort footprint is derived. -/
theorem actual_real_partial_original_exit_async_step (O : Source.{u,v,w} X)
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
      (canonicalExitProjection O H D hD (O.calendar.age node) processed) =
    asyncStep (canonicalExitAsyncOperation O H D hD sample gamma common r (O.calendar.age node) processed edge)
      (canonicalExitProjection O H D hD (O.calendar.age node) processed s) := by
  let actors := canonicalExitActors O H D hD (O.calendar.age node) processed
  have hbefore : ∀ actor ∈ actors, actor ∈ beforeExitActors T (O.calendar.age node) := by
    intro actor hm
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).1
  unfold canonicalExitProjection canonicalExitAsyncOperation
  cases howner : eventActor O H D hD (.exit edge) with
  | none =>
    simp only [howner]
    apply actual_original_base_boundary_async_step O H D hD (.exit edge) howner (fun _ _ he => by cases he) gamma common
    intro actor x hx
    by_cases hm : actor ∈ canonicalExitActors O H D hD (O.calendar.age node) processed
    · have ha := Finset.mem_filter.mp (Finset.mem_toList.mp hm)
      have hb := (Finset.mem_filter.mp ha.1).2
      have hx' : x ∈ originalInsideCopies O sample (actorInput O D actor) := by
        simpa only [originalPendingSlots,if_pos hm] using hx
      exact actual_real_partial_exit_batch_actor_region O H D hD actor node
        (by simpa only [actorInput,D.calendar] using hb.1)
        (by simpa only [D.calendar] using hb.2)
        sample register gamma common r hs processed ha.2 hp x hx'
    · simp only [originalPendingSlots,if_neg hm,Finset.notMem_empty] at hx
  | some owner =>
    simp only [howner]
    have hm : owner ∈ actors := Finset.mem_toList.mpr
      (actual_original_owned_exit_is_pending O H D hD _ processed edge hprocessed hdate hnew owner howner)
    apply actual_original_private_boundary_async_step O H D hD owner (.exit edge) howner gamma common
    · exact actual_pending_actor_base_disjoint O D sample actors owner hm
    · intro other hne
      by_cases ho : other ∈ canonicalExitActors O H D hD (O.calendar.age node) processed
      · simp only [originalPendingSlots,if_pos ho]
        exact actual_before_exit_pending_cohorts_disjoint O H D hD _ owner other (Ne.symm hne)
          (hbefore owner hm) (hbefore other ho) sample
      · simp [originalPendingSlots,ho]

#print axioms actual_real_partial_original_exit_async_step
end G1CanonicalOriginalExitAsyncStep
