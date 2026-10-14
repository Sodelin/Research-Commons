import G1CanonicalPendingRootTerminal

/-! Actual ORIGINAL node kernels execute as concrete private/base operations
on the canonical runtime actor family. Every owner membership, other-slot
footprint and base separation is DERIVED from the original physical calendar. -/
namespace G1CanonicalOriginalNodeAsyncStep
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1ActiveCoreBridgeCohorts G1CanonicalFiniteActiveEpochAdmission G1OriginalActorOperationOwnership
open G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets G1CanonicalPendingBoundaryMembership
open G1CanonicalOriginalActorOpening G1CanonicalOriginalActorClosing
open G1TaggedOriginalCalendar G1ActualOriginalPrivateAsyncStep G1ActualOriginalBaseAsyncStep
open G1ActualOriginalUnrankedLocalKernel G1PendingActorInterfaceCommutation G1OriginalSpanRegion
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalDateActors (T : Source X) (date : ℝ) := (afterOpeningActors T date).toList

noncomputable def canonicalNodeAsyncOperation (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (node : O.Vertex) :=
  let actors := canonicalDateActors T (O.calendar.age node)
  let slots := originalPendingSlots O D sample actors
  match nodeActorOwner O H D hD node with
  | some actor => AsyncOperation.localStep actor
      (originalLocalRow O.network sample r (slots actor) [eraseEvent O H gamma common (.node node)])
  | none => AsyncOperation.exterior
      (originalLocalRow O.network sample r (activeOriginalBase O D sample actors) [eraseEvent O H gamma common (.node node)])

/-- Complete actual source-to-async node row at the canonical runtime roles.
No caller-supplied owner/separator/kernel equality is an assumption. Current
private region support is the precise real-prefix invariant propagated next. -/
theorem actual_canonical_original_node_async_step (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (node : O.Vertex)
    (s : Code O.network sample)
    (hregion : ∀ actor ∈ canonicalDateActors T (O.calendar.age node),
      ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
        SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x)) :
    (sourceProgram O.network r [eraseEvent O H gamma common (.node node)] s).map
      (originalAsyncProjection O (activeOriginalBase O D sample (canonicalDateActors T (O.calendar.age node)))
        (originalPendingSlots O D sample (canonicalDateActors T (O.calendar.age node)))) =
    asyncStep (canonicalNodeAsyncOperation O H D hD sample gamma common r node)
      (originalAsyncProjection O (activeOriginalBase O D sample (canonicalDateActors T (O.calendar.age node)))
        (originalPendingSlots O D sample (canonicalDateActors T (O.calendar.age node))) s) := by
  let actors := canonicalDateActors T (O.calendar.age node)
  cases howner : nodeActorOwner O H D hD node with
  | none =>
    simp only [canonicalNodeAsyncOperation,howner]
    apply actual_original_base_boundary_async_step O H D hD (.node node) howner (fun _ _ he => by cases he) gamma common
    intro actor x hx
    by_cases hm : actor ∈ canonicalDateActors T (O.calendar.age node)
    · have hx' : x ∈ originalInsideCopies O sample (actorInput O D actor) := by
        simpa only [originalPendingSlots,if_pos hm] using hx
      exact hregion actor hm x hx'
    · simp only [originalPendingSlots,if_neg hm,Finset.notMem_empty] at hx
  | some owner =>
    simp only [canonicalNodeAsyncOperation,howner]
    have hm : owner ∈ actors := Finset.mem_toList.mpr (actual_original_owned_node_is_active O H D hD node owner howner)
    apply actual_original_private_boundary_async_step O H D hD owner (.node node) howner gamma common
    · exact actual_pending_actor_base_disjoint O D sample actors owner hm
    · intro other hne
      by_cases ho : other ∈ canonicalDateActors T (O.calendar.age node)
      · have ha : T.calendar.Active (O.calendar.age node) owner.val := (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2
        have hb : T.calendar.Active (O.calendar.age node) other.val := (Finset.mem_filter.mp (Finset.mem_toList.mp ho)).2
        simp only [originalPendingSlots,if_pos ho]
        exact actual_active_originated_original_cohorts_disjoint O H D hD owner.val other.val owner.property other.property
          (fun he => hne (Subtype.ext he).symm) _ ha hb sample
      · simp [originalPendingSlots,ho]

#print axioms actual_canonical_original_node_async_step
end G1CanonicalOriginalNodeAsyncStep
