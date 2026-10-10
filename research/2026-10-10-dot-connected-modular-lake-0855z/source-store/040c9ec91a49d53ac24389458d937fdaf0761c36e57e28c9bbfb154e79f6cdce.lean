import G1CanonicalWholeCalendarSameCompletion
import G1CanonicalPendingTrueKExposure

/-! Exact source-operation identities for the private kernels emitted by the
actual compiler. History observation and other-coordinate work contribute no
private kernel. Original node/exit ownership and current roles derive the
fixed original descendant cohort; no kernel/output identity is a premise. -/
namespace G1CanonicalActorKernelSourceBindings
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalPendingBoundaryMembership G1CanonicalOriginalActorOpening G1CanonicalOriginalNodeAsyncStep
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalEpochAsync
open G1ActualOriginalUnrankedLocalKernel G1OriginalActorPrivateWordKernel
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1PendingBaseCheckpointRecorder
open G1TaggedOriginalCalendar G1ActiveCoreBridgeCohorts G1UnrankedSourceView
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

lemma owner_kernels_append {I S Base : Type*} [DecidableEq I] (owner : I)
    (first last : List (AsyncOperation I S Base)) :
    ownerKernels owner (first ++ last) = ownerKernels owner first ++ ownerKernels owner last := by
  induction first with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [List.cons_append,ownerKernels]
    case localStep other kernel => split_ifs <;> simp [ih]
    all_goals exact ih

lemma owner_kernels_history_lift {I S Base Obs : Type*} [DecidableEq I]
    (owner : I) (ops : List (AsyncOperation I S Base)) :
    ownerKernels owner (ops.map (historyLift (Obs := Obs))) = ownerKernels owner ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [List.map_cons,historyLift,ownerKernels]
    case localStep other kernel => split_ifs <;> simp [ih]
    all_goals exact ih

lemma owner_kernels_recorded_block {I S Base Obs : Type*} [DecidableEq I]
    (owner : I) (observer : Base → Obs) (ops : List (AsyncOperation I S Base)) :
    ownerKernels owner (recordedBlock observer ops) = ownerKernels owner ops := by
  rw [recordedBlock,owner_kernels_append,owner_kernels_history_lift]
  simp [recordBaseCheckpoint,ownerKernels]

lemma owner_kernels_nodup_coordinate_draws {I S Base : Type*} [DecidableEq I]
    (owner : I) (actors : List I) (kernels : I → S → PMF S) (hn : actors.Nodup) :
    ownerKernels owner (actors.map (fun other => (AsyncOperation.localStep other (kernels other) : AsyncOperation I S Base))) =
      if owner ∈ actors then [kernels owner] else [] := by
  induction actors with
  | nil => simp [ownerKernels]
  | cons other actors ih =>
    have hp := List.nodup_cons.mp hn
    simp only [List.map_cons,ownerKernels]
    rw [ih hp.2]
    by_cases he : owner = other
    · subst other; simp [hp.1]
    · simp [he]

/-- Each actual node's emitted private kernel has its fixed ORIGINAL inside
carrier. Runtime role membership is derived from actual node ownership. -/
theorem actual_original_node_owner_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (node : O.Vertex) :
    ownerKernels actor [canonicalNodeAsyncOperation O H D hD sample gamma common r node] =
      if nodeActorOwner O H D hD node = some actor then
        [originalLocalRow O.network sample r (originalInsideCopies O sample (actorInput O D actor))
          [eraseEvent O H gamma common (.node node)]] else [] := by
  cases ho : nodeActorOwner O H D hD node with
  | none => simp [canonicalNodeAsyncOperation,ho,ownerKernels]
  | some owner =>
    by_cases he : actor = owner
    · subst owner
      have hm : actor ∈ canonicalDateActors T (O.calendar.age node) := Finset.mem_toList.mpr
        (actual_original_owned_node_is_active O H D hD node actor ho)
      simp [canonicalNodeAsyncOperation,ho,ownerKernels,originalPendingSlots,hm]
    · simp [canonicalNodeAsyncOperation,ho,ownerKernels,he,Ne.symm he]

/-- The original parallel exit ID and exact processed-exit prefix derive the
pending actor carrier, including its own final cut before immediate close. -/
theorem actual_original_exit_owner_kernel (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (date : ℝ) (processed : List O.Edge) (edge : O.Edge)
    (hprocessed : ∀ e ∈ processed, O.calendar.age (O.network.graph.source e) = date)
    (hdate : O.calendar.age (O.network.graph.source edge) = date) (hnew : edge ∉ processed) :
    ownerKernels actor [canonicalExitAsyncOperation O H D hD sample gamma common r date processed edge] =
      if eventActor O H D hD (.exit edge) = some actor then
        [originalLocalRow O.network sample r (originalInsideCopies O sample (actorInput O D actor))
          [eraseEvent O H gamma common (.exit edge)]] else [] := by
  cases ho : eventActor O H D hD (.exit edge) with
  | none => simp [canonicalExitAsyncOperation,ho,ownerKernels]
  | some owner =>
    by_cases he : actor = owner
    · subst owner
      have hm : actor ∈ canonicalExitActors O H D hD date processed := Finset.mem_toList.mpr
        (actual_original_owned_exit_is_pending O H D hD date processed edge hprocessed hdate hnew actor ho)
      simp [canonicalExitAsyncOperation,ho,ownerKernels,originalPendingSlots,hm]
    · simp [canonicalExitAsyncOperation,ho,ownerKernels,he,Ne.symm he]

/-- A genuine old epoch contributes exactly ONE unchanged-duration private
source kernel to each active original actor, and none to every inactive slot. -/
theorem actual_original_epoch_owner_kernel (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (r : PositivePairRates O.Edge) (actor : BridgeActor T) (date : ℝ) (duration : ℝ≥0) :
    ownerKernels actor (canonicalEpochAsyncOps O D sample r date duration) =
      if actor ∈ canonicalDateActors T date then
        [originalLocalRow O.network sample r (originalInsideCopies O sample (actorInput O D actor)) [.interval duration]] else [] := by
  unfold canonicalEpochAsyncOps
  rw [owner_kernels_append]
  have hdraw := owner_kernels_nodup_coordinate_draws (Base := UnrankedView O.Vertex O.Edge Copy)
    actor (canonicalDateActors T date)
    (fun other => originalLocalRow O.network sample r
      (originalPendingSlots O D sample (canonicalDateActors T date) other) [.interval duration])
    (Finset.nodup_toList _)
  rw [hdraw]
  by_cases hm : actor ∈ canonicalDateActors T date <;>
    simp [hm,ownerKernels,originalPendingSlots]

#print axioms actual_original_node_owner_kernel
#print axioms actual_original_exit_owner_kernel
#print axioms actual_original_epoch_owner_kernel
end G1CanonicalActorKernelSourceBindings
