import G1CanonicalActorKernelSourceBindings

/-! The whole real chronological boundary compiler emits exactly the
source-owned private operation word on a fixed ORIGINAL actor carrier.
Immediate close, original opens and every checkpoint contribute no hidden
private operation. The exact exit IDs and original ordering are retained. -/
namespace G1CanonicalBoundaryPrivateWordBinding
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalOriginalOpeningAsyncBatch G1CanonicalOriginalExitCloseReplay G1CanonicalOriginalExitAsyncStep
open G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalBoundaryAsyncBatch G1OriginalCalendarDecomposition
open G1ActualOriginalNodeBatchRootHistory G1ActualOriginalExitBatchRootHistory G1ActualOriginalBoundaryRootHistory
open G1ActualOriginalUnrankedLocalKernel G1OriginalActorPrivateWordKernel
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1PendingBaseCheckpointRecorder
open G1TaggedOriginalCalendar G1ActiveCoreBridgeCohorts G1UnrankedSourceView
open G1CanonicalActorKernelSourceBindings
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma owner_kernels_opening_batch (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (actor : BridgeActor T) (actors opening : List (BridgeActor T)) :
    ownerKernels actor (canonicalOpeningBatchOps O D sample actors opening) = [] := by
  induction opening generalizing actors with
  | nil => rfl
  | cons other opening ih =>
    change ownerKernels actor (canonicalOpeningBatchOps O D sample (actors ++ [other]) opening) = []
    exact ih _

lemma actual_recorded_nodes_private_kernel_word (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (nodes : List O.Vertex) :
    ownerKernels actor (canonicalRecordedNodeBatchOps O H D hD sample gamma common r nodes) =
      nodes.flatMap (fun node => if nodeActorOwner O H D hD node = some actor then
        [originalLocalRow O.network sample r (originalInsideCopies O sample (actorInput O D actor))
          [eraseEvent O H gamma common (.node node)]] else []) := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
    rw [canonicalRecordedNodeBatchOps,List.flatMap_cons,owner_kernels_append,owner_kernels_recorded_block,
      actual_original_node_owner_kernel]
    exact congrArg _ ih

lemma actual_recorded_exits_private_kernel_word (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (date : ℝ) (processed edges : List O.Edge)
    (hprocessed : ∀ e ∈ processed, O.calendar.age (O.network.graph.source e) = date)
    (hdate : ∀ e ∈ edges, O.calendar.age (O.network.graph.source e) = date)
    (hn : (processed ++ edges).Nodup) :
    ownerKernels actor (canonicalRecordedExitBatchOps O H D hD sample gamma common r date processed edges) =
      edges.flatMap (fun edge => if eventActor O H D hD (.exit edge) = some actor then
        [originalLocalRow O.network sample r (originalInsideCopies O sample (actorInput O D actor))
          [eraseEvent O H gamma common (.exit edge)]] else []) := by
  induction edges generalizing processed with
  | nil => rfl
  | cons edge edges ih =>
    have he := hdate edge (List.mem_cons_self)
    have hnew : edge ∉ processed := by
      intro hm
      exact (List.nodup_append.mp hn).2.2 edge hm edge (List.mem_cons_self) rfl
    have hp : ∀ e ∈ processed ++ [edge], O.calendar.age (O.network.graph.source e) = date := by
      intro e hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hprocessed e hm
      · exact (List.mem_singleton.mp hm) ▸ he
    have ht := fun e hm => hdate e (List.mem_cons_of_mem edge hm)
    have hn' : ((processed ++ [edge]) ++ edges).Nodup := by
      simpa only [List.append_assoc,List.singleton_append] using hn
    have hclose : ownerKernels (S := UnrankedView O.Vertex O.Edge Copy) (Base := UnrankedView O.Vertex O.Edge Copy) actor ((closingActor O H D hD (.exit edge)).toList.map (fun other =>
        AsyncOperation.interface other
          (G1ActualOriginalOpenCloseAsyncInterface.originalCloseKernel (originalInsideCopies O sample (actorInput O D other))))) = [] := by
      cases closingActor O H D hD (.exit edge) <;> rfl
    rw [canonicalRecordedExitBatchOps,owner_kernels_append,owner_kernels_recorded_block,
      canonicalRuntimeExitOps,owner_kernels_append,hclose,List.append_nil,
      actual_original_exit_owner_kernel O H D hD sample gamma common r actor date processed edge hprocessed he hnew,
      ih _ hp ht hn',List.flatMap_cons]

noncomputable def originalBoundaryPrivateWord (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (date : ℝ) :=
  ((originalBoundaryEvents O date).filter (fun event => decide (eventActor O H D hD event = some actor))).map
    (eraseEvent O H gamma common)

lemma filter_map_as_flatmap {A B : Type*} (items : List A) (pred : A → Bool) (f : A → B) :
    (items.filter pred).map f = items.flatMap (fun item => if pred item then [f item] else []) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    cases he : pred item <;> simp [he,ih]

/-- No original boundary operation is duplicated or lost in the private
kernel word emitted by the ACTUAL full boundary/history compiler. -/
theorem actual_whole_boundary_private_kernel_word (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (date : ℝ) :
    ownerKernels actor (canonicalRecordedBoundaryOps O H D hD sample gamma common r date) =
      (originalBoundaryPrivateWord O H D hD actor gamma common date).map
        (fun op => originalLocalRow O.network sample r (originalInsideCopies O sample (actorInput O D actor)) [op]) := by
  unfold canonicalRecordedBoundaryOps
  rw [owner_kernels_append,owner_kernels_append,owner_kernels_history_lift,owner_kernels_opening_batch,List.append_nil]
  rw [actual_recorded_exits_private_kernel_word O H D hD sample gamma common r actor date [] (originalExits O.network O.calendar date)
    (fun _ hm => by cases hm)
    (fun e hm => (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2)
    (by simpa only [List.nil_append,originalExits] using Finset.nodup_toList _),
    actual_recorded_nodes_private_kernel_word]
  unfold originalBoundaryPrivateWord originalBoundaryEvents
  rw [List.filter_append,List.map_append,List.map_append,List.map_map,List.map_map]
  simp only [Function.comp_def,filter_map_as_flatmap,List.flatMap_map,eraseEvent,eventActor,originalExits,decide_eq_true_eq]

#print axioms actual_whole_boundary_private_kernel_word
end G1CanonicalBoundaryPrivateWordBinding
