import G1OwnProtocolBlockExtraction

/-! Each individual emitted OWN block, even after arbitrary earlier OTHER
actor promotions, is the complete source-derived OriginalSpan K. Literal
interfaces and empty-word outside identities are identified, not fitted. -/
namespace G1CanonicalPromotedBlockTrueK
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalOwnTwoInterfaceRuntime
open G1CanonicalOwnInteriorPrivateWord G1CanonicalOwnProtocolSignature G1ActualOwnPendingKReplacement
open G1CanonicalPendingTrueKExposure G1CanonicalInitializedWholeCalendarHistory
open G1CanonicalActorKernelSourceBindings
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open G1OwnProtocolSignatureTransport G1ActualOwnerBlockEmission G1OwnProtocolBlockExtraction
open G1PendingBaseCheckpointRecorder G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_original_owner_word_nonempty (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    ownerKernels actor (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r) ≠ [] := by
  rw [←actual_own_interior_kernel_list_is_whole_private_word O H D hD sample gamma common r actor]
  simp [ownRuntimeParts,owner_kernels_append,ownerKernels,historyLift]

/-- Actual literal block extraction for an arbitrary unprocessed actor,
including crossing lifetimes and arbitrary coincident-date prior promotions.
The before/future private words are empty; the interior row is TRUE source K. -/
theorem actual_unprocessed_actor_block_admission (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (earlier : List (BridgeActor T)) (hn : actor ∉ earlier) :
    ∃ before interior future,
      promoteEveryActor earlier (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r) =
        before ++ [(ownRuntimeParts O H D hD sample gamma common r actor).opening] ++
        interior ++ [(ownRuntimeParts O H D hD sample gamma common r actor).closing] ++ future ∧
      (∀ op ∈ before, InteriorSafe actor op) ∧ (∀ op ∈ interior, InteriorSafe actor op) ∧
      (∀ op ∈ future, InteriorSafe actor op) ∧
      ownerKernels actor before = [] ∧ ownerKernels actor future = [] ∧ interior ≠ [] ∧
      actorWordKernel (ownerKernels actor interior) = canonicalPendingKRow O H D hD sample gamma common r actor := by
  let parts := ownRuntimeParts O H D hD sample gamma common r actor
  obtain ⟨opening,ho⟩ : ∃ opening, parts.opening = AsyncOperation.interface actor opening := ⟨_,rfl⟩
  obtain ⟨closing,hc⟩ : ∃ closing, parts.closing = AsyncOperation.interface actor closing := ⟨_,rfl⟩
  have hs := actual_unprocessed_original_protocol_after_promotions O H D hD sample gamma common r actor earlier hn
  change ownProtocolSignature actor _ = [parts.opening] ++ _ ++ [parts.closing] at hs
  rw [ho,hc] at hs
  obtain ⟨before,interior,future,hlist,hb,hi,hf,hkb,hki,hkf⟩ :=
    actual_two_interface_signature_extract actor _ opening closing _ hs
  refine ⟨before,interior,future,?_,hb,hi,hf,hkb,hkf,?_,?_⟩
  · simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,ho,hc,parts] using hlist
  · intro he
    rw [he] at hki
    exact actual_original_owner_word_nonempty O H D hD sample gamma common r actor hki.symm
  · rw [hki,←actual_own_interior_kernel_list_is_whole_private_word O H D hD sample gamma common r actor]
    exact actual_own_interior_source_K_kernel_all_values O H D hD sample gamma common r actor

/-- The existing algorithm emits exactly one nonempty own K block between
the actual OWN interfaces. Optional before/future blocks carry only the
empty-word identity. All original exterior operations remain once in order. -/
theorem actual_individual_promoted_block_is_true_K (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (earlier : List (BridgeActor T)) (hn : actor ∉ earlier) :
    ∃ before interior future,
      ownerKernels actor before = [] ∧ ownerKernels actor future = [] ∧
      (∀ op ∈ before, InteriorSafe actor op) ∧ (∀ op ∈ interior, InteriorSafe actor op) ∧
      (∀ op ∈ future, InteriorSafe actor op) ∧
      promoteOwnerBlocks actor
        (promoteEveryActor earlier (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)).length
        (promoteEveryActor earlier (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)) =
        emittedSafeBlock actor before ++ [(ownRuntimeParts O H D hD sample gamma common r actor).opening] ++
        [.localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor)] ++
        outsideOperations actor interior ++ [(ownRuntimeParts O H D hD sample gamma common r actor).closing] ++
        emittedSafeBlock actor future := by
  obtain ⟨before,interior,future,hlist,hb,hi,hf,hkb,hkf,hne,hK⟩ :=
    actual_unprocessed_actor_block_admission O H D hD sample gamma common r actor earlier hn
  let parts := ownRuntimeParts O H D hD sample gamma common r actor
  obtain ⟨opening,ho⟩ : ∃ opening, parts.opening = AsyncOperation.interface actor opening := ⟨_,rfl⟩
  obtain ⟨closing,hc⟩ : ∃ closing, parts.closing = AsyncOperation.interface actor closing := ⟨_,rfl⟩
  refine ⟨before,interior,future,hkb,hkf,hb,hi,hf,?_⟩
  rw [hlist]
  change promoteOwnerBlocks actor
    (before ++ [parts.opening] ++ interior ++ [parts.closing] ++ future).length
    (before ++ [parts.opening] ++ interior ++ [parts.closing] ++ future) = _
  rw [ho,hc]
  simp only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
  rw [actual_two_interface_length_fuel_emission actor before interior future hb hi hf]
  have he : emittedSafeBlock actor interior =
      .localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor) :: outsideOperations actor interior := by
    simp only [emittedSafeBlock,if_neg hne,hK]
  rw [he]
  simp only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,ho,hc,parts]

#print axioms actual_individual_promoted_block_is_true_K
end G1CanonicalPromotedBlockTrueK
