import G1CanonicalPromotedBlockTrueK

/-! EVERY original bridge in the same finite promoted interpreter carries
exactly its actual K row between its unchanged opening/release interfaces.
Later crossing actors preserve it. Extra outside blocks are pure identities. -/
namespace G1AllOriginalPromotedKLabels
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalOwnTwoInterfaceRuntime G1CanonicalPromotedBlockTrueK
open G1CanonicalPendingTrueKExposure G1CanonicalInitializedWholeCalendarHistory
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open G1OwnProtocolSignatureTransport G1ActualOwnerBlockEmission G1PendingBaseCheckpointRecorder G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma signature_own_outside_safe {I S Base : Type*} [DecidableEq I] (owner : I)
    (ops : List (AsyncOperation I S Base)) (hs : ∀ op ∈ ops, InteriorSafe owner op) :
    ownProtocolSignature owner (outsideOperations owner ops) = [] := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    have ho := hs op List.mem_cons_self
    have ht := ih (fun q hq => hs q (List.mem_cons_of_mem op hq))
    simp only [ownProtocolSignature] at ht
    cases op with
    | localStep other kernel =>
      by_cases he : owner = other
      · simp only [outsideOperations,if_pos he,ownProtocolSignature]
        exact ht
      · simp [outsideOperations,he,ownProtocolSignature,ownedProtocolOp,ht]
    | interface other kernel =>
      change owner ≠ other at ho
      simp [outsideOperations,ownProtocolSignature,ownedProtocolOp,ho,ht]
    | exterior kernel => simp [outsideOperations,ownProtocolSignature,ownedProtocolOp,ht]

lemma signature_empty_emitted_block {I S Base : Type*} [DecidableEq I] (owner : I)
    (ops : List (AsyncOperation I S Base)) (hs : ∀ op ∈ ops, InteriorSafe owner op)
    (hk : ownerKernels owner ops = []) :
    ownProtocolSignature owner (emittedSafeBlock owner ops) = [] ∨
      ownProtocolSignature owner (emittedSafeBlock owner ops) = [.localStep owner (actorWordKernel [])] := by
  by_cases he : ops = []
  · left; simp [emittedSafeBlock,he,ownProtocolSignature]
  · right
    rw [emittedSafeBlock,if_neg he,hk]
    have ht := signature_own_outside_safe owner ops hs
    simp only [ownProtocolSignature] at ht
    simp [ownProtocolSignature,ownedProtocolOp,ht]

lemma promote_every_actor_append {I S Base : Type*} [DecidableEq I] (first last : List I)
    (ops : List (AsyncOperation I S Base)) :
    promoteEveryActor (first ++ last) ops = promoteEveryActor last (promoteEveryActor first ops) := by
  induction first generalizing ops with
  | nil => rfl
  | cons owner first ih => simpa only [List.cons_append,promoteEveryActor] using ih (promoteOwnerBlocks owner ops.length ops)

lemma actor_mem_list_split {I : Type*} (actor : I) (actors : List I) (hm : actor ∈ actors) :
    ∃ first last, actors = first ++ actor::last := by
  induction actors with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons other actors ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst other; exact ⟨[],actors,rfl⟩
    · obtain ⟨first,last,he⟩ := ih hm
      exact ⟨other::first,last,by simpa only [List.cons_append] using congrArg (List.cons other) he⟩

/-- No actor label is lost or split by arbitrary later crossing promotions.
For every original actor, the FINAL SAME interpreter contains exactly its
true K row between its literal own interfaces, up to outside identity rows. -/
theorem actual_every_original_promoted_actor_has_true_K (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actors : List (BridgeActor T)) (hn : actors.Nodup) (actor : BridgeActor T) (hm : actor ∈ actors) :
    ∃ left right,
      (left = [] ∨ left = [.localStep actor (actorWordKernel [])]) ∧
      (right = [] ∨ right = [.localStep actor (actorWordKernel [])]) ∧
      ownProtocolSignature actor (promoteEveryActor actors
        (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)) =
        left ++ [(ownRuntimeParts O H D hD sample gamma common r actor).opening] ++
        [.localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor)] ++
        [(ownRuntimeParts O H D hD sample gamma common r actor).closing] ++ right := by
  obtain ⟨earlier,later,he⟩ := actor_mem_list_split actor actors hm
  rw [he] at hn
  have hd := List.nodup_append.mp hn
  have hb : actor ∉ earlier := fun ha => hd.2.2 actor ha actor List.mem_cons_self rfl
  have ht : actor ∉ later := (List.nodup_cons.mp hd.2.1).1
  obtain ⟨before,interior,future,hkb,hkf,hsb,hsi,hsf,hstep⟩ :=
    actual_individual_promoted_block_is_true_K O H D hD sample gamma common r actor earlier hb
  let left := ownProtocolSignature actor (emittedSafeBlock actor before)
  let right := ownProtocolSignature actor (emittedSafeBlock actor future)
  refine ⟨left,right,signature_empty_emitted_block actor before hsb hkb,
    signature_empty_emitted_block actor future hsf hkf,?_⟩
  rw [he,promote_every_actor_append]
  change ownProtocolSignature actor (promoteEveryActor later (promoteOwnerBlocks actor
    (promoteEveryActor earlier (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)).length
    (promoteEveryActor earlier (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)))) = _
  rw [actual_other_finite_promotions_preserve_own_protocol actor later ht,hstep]
  simp only [own_signature_append]
  rw [signature_own_outside_safe actor interior hsi]
  simp [ownProtocolSignature,ownedProtocolOp,ownRuntimeParts,historyLift,left,right]

/-- The complete original finite bridge set instantiates the label theorem;
neither a selected subset nor a bound on old descendant leaves is supplied. -/
theorem actual_all_original_bridge_K_labels (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) :
    ∃ left right,
      (left = [] ∨ left = [.localStep actor (actorWordKernel [])]) ∧
      (right = [] ∨ right = [.localStep actor (actorWordKernel [])]) ∧
      ownProtocolSignature actor (promoteEveryActor (Finset.univ.toList)
        (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)) =
        left ++ [(ownRuntimeParts O H D hD sample gamma common r actor).opening] ++
        [.localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor)] ++
        [(ownRuntimeParts O H D hD sample gamma common r actor).closing] ++ right := by
  exact actual_every_original_promoted_actor_has_true_K O H D hD sample gamma common r
    Finset.univ.toList (Finset.nodup_toList _) actor (Finset.mem_toList.mpr (Finset.mem_univ _))

#print axioms actual_every_original_promoted_actor_has_true_K
end G1AllOriginalPromotedKLabels
