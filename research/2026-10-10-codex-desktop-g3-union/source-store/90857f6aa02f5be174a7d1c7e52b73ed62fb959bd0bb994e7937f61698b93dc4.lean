import G1AllOriginalPromotedKLabels

/-! The EXISTING all-actor interpreter commutes with recording every actual
interface output. Private K rows and their own opening/release signature are
unchanged; all recorded entering values remain in the joint causal law. -/
namespace G1ExactPromotionInterfaceRecordLift
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open G1PendingInterfaceEntryRecorder G1OwnProtocolSignatureTransport
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

lemma recorded_interior_safe_iff (owner : I) (op : AsyncOperation I S Base) :
    InteriorSafe owner (interfaceRecordingLift op) ↔ InteriorSafe owner op := by cases op <;> rfl

lemma recorded_owned_op (owner : I) (op : AsyncOperation I S Base) :
    ownedProtocolOp owner (interfaceRecordingLift op) = ownedProtocolOp owner op := by cases op <;> rfl

lemma recorded_signature (owner : I) (ops : List (AsyncOperation I S Base)) :
    ownProtocolSignature owner (ops.map interfaceRecordingLift) =
      (ownProtocolSignature owner ops).map interfaceRecordingLift := by
  unfold ownProtocolSignature
  rw [List.filter_map]
  have he : (ownedProtocolOp owner) ∘ (interfaceRecordingLift (I := I) (S := S) (Base := Base)) =
      ownedProtocolOp owner := funext (recorded_owned_op owner)
  rw [he]

lemma recorded_outside_operations (owner : I) (ops : List (AsyncOperation I S Base)) :
    outsideOperations owner (ops.map interfaceRecordingLift) =
      (outsideOperations owner ops).map interfaceRecordingLift := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | localStep other kernel =>
      by_cases he : owner = other
      · simp only [List.map_cons,interfaceRecordingLift,outsideOperations,if_pos he]
        exact ih
      · simp only [List.map_cons,interfaceRecordingLift,outsideOperations,if_neg he]
        rw [ih]
    | interface other kernel => simp [outsideOperations,interfaceRecordingLift,ih]
    | exterior kernel => simp [outsideOperations,interfaceRecordingLift,ih]

lemma recorded_take_safe (owner : I) (ops : List (AsyncOperation I S Base)) :
    (ops.map interfaceRecordingLift).takeWhile (fun q => decide (InteriorSafe owner q)) =
      (ops.takeWhile (fun q => decide (InteriorSafe owner q))).map interfaceRecordingLift := by
  rw [List.takeWhile_map]
  have he : (fun q => decide (InteriorSafe owner q)) ∘ (interfaceRecordingLift (I := I) (S := S) (Base := Base)) =
      (fun q => decide (InteriorSafe owner q)) := by
    funext q; rw [Function.comp_apply,recorded_interior_safe_iff]
  rw [he]

lemma recorded_drop_safe (owner : I) (ops : List (AsyncOperation I S Base)) :
    (ops.map interfaceRecordingLift).dropWhile (fun q => decide (InteriorSafe owner q)) =
      (ops.dropWhile (fun q => decide (InteriorSafe owner q))).map interfaceRecordingLift := by
  rw [List.dropWhile_map]
  have he : (fun q => decide (InteriorSafe owner q)) ∘ (interfaceRecordingLift (I := I) (S := S) (Base := Base)) =
      (fun q => decide (InteriorSafe owner q)) := by
    funext q; rw [Function.comp_apply,recorded_interior_safe_iff]
  rw [he]

/-- Literal promotion itself, rather than only its endpoint marginal, is
compatible with EVERY genuine interface-output record. -/
theorem actual_owner_promotion_record_lift (owner : I) (fuel : ℕ) (ops : List (AsyncOperation I S Base)) :
    promoteOwnerBlocks owner fuel (ops.map interfaceRecordingLift) =
      (promoteOwnerBlocks owner fuel ops).map interfaceRecordingLift := by
  induction fuel generalizing ops with
  | zero => rfl
  | succ fuel ih =>
    cases ops with
    | nil => rfl
    | cons op ops =>
      by_cases hs : InteriorSafe owner op
      · have hr : InteriorSafe owner (interfaceRecordingLift op) := (recorded_interior_safe_iff owner op).mpr hs
        rw [List.map_cons,promoteOwnerBlocks,if_pos hr,promoteOwnerBlocks,if_pos hs]
        have ht := recorded_take_safe owner (op::ops)
        have hd := recorded_drop_safe owner (op::ops)
        simp only [List.map_cons] at ht hd
        simp only [ht,hd]
        simp only [owner_kernels_entry_record_lift,recorded_outside_operations,ih,
          List.map_cons,List.map_append,interfaceRecordingLift]
      · have hr : ¬InteriorSafe owner (interfaceRecordingLift op) := fun hh => hs ((recorded_interior_safe_iff owner op).mp hh)
        rw [List.map_cons,promoteOwnerBlocks,if_neg hr,promoteOwnerBlocks,if_neg hs]
        simp only [List.map_cons,ih]

theorem actual_every_actor_promotion_record_lift (owners : List I) (ops : List (AsyncOperation I S Base)) :
    promoteEveryActor owners (ops.map interfaceRecordingLift) =
      (promoteEveryActor owners ops).map interfaceRecordingLift := by
  induction owners generalizing ops with
  | nil => rfl
  | cons owner owners ih =>
    simp only [promoteEveryActor,List.length_map]
    rw [actual_owner_promotion_record_lift,ih]

#print axioms actual_every_actor_promotion_record_lift
end G1ExactPromotionInterfaceRecordLift
