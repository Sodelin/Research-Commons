import G1ActualOwnPendingKReplacement

/-! Other-actor promotion preserves the exact OWN interface/private-kernel
signature. This is the finite protocol invariant needed to repeat canonical
true-K substitution when arbitrary bridge lifetimes overlap. -/
namespace G1OwnProtocolSignatureTransport
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

def ownedProtocolOp (owner : I) : AsyncOperation I S Base → Bool
  | .localStep other _ => decide (owner = other)
  | .interface other _ => decide (owner = other)
  | .exterior _ => false

def ownProtocolSignature (owner : I) (ops : List (AsyncOperation I S Base)) := ops.filter (ownedProtocolOp owner)

lemma own_signature_append (owner : I) (first last : List (AsyncOperation I S Base)) :
    ownProtocolSignature owner (first ++ last) = ownProtocolSignature owner first ++ ownProtocolSignature owner last :=
  List.filter_append first last

lemma own_signature_other_local (owner other : I) (hne : owner ≠ other) (kernel : S → PMF S)
    (ops : List (AsyncOperation I S Base)) :
    ownProtocolSignature owner (.localStep other kernel :: ops) = ownProtocolSignature owner ops := by
  simp [ownProtocolSignature,ownedProtocolOp,hne]

lemma own_signature_other_outside (owner other : I) (hne : owner ≠ other) (ops : List (AsyncOperation I S Base)) :
    ownProtocolSignature owner (outsideOperations other ops) = ownProtocolSignature owner ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    simp only [ownProtocolSignature] at ih
    cases op with
    | localStep current kernel =>
      by_cases ho : other = current
      · subst current
        simp [outsideOperations,ownProtocolSignature,ownedProtocolOp,hne,ih]
      · simp only [outsideOperations,if_neg ho,ownProtocolSignature,List.filter_cons]
        cases ownedProtocolOp owner (.localStep current kernel) <;> simp [ih]
    | interface current kernel =>
      simp only [outsideOperations,ownProtocolSignature,List.filter_cons]
      cases ownedProtocolOp owner (.interface current kernel) <;> simp [ih]
    | exterior kernel =>
      simpa only [outsideOperations,ownProtocolSignature,List.filter_cons,ownedProtocolOp,Bool.false_eq_true,if_false] using ih

/-- Promoting ANY other finite actor leaves this actor's exact private source
kernel order and original opening/release interface functions unchanged. -/
theorem actual_other_actor_promotion_preserves_own_protocol (owner other : I) (hne : owner ≠ other)
    (fuel : Nat) (ops : List (AsyncOperation I S Base)) :
    ownProtocolSignature owner (promoteOwnerBlocks other fuel ops) = ownProtocolSignature owner ops := by
  induction fuel generalizing ops with
  | zero => rfl
  | succ fuel ih =>
    cases ops with
    | nil => rfl
    | cons op ops =>
      by_cases hs : InteriorSafe other op
      · let chunk := (op::ops).takeWhile (fun q => decide (InteriorSafe other q))
        let later := (op::ops).dropWhile (fun q => decide (InteriorSafe other q))
        have he : op::ops = chunk ++ later :=
          (List.takeWhile_append_dropWhile (p := fun q => decide (InteriorSafe other q)) (l := op::ops)).symm
        rw [promoteOwnerBlocks,if_pos hs]
        change ownProtocolSignature owner (.localStep other (actorWordKernel (ownerKernels other chunk)) ::
          (outsideOperations other chunk ++ promoteOwnerBlocks other fuel later)) = _
        rw [own_signature_other_local owner other hne,own_signature_append,
          own_signature_other_outside owner other hne chunk,ih,he,own_signature_append]
      · rw [promoteOwnerBlocks,if_neg hs]
        change ownProtocolSignature owner (op :: promoteOwnerBlocks other fuel ops) = _
        have hi := ih ops
        simp only [ownProtocolSignature] at hi
        simp only [ownProtocolSignature,List.filter_cons]
        cases ownedProtocolOp owner op <;> simp [hi]

lemma owner_kernels_from_protocol_signature (owner : I) (ops : List (AsyncOperation I S Base)) :
    ownerKernels owner (ownProtocolSignature owner ops) = ownerKernels owner ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    simp only [ownProtocolSignature] at ih
    cases op with
    | localStep other kernel =>
      by_cases he : owner = other
      · subst other; simp [ownProtocolSignature,ownedProtocolOp,ownerKernels,ih]
      · simp [ownProtocolSignature,ownedProtocolOp,ownerKernels,he,ih]
    | interface other kernel =>
      by_cases he : owner = other
      · subst other; simp [ownProtocolSignature,ownedProtocolOp,ownerKernels,ih]
      · simp [ownProtocolSignature,ownedProtocolOp,ownerKernels,he,ih]
    | exterior kernel => simpa [ownProtocolSignature,ownedProtocolOp,ownerKernels] using ih

/-- The entire ORIGINAL private word of an unprocessed actor survives all
earlier OTHER actor promotions. It is not refitted or shortened by overlaps. -/
theorem actual_other_actor_promotion_preserves_own_kernel_list (owner other : I) (hne : owner ≠ other)
    (fuel : Nat) (ops : List (AsyncOperation I S Base)) :
    ownerKernels owner (promoteOwnerBlocks other fuel ops) = ownerKernels owner ops := by
  rw [←owner_kernels_from_protocol_signature,actual_other_actor_promotion_preserves_own_protocol owner other hne,
    owner_kernels_from_protocol_signature]

theorem actual_other_finite_promotions_preserve_own_protocol (owner : I) (owners : List I)
    (hn : owner ∉ owners) (ops : List (AsyncOperation I S Base)) :
    ownProtocolSignature owner (promoteEveryActor owners ops) = ownProtocolSignature owner ops := by
  induction owners generalizing ops with
  | nil => rfl
  | cons other owners ih =>
    have hne : owner ≠ other := fun he => hn (List.mem_cons.mpr (Or.inl he))
    rw [promoteEveryActor,ih (fun hm => hn (List.mem_cons_of_mem other hm)),
      actual_other_actor_promotion_preserves_own_protocol owner other hne]

#print axioms actual_other_actor_promotion_preserves_own_protocol
#print axioms actual_other_finite_promotions_preserve_own_protocol
end G1OwnProtocolSignatureTransport
