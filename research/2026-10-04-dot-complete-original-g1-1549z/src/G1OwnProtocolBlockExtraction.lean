import G1ActualOwnerBlockEmission

/-! Recover the actual own-interface-delimited blocks from the retained
operation signature. These are literal sublists of the existing promoted
program, not supplied abstract lifecycle or source-law equalities. -/
namespace G1OwnProtocolBlockExtraction
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion
open G1OwnProtocolSignatureTransport G1ActualOwnerBlockEmission
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

lemma signature_cons_extract (owner : I) (ops : List (AsyncOperation I S Base))
    (head : AsyncOperation I S Base) (tail : List (AsyncOperation I S Base))
    (he : ownProtocolSignature owner ops = head::tail) :
    ∃ first later, ops = first ++ head::later ∧ ownProtocolSignature owner first = [] ∧
      ownProtocolSignature owner later = tail := by
  induction ops with
  | nil => simp [ownProtocolSignature] at he
  | cons op ops ih =>
    by_cases ho : ownedProtocolOp owner op = true
    · have ht : op = head ∧ ownProtocolSignature owner ops = tail := by
        simpa [ownProtocolSignature,ho] using he
      exact ⟨[],ops,by simp [ht.1],rfl,ht.2⟩
    · have ht : ownProtocolSignature owner ops = head::tail := by
        simpa [ownProtocolSignature,ho] using he
      obtain ⟨first,later,hlist,hfirst,hlater⟩ := ih ht
      refine ⟨op::first,later,?_,?_,hlater⟩
      · simpa only [List.cons_append] using congrArg (List.cons op) hlist
      · change (op::first).filter (ownedProtocolOp owner) = []
        rw [List.filter_cons,if_neg ho]
        exact hfirst

lemma signature_reverse (owner : I) (ops : List (AsyncOperation I S Base)) :
    ownProtocolSignature owner ops.reverse = (ownProtocolSignature owner ops).reverse := by
  simp [ownProtocolSignature]

lemma signature_last_extract (owner : I) (ops tail : List (AsyncOperation I S Base))
    (last : AsyncOperation I S Base) (he : ownProtocolSignature owner ops = tail ++ [last]) :
    ∃ first later, ops = first ++ last::later ∧ ownProtocolSignature owner first = tail ∧
      ownProtocolSignature owner later = [] := by
  have hr : ownProtocolSignature owner ops.reverse = last::tail.reverse := by
    rw [signature_reverse,he]
    simp
  obtain ⟨revLater,revFirst,hl,ha,hb⟩ := signature_cons_extract owner ops.reverse last tail.reverse hr
  refine ⟨revFirst.reverse,revLater.reverse,?_,?_,?_⟩
  · have hs := congrArg List.reverse hl
    simpa using hs
  · rw [signature_reverse,hb,List.reverse_reverse]
  · rw [signature_reverse,ha]; rfl

lemma signature_nil_is_interior_safe (owner : I) (ops : List (AsyncOperation I S Base))
    (hn : ownProtocolSignature owner ops = []) : ∀ op ∈ ops, InteriorSafe owner op := by
  intro op hm
  cases op with
  | localStep other kernel => trivial
  | exterior kernel => trivial
  | interface other kernel =>
    change owner ≠ other
    intro he
    subst other
    have hp : AsyncOperation.interface owner kernel ∈ ownProtocolSignature owner ops :=
      List.mem_filter.mpr ⟨hm,by simp [ownedProtocolOp]⟩
    rw [hn] at hp
    exact List.not_mem_nil hp

lemma signature_locals_is_interior_safe (owner : I) (ops : List (AsyncOperation I S Base))
    (kernels : List (S → PMF S))
    (hn : ownProtocolSignature owner ops = kernels.map (.localStep owner)) :
    ∀ op ∈ ops, InteriorSafe owner op := by
  intro op hm
  cases op with
  | localStep other kernel => trivial
  | exterior kernel => trivial
  | interface other kernel =>
    change owner ≠ other
    intro he
    subst other
    have hp : AsyncOperation.interface owner kernel ∈ ownProtocolSignature owner ops :=
      List.mem_filter.mpr ⟨hm,by simp [ownedProtocolOp]⟩
    rw [hn] at hp
    obtain ⟨old,_,he⟩ := List.mem_map.mp hp
    cases he

lemma owner_kernels_mapped_own (owner : I) (kernels : List (S → PMF S)) :
    ownerKernels owner (Base := Base) (kernels.map (.localStep owner)) = kernels := by
  induction kernels with
  | nil => rfl
  | cons k ks ih => simp [ownerKernels,ih]

/-- The retained exact signature DERIVES all literal blocks, their complete
kernel lists and the physical no-own-interface admission used by promotion. -/
theorem actual_two_interface_signature_extract (owner : I) (ops : List (AsyncOperation I S Base))
    (opening closing : Base × S → PMF (Base × S)) (kernels : List (S → PMF S))
    (hs : ownProtocolSignature owner ops = [.interface owner opening] ++
      kernels.map (.localStep owner) ++ [.interface owner closing]) :
    ∃ before interior future,
      ops = before ++ .interface owner opening :: (interior ++ .interface owner closing :: future) ∧
      (∀ op ∈ before, InteriorSafe owner op) ∧ (∀ op ∈ interior, InteriorSafe owner op) ∧
      (∀ op ∈ future, InteriorSafe owner op) ∧
      ownerKernels owner before = [] ∧ ownerKernels owner interior = kernels ∧ ownerKernels owner future = [] := by
  have hfirst : ownProtocolSignature owner ops = .interface owner opening ::
      (kernels.map (.localStep owner) ++ [.interface owner closing]) := by simpa using hs
  obtain ⟨before,later,hb,hbefore,hlater⟩ := signature_cons_extract owner ops _ _ hfirst
  obtain ⟨interior,future,hi,hinterior,hfuture⟩ := signature_last_extract owner later _ _ hlater
  refine ⟨before,interior,future,by rw [hb,hi],signature_nil_is_interior_safe owner before hbefore,
    signature_locals_is_interior_safe owner interior kernels hinterior,
    signature_nil_is_interior_safe owner future hfuture,?_,?_,?_⟩
  · rw [←owner_kernels_from_protocol_signature,hbefore]; rfl
  · rw [←owner_kernels_from_protocol_signature,hinterior,owner_kernels_mapped_own]
  · rw [←owner_kernels_from_protocol_signature,hfuture]; rfl

#print axioms actual_two_interface_signature_extract
end G1OwnProtocolBlockExtraction
