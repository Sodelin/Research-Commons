import G1PendingActorInterfaceCommutation

/-! Finite asynchronous promotion of a whole private actor word to one
pending output kernel. Other actor opens/closes may cross its interval; only
the selected actor's own interface reads are excluded from its interior.
Full exterior/history state is preserved. -/
namespace G1FinitePendingActorPromotion
open G1PendingActorInterfaceCommutation
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

noncomputable def actorWordKernel : List (S → PMF S) → S → PMF S
  | [],value => PMF.pure value
  | kernel::kernels,value => (kernel value).bind (actorWordKernel kernels)

noncomputable def pendingWordStep (owner : I) (kernels : List (S → PMF S)) :
    Base × (I → S) → PMF (Base × (I → S)) :=
  asyncStep (.localStep owner (actorWordKernel kernels))

def ownerKernels (owner : I) : List (AsyncOperation I S Base) → List (S → PMF S)
  | [] => []
  | .localStep other kernel::ops => if owner = other then kernel::ownerKernels owner ops else ownerKernels owner ops
  | _::ops => ownerKernels owner ops

def outsideOperations (owner : I) : List (AsyncOperation I S Base) → List (AsyncOperation I S Base)
  | [] => []
  | (.localStep other kernel)::ops => if owner = other then outsideOperations owner ops
      else (.localStep other kernel)::outsideOperations owner ops
  | op::ops => op::outsideOperations owner ops

def InteriorSafe (owner : I) : AsyncOperation I S Base → Prop
  | .localStep _ _ => True
  | .interface other _ => owner ≠ other
  | .exterior _ => True

lemma actual_own_kernel_composition (owner : I) (first last : S → PMF S) (state : Base × (I → S)) :
    (asyncStep (.localStep owner first) state).bind (asyncStep (.localStep owner last)) =
      asyncStep (.localStep owner (fun value => (first value).bind last)) state := by
  simp only [asyncStep,PMF.bind_map,Function.comp_def,Function.update_self]
  rw [PMF.map_bind]
  congr 1
  funext firstValue
  simp only [PMF.map_comp,Function.comp_def,Function.update_idem]

lemma actual_safe_prepend_promotion (owner : I) (op : AsyncOperation I S Base)
    (hsafe : SafeFor owner op) (kernels : List (S → PMF S))
    (outside : List (AsyncOperation I S Base)) (state : Base × (I → S)) :
    (asyncStep op state).bind (fun next => (pendingWordStep owner kernels next).bind (asyncProgram outside)) =
      (pendingWordStep owner kernels state).bind (asyncProgram (op::outside)) := by
  change (asyncStep op state).bind (fun next =>
      (asyncStep (.localStep owner (actorWordKernel kernels)) next).bind (asyncProgram outside)) = _
  rw [←PMF.bind_bind,←private_commutes_safe_interface owner (actorWordKernel kernels) op hsafe state]
  simp only [pendingWordStep,asyncProgram,PMF.bind_bind]

/-- Entire finite private words fuse to one kernel at the actor's opening,
without reprocessing any exterior operation or observing a future actor output
before its own interface. Crossing other actors are permitted. -/
theorem actual_finite_pending_actor_promotion (owner : I) (ops : List (AsyncOperation I S Base))
    (hsafe : ∀ op ∈ ops, InteriorSafe owner op) (state : Base × (I → S)) :
    asyncProgram ops state =
      (pendingWordStep owner (ownerKernels owner ops) state).bind
        (asyncProgram (outsideOperations owner ops)) := by
  induction ops generalizing state with
  | nil =>
      simp [asyncProgram,pendingWordStep,ownerKernels,outsideOperations,actorWordKernel,
        asyncStep,PMF.pure_map,Function.update_eq_self]
  | cons op ops ih =>
      have ht : ∀ q ∈ ops, InteriorSafe owner q := fun q hq => hsafe q (List.mem_cons_of_mem op hq)
      have htail : asyncProgram ops = fun next =>
          (pendingWordStep owner (ownerKernels owner ops) next).bind
            (asyncProgram (outsideOperations owner ops)) := funext (ih ht)
      cases op with
      | localStep other kernel =>
          by_cases ho : owner = other
          · subst other
            simp only [asyncProgram,ownerKernels,outsideOperations,if_pos rfl]
            rw [htail]
            rw [←PMF.bind_bind]
            congr 1
            exact actual_own_kernel_composition owner kernel (actorWordKernel (ownerKernels owner ops)) state
          · simp only [asyncProgram,ownerKernels,outsideOperations,if_neg ho]
            rw [htail]
            exact actual_safe_prepend_promotion owner (.localStep other kernel) ho _ _ state
      | interface other kernel =>
          have ho : owner ≠ other := hsafe (.interface other kernel) (by simp)
          simp only [asyncProgram,ownerKernels,outsideOperations]
          rw [htail]
          exact actual_safe_prepend_promotion owner (.interface other kernel) ho _ _ state
      | exterior kernel =>
          simp only [asyncProgram,ownerKernels,outsideOperations]
          rw [htail]
          exact actual_safe_prepend_promotion owner (.exterior kernel) trivial _ _ state

/-- Arbitrary later interaction may read the newly exposed full actor output.
The SAME continuation sees the identical full joint law. -/
theorem actual_pending_actor_same_continuation {Obs : Type*} (owner : I)
    (ops : List (AsyncOperation I S Base)) (hsafe : ∀ op ∈ ops, InteriorSafe owner op)
    (state : Base × (I → S)) (future : Base × (I → S) → PMF Obs) :
    (asyncProgram ops state).bind future =
      ((pendingWordStep owner (ownerKernels owner ops) state).bind
        (asyncProgram (outsideOperations owner ops))).bind future := by
  rw [actual_finite_pending_actor_promotion owner ops hsafe state]

#print axioms actual_finite_pending_actor_promotion
end G1FinitePendingActorPromotion
