import G1CanonicalOriginalAdjacentSourceSupport
import Mathlib.Data.List.TakeWhile

/-! A concrete finite ALL-actor promotion algorithm. It fuses each private
word only inside blocks between that actor's own interfaces. This preserves
all original base/history coordinates; actual compiler/K admission is separate. -/
namespace G1WholeFinitePendingPromotion
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

noncomputable def promoteOwnerBlocks (owner : I) : Nat → List (AsyncOperation I S Base) → List (AsyncOperation I S Base)
  | 0,ops => ops
  | _+1,[] => []
  | fuel+1,op::ops =>
      if InteriorSafe owner op then
        let chunk := (op::ops).takeWhile (fun q => decide (InteriorSafe owner q))
        let later := (op::ops).dropWhile (fun q => decide (InteriorSafe owner q))
        .localStep owner (actorWordKernel (ownerKernels owner chunk)) ::
          (outsideOperations owner chunk ++ promoteOwnerBlocks owner fuel later)
      else op :: promoteOwnerBlocks owner fuel ops

/-- Concrete interface-delimited promotion preserves the entire joint runtime
law for every fuel and every actual operation list. An actor's own interface
is never moved or crossed; the SAME future may observe all exposed outputs. -/
theorem actual_owner_block_promotion_row (owner : I) (fuel : Nat) (ops : List (AsyncOperation I S Base))
    (state : Base × (I → S)) :
    asyncProgram ops state = asyncProgram (promoteOwnerBlocks owner fuel ops) state := by
  induction fuel generalizing ops state with
  | zero => rfl
  | succ fuel ih =>
    cases ops with
    | nil => rfl
    | cons op ops =>
      by_cases hs : InteriorSafe owner op
      · let chunk := (op::ops).takeWhile (fun q => decide (InteriorSafe owner q))
        let later := (op::ops).dropWhile (fun q => decide (InteriorSafe owner q))
        have hc : ∀ q ∈ chunk, InteriorSafe owner q := by
          intro q hq
          exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun q => decide (InteriorSafe owner q)) (l := op::ops) hq)
        have he : op::ops = chunk ++ later := (List.takeWhile_append_dropWhile (p := fun q => decide (InteriorSafe owner q)) (l := op::ops)).symm
        have hf : asyncProgram later = asyncProgram (promoteOwnerBlocks owner fuel later) := funext (ih later)
        calc
          _ = (asyncProgram chunk state).bind (asyncProgram later) := by rw [he,async_program_append]
          _ = (pendingWordStep owner (ownerKernels owner chunk) state).bind
              (asyncProgram (outsideOperations owner chunk ++ later)) := by
            rw [actual_finite_pending_actor_promotion owner chunk hc state]
            simp only [PMF.bind_bind]
            congr 1
            funext next
            exact (async_program_append _ _ _).symm
          _ = (pendingWordStep owner (ownerKernels owner chunk) state).bind
              (asyncProgram (outsideOperations owner chunk ++ promoteOwnerBlocks owner fuel later)) := by
            congr 1
            funext next
            rw [async_program_append,async_program_append,hf]
          _ = _ := by simp only [promoteOwnerBlocks,if_pos hs,asyncProgram,pendingWordStep]; rfl
      · simp only [promoteOwnerBlocks,if_neg hs,asyncProgram]
        congr 1
        exact funext (ih ops)

noncomputable def promoteEveryActor : List I → List (AsyncOperation I S Base) → List (AsyncOperation I S Base)
  | [],ops => ops
  | owner::owners,ops => promoteEveryActor owners (promoteOwnerBlocks owner ops.length ops)

/-- Arbitrary finite many-actor promotion is one concrete interpreter, not a
supplied source-law equality. Every original operation is processed once and
all joint base/history and exposed actor state laws are preserved. -/
theorem actual_every_actor_promotion_row (owners : List I) (ops : List (AsyncOperation I S Base))
    (state : Base × (I → S)) :
    asyncProgram ops state = asyncProgram (promoteEveryActor owners ops) state := by
  induction owners generalizing ops with
  | nil => rfl
  | cons owner owners ih =>
    exact (actual_owner_block_promotion_row owner ops.length ops state).trans (ih _)

/-- Any SAME completion/history continuation sees precisely the preserved
whole joint row. Actual source compiler/K-label instantiation remains needed. -/
theorem actual_every_actor_promotion_same_continuation {Obs : Type*}
    (owners : List I) (ops : List (AsyncOperation I S Base))
    (state : Base × (I → S)) (future : Base × (I → S) → PMF Obs) :
    (asyncProgram ops state).bind future = (asyncProgram (promoteEveryActor owners ops) state).bind future := by
  rw [actual_every_actor_promotion_row]

#print axioms actual_every_actor_promotion_row
end G1WholeFinitePendingPromotion
