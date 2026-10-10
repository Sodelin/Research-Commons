import G1ActualCrossingSourcePendingFusion

/-! Finite private-actor schedule commutation. Distinct actor computations
commute even across arbitrary interleavings. This algebra is the scheduler
layer; canonical original-source operation admission is separate. -/
namespace G1FiniteActorScheduleCommutation
open scoped Classical
variable {I S : Type*} [DecidableEq I]

structure ActorOperation (I S : Type*) where
  owner : I
  kernel : S → PMF S

noncomputable def actorStep (op : ActorOperation I S) (state : I → S) : PMF (I → S) :=
  (op.kernel (state op.owner)).map (fun value => Function.update state op.owner value)

/-- Actual private kernels depend only on their own actor coordinate; the
commutation law is derived from product sampling, not supplied as a field. -/
theorem distinct_actor_steps_commute (left right : ActorOperation I S)
    (hne : left.owner ≠ right.owner) (state : I → S) :
    (actorStep left state).bind (actorStep right) = (actorStep right state).bind (actorStep left) := by
  simp only [actorStep,PMF.bind_map,PMF.map_bind,Function.comp_def]
  simp only [Function.update_of_ne hne,Function.update_of_ne hne.symm]
  simp only [PMF.map,Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext rightValue
  congr 1
  funext leftValue
  congr 1
  exact Function.update_comm hne leftValue rightValue state

noncomputable def actorProgram : List (ActorOperation I S) → (I → S) → PMF (I → S)
  | [],state => PMF.pure state
  | op::ops,state => (actorStep op state).bind (actorProgram ops)

lemma actor_program_append (first last : List (ActorOperation I S)) (state : I → S) :
    actorProgram (first ++ last) state = (actorProgram first state).bind (actorProgram last) := by
  induction first generalizing state with
  | nil => simp [actorProgram,PMF.pure_bind]
  | cons op ops ih =>
      simp only [List.cons_append,actorProgram,PMF.bind_bind]
      congr 1
      funext next
      exact ih next

/-- A physical schedule move exchanges adjacent DISTINCT owners and leaves
all their private kernels and their own relative instruction order unchanged. -/
inductive ScheduleSwap : List (ActorOperation I S) → List (ActorOperation I S) → Prop
  | exchange (before after : List (ActorOperation I S)) (left right : ActorOperation I S)
      (hne : left.owner ≠ right.owner) :
      ScheduleSwap (before ++ left::right::after) (before ++ right::left::after)

theorem actual_schedule_swap_preserves_actor_law {first last : List (ActorOperation I S)}
    (hswap : ScheduleSwap first last) (state : I → S) : actorProgram first state = actorProgram last state := by
  cases hswap with
  | exchange before after left right hne =>
      rw [actor_program_append,actor_program_append]
      congr 1
      funext entering
      simp only [actorProgram,←PMF.bind_bind]
      rw [distinct_actor_steps_commute left right hne entering]

theorem actual_finite_actor_schedule_equivalence {first last : List (ActorOperation I S)}
    (schedule : Relation.ReflTransGen ScheduleSwap first last) (state : I → S) :
    actorProgram first state = actorProgram last state := by
  induction schedule with
  | refl => rfl
  | tail prior step ih => exact ih.trans (actual_schedule_swap_preserves_actor_law step state)

#print axioms actual_finite_actor_schedule_equivalence
end G1FiniteActorScheduleCommutation
