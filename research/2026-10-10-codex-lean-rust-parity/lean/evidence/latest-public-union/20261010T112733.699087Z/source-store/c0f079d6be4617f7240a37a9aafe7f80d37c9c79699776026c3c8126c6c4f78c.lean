import G1CanonicalPartialBatchRootObserver

/-! A concrete checkpoint recorder extends the pending ORIGINAL base with
chronological observations. Private kernels cannot read recorded history or
cached other coordinates. The finite pending algebra preserves the whole
joint history when it promotes genuine local computations. -/
namespace G1PendingBaseCheckpointRecorder
open G1PendingActorInterfaceCommutation G1WholeFinitePendingPromotion
open scoped Classical
variable {I S Base Obs : Type*} [DecidableEq I]

noncomputable def withBaseHistory (history : List Obs) (state : Base × (I → S)) :
    (Base × List Obs) × (I → S) := ((state.1,history),state.2)

noncomputable def historyLift : AsyncOperation I S Base → AsyncOperation I S (Base × List Obs)
  | .localStep owner kernel => .localStep owner kernel
  | .interface owner kernel => .interface owner (fun value =>
      (kernel (value.1.1,value.2)).map (fun next => ((next.1,value.1.2),next.2)))
  | .exterior kernel => .exterior (fun value => (kernel value.1).map (fun next => (next,value.2)))

lemma actual_history_lift_step (op : AsyncOperation I S Base) (history : List Obs) (state : Base × (I → S)) :
    (asyncStep op state).map (withBaseHistory history) =
      asyncStep (historyLift op) (withBaseHistory history state) := by
  cases op <;> simp only [historyLift,asyncStep,withBaseHistory,PMF.map_comp,Function.comp_def]

lemma actual_history_lift_program (ops : List (AsyncOperation I S Base)) (history : List Obs) (state : Base × (I → S)) :
    (asyncProgram ops state).map (withBaseHistory history) =
      asyncProgram (ops.map historyLift) (withBaseHistory history state) := by
  induction ops generalizing state with
  | nil => simp [asyncProgram,PMF.pure_map]
  | cons op ops ih =>
    simp only [asyncProgram,List.map_cons,PMF.map_bind]
    simp_rw [ih]
    rw [←actual_history_lift_step,PMF.bind_map]; rfl

noncomputable def recordBaseCheckpoint (observer : Base → Obs) : AsyncOperation I S (Base × List Obs) :=
  .exterior (fun value => PMF.pure (value.1,value.2 ++ [observer value.1]))

lemma actual_record_base_checkpoint (observer : Base → Obs) (history : List Obs) (state : Base × (I → S)) :
    asyncStep (recordBaseCheckpoint observer) (withBaseHistory history state) =
      PMF.pure (withBaseHistory (history ++ [observer state.1]) state) := by
  simp [recordBaseCheckpoint,asyncStep,withBaseHistory,PMF.pure_map]

noncomputable def recordedBlock (observer : Base → Obs) (ops : List (AsyncOperation I S Base)) :
    List (AsyncOperation I S (Base × List Obs)) := ops.map historyLift ++ [recordBaseCheckpoint observer]

/-- One real source event may consist of several concrete pending operations,
including its immediate close. Recording after the block keeps the entire
old history and adds exactly that original post-event base observation. -/
lemma actual_recorded_block_row (observer : Base → Obs) (ops : List (AsyncOperation I S Base))
    (history : List Obs) (state : Base × (I → S)) :
    (asyncProgram ops state).map (fun next => withBaseHistory (history ++ [observer next.1]) next) =
      asyncProgram (recordedBlock observer ops) (withBaseHistory history state) := by
  rw [recordedBlock,async_program_append,←actual_history_lift_program,PMF.bind_map]
  simp only [Function.comp_def,asyncProgram,PMF.bind_pure,actual_record_base_checkpoint]
  rfl

/-- Arbitrary-many actor promotion preserves the ENTIRE recorded checkpoint
trajectory, together with all exposed coordinates and the SAME continuation.
This is applied only after actual source/event admissions are proved. -/
theorem actual_recorded_pending_promotion_same_future {Result : Type*}
    (owners : List I) (ops : List (AsyncOperation I S (Base × List Obs)))
    (state : (Base × List Obs) × (I → S)) (future : (Base × List Obs) × (I → S) → PMF Result) :
    (asyncProgram ops state).bind future =
      (asyncProgram (promoteEveryActor owners ops) state).bind future :=
  actual_every_actor_promotion_same_continuation owners ops state future

#print axioms actual_recorded_block_row
#print axioms actual_recorded_pending_promotion_same_future
end G1PendingBaseCheckpointRecorder
