import G1FiniteActorScheduleCommutation

/-! Pending actor updates commute past other original actor interfaces and
exterior operations. The exterior carrier may include the entire joint
checkpoint history and SAME immutable entering register. -/
namespace G1PendingActorInterfaceCommutation
open G1FiniteActorScheduleCommutation
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

inductive AsyncOperation (I S Base : Type*)
  | localStep (owner : I) (kernel : S → PMF S)
  | interface (owner : I) (kernel : Base × S → PMF (Base × S))
  | exterior (kernel : Base → PMF Base)

noncomputable def asyncStep : AsyncOperation I S Base → (Base × (I → S)) → PMF (Base × (I → S))
  | .localStep owner kernel,state => (kernel (state.2 owner)).map
      (fun value => (state.1,Function.update state.2 owner value))
  | .interface owner kernel,state => (kernel (state.1,state.2 owner)).map
      (fun value => (value.1,Function.update state.2 owner value.2))
  | .exterior kernel,state => (kernel state.1).map (fun value => (value,state.2))

def SafeFor (owner : I) : AsyncOperation I S Base → Prop
  | .localStep other _ => owner ≠ other
  | .interface other _ => owner ≠ other
  | .exterior _ => True

/-- A held actor computation cannot observe another interface's outside
changes, and that interface cannot read the held actor's localStep coordinate. -/
theorem private_commutes_safe_interface (owner : I) (kernel : S → PMF S)
    (op : AsyncOperation I S Base) (hsafe : SafeFor owner op) (state : Base × (I → S)) :
    (asyncStep (.localStep owner kernel) state).bind (asyncStep op) =
      (asyncStep op state).bind (asyncStep (.localStep owner kernel)) := by
  cases op with
  | localStep other k =>
      simp only [SafeFor] at hsafe
      simp only [asyncStep,PMF.bind_map,Function.comp_def]
      simp only [Function.update_of_ne hsafe,Function.update_of_ne hsafe.symm]
      simp only [PMF.map,Function.comp_def]
      rw [PMF.bind_comm]
      congr 1
      funext otherValue
      congr 1
      funext ownValue
      congr 1
      exact congrArg (fun f => (state.1,f)) (Function.update_comm hsafe ownValue otherValue state.2)
  | interface other k =>
      simp only [SafeFor] at hsafe
      simp only [asyncStep,PMF.bind_map,Function.comp_def]
      simp only [Function.update_of_ne hsafe,Function.update_of_ne hsafe.symm]
      simp only [PMF.map,Function.comp_def]
      rw [PMF.bind_comm]
      congr 1
      funext interfaceValue
      congr 1
      funext ownValue
      congr 1
      exact congrArg (fun f => (interfaceValue.1,f))
        (Function.update_comm hsafe ownValue interfaceValue.2 state.2)
  | exterior k =>
      simp only [asyncStep,PMF.bind_map,Function.comp_def]
      simp only [PMF.map,Function.comp_def]
      rw [PMF.bind_comm]

noncomputable def asyncProgram : List (AsyncOperation I S Base) → (Base × (I → S)) → PMF (Base × (I → S))
  | [],state => PMF.pure state
  | op::ops,state => (asyncStep op state).bind (asyncProgram ops)

lemma async_program_append (first last : List (AsyncOperation I S Base)) (state : Base × (I → S)) :
    asyncProgram (first ++ last) state = (asyncProgram first state).bind (asyncProgram last) := by
  induction first generalizing state with
  | nil => simp [asyncProgram,PMF.pure_bind]
  | cons op ops ih =>
      simp only [List.cons_append,asyncProgram,PMF.bind_bind]
      congr 1
      funext next
      exact ih next

/-- Promotion across any finite safe exterior/interface sequence preserves
the complete joint final exterior/history and actor state. -/
theorem private_commutes_safe_program (owner : I) (kernel : S → PMF S)
    (ops : List (AsyncOperation I S Base)) (hsafe : ∀ op ∈ ops, SafeFor owner op)
    (state : Base × (I → S)) :
    (asyncStep (.localStep owner kernel) state).bind (asyncProgram ops) =
      (asyncProgram ops state).bind (asyncStep (.localStep owner kernel)) := by
  induction ops generalizing state with
  | nil => simp [asyncProgram,PMF.bind_pure,PMF.pure_bind]
  | cons op ops ih =>
      calc
        _ = ((asyncStep (.localStep owner kernel) state).bind (asyncStep op)).bind (asyncProgram ops) := by
          simp only [asyncProgram,PMF.bind_bind]
        _ = ((asyncStep op state).bind (asyncStep (.localStep owner kernel))).bind (asyncProgram ops) := by
          rw [private_commutes_safe_interface owner kernel op (hsafe op (by simp)) state]
        _ = _ := by
          simp only [asyncProgram,PMF.bind_bind]
          congr 1
          funext next
          exact ih (fun q hq => hsafe q (List.mem_cons_of_mem op hq)) next

#print axioms private_commutes_safe_program
end G1PendingActorInterfaceCommutation
