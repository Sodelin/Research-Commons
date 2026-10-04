import G1CanonicalOwnOpeningRuntimePosition

/-! Other actor interfaces and retained base work preserve an OWN entering
coordinate. These actual support facts, rather than an invented whole cached
Code state, connect recorded opening values with later private computation. -/
namespace G1ActualSafeOwnInputRetention
open G1PendingActorInterfaceCommutation G1PendingInterfaceEntryRecorder
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

theorem actual_safe_step_own_coordinate (owner : I) (op : AsyncOperation I S Base) (hsafe : SafeFor owner op)
    (state : Base × (I → S)) {next : Base × (I → S)} (hn : next ∈ (asyncStep op state).support) :
    next.2 owner = state.2 owner := by
  cases op with
  | localStep other kernel =>
    obtain ⟨value,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    exact Function.update_of_ne hsafe _ _
  | interface other kernel =>
    obtain ⟨value,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    exact Function.update_of_ne hsafe _ _
  | exterior kernel =>
    obtain ⟨value,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    rfl

theorem actual_safe_program_own_coordinate (owner : I) (ops : List (AsyncOperation I S Base))
    (hsafe : ∀ op ∈ ops, SafeFor owner op) (state : Base × (I → S))
    {next : Base × (I → S)} (hn : next ∈ (asyncProgram ops state).support) : next.2 owner = state.2 owner := by
  induction ops generalizing state with
  | nil =>
    have he : next = state := by simpa only [asyncProgram,PMF.mem_support_pure_iff] using hn
    rw [he]
  | cons op ops ih =>
    obtain ⟨middle,hm,hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
    exact (ih (fun other ho => hsafe other (List.mem_cons_of_mem op ho)) middle hn).trans
      (actual_safe_step_own_coordinate owner op (hsafe op (List.mem_cons_self)) state hm)

lemma safe_entry_record_lift (owner : I) (op : AsyncOperation I S Base) (hs : SafeFor owner op) :
    SafeFor owner (interfaceRecordingLift op) := by cases op <;> exact hs

/-- Recorded entering inputs persist through ANY other private/base/interface
work. Whole recorded-entry distributions persist through every promotion by
the checked finite commutation theorem, without a supplied source-law field. -/
theorem actual_safe_recorded_program_own_coordinate (owner : I) (ops : List (AsyncOperation I S Base))
    (hsafe : ∀ op ∈ ops, SafeFor owner op) (records : List (I × S)) (state : Base × (I → S))
    {next : (Base × List (I × S)) × (I → S)}
    (hn : next ∈ (asyncProgram (ops.map interfaceRecordingLift) (withEntryRecords records state)).support) :
    next.2 owner = state.2 owner := by
  apply actual_safe_program_own_coordinate owner (ops.map interfaceRecordingLift) _ (withEntryRecords records state) hn
  intro op hm
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hm
  exact safe_entry_record_lift owner original (hsafe original ho)

#print axioms actual_safe_program_own_coordinate
#print axioms actual_safe_recorded_program_own_coordinate
end G1ActualSafeOwnInputRetention
