import G1RecordedOwnOpeningRealFrontier

/-! Genuine interface recording only APPENDS; a first OWN opening value is
never replaced by a later closing output. These support facts retain the
whole joint record, not a product of separately manufactured witnesses. -/
namespace G1FirstOwnInterfaceRecordSupport
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1PendingInterfaceEntryRecorder
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

def NoOwnRecord (owner : I) (records : List (I × S)) : Prop := ∀ pair ∈ records, pair.1 ≠ owner

def FirstOwnRecord (owner : I) (value : S) (records : List (I × S)) : Prop :=
  ∃ first later, records = first ++ (owner,value)::later ∧ NoOwnRecord owner first

lemma first_own_record_append (owner : I) (value : S) (first last : List (I × S))
    (hs : FirstOwnRecord owner value first) : FirstOwnRecord owner value (first ++ last) := by
  obtain ⟨before,later,he,hn⟩ := hs
  refine ⟨before,later++last,?_,hn⟩
  simp only [he,List.append_assoc,List.cons_append]

theorem actual_record_step_appends (op : AsyncOperation I S Base)
    (state : (Base × List (I × S)) × (I → S))
    {next : (Base × List (I × S)) × (I → S)}
    (hn : next ∈ (asyncStep (interfaceRecordingLift op) state).support) :
    ∃ added, next.1.2 = state.1.2 ++ added := by
  cases op with
  | localStep other kernel =>
    obtain ⟨value,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    exact ⟨[],(List.append_nil _).symm⟩
  | interface other kernel =>
    obtain ⟨value,hv,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    obtain ⟨actual,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    exact ⟨[(other,actual.2)],rfl⟩
  | exterior kernel =>
    obtain ⟨value,hv,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    obtain ⟨actual,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    exact ⟨[],(List.append_nil _).symm⟩

theorem actual_record_program_appends (ops : List (AsyncOperation I S Base))
    (state : (Base × List (I × S)) × (I → S))
    {next : (Base × List (I × S)) × (I → S)}
    (hn : next ∈ (asyncProgram (ops.map interfaceRecordingLift) state).support) :
    ∃ added, next.1.2 = state.1.2 ++ added := by
  induction ops generalizing state with
  | nil =>
    have he : next = state := by simpa only [List.map_nil,asyncProgram,PMF.mem_support_pure_iff] using hn
    exact ⟨[],by simp [he]⟩
  | cons op ops ih =>
    obtain ⟨middle,hm,hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
    obtain ⟨first,hfirst⟩ := actual_record_step_appends op state hm
    obtain ⟨last,hlast⟩ := ih middle hn
    exact ⟨first++last,by rw [hlast,hfirst,List.append_assoc]⟩

theorem actual_no_own_record_safe_step (owner : I) (op : AsyncOperation I S Base)
    (hs : InteriorSafe owner op) (state : (Base × List (I × S)) × (I → S))
    (hno : NoOwnRecord owner state.1.2) {next : (Base × List (I × S)) × (I → S)}
    (hn : next ∈ (asyncStep (interfaceRecordingLift op) state).support) : NoOwnRecord owner next.1.2 := by
  cases op with
  | localStep other kernel =>
    obtain ⟨value,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    exact hno
  | exterior kernel =>
    obtain ⟨value,hv,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    obtain ⟨actual,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    exact hno
  | interface other kernel =>
    obtain ⟨value,hv,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
    obtain ⟨actual,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    intro pair hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hno pair hp
    · have he := List.mem_singleton.mp hp
      rw [he]
      exact Ne.symm hs

theorem actual_no_own_record_safe_program (owner : I) (ops : List (AsyncOperation I S Base))
    (hs : ∀ op ∈ ops, InteriorSafe owner op) (state : (Base × List (I × S)) × (I → S))
    (hno : NoOwnRecord owner state.1.2) {next : (Base × List (I × S)) × (I → S)}
    (hn : next ∈ (asyncProgram (ops.map interfaceRecordingLift) state).support) : NoOwnRecord owner next.1.2 := by
  induction ops generalizing state with
  | nil =>
    have he : next = state := by simpa only [List.map_nil,asyncProgram,PMF.mem_support_pure_iff] using hn
    rw [he]; exact hno
  | cons op ops ih =>
    obtain ⟨middle,hm,hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
    exact ih (fun q hq => hs q (List.mem_cons_of_mem op hq)) middle
      (actual_no_own_record_safe_step owner op (hs op List.mem_cons_self) state hno hm) hn

theorem actual_own_interface_first_record (owner : I) (kernel : Base × S → PMF (Base × S))
    (state : (Base × List (I × S)) × (I → S)) (hno : NoOwnRecord owner state.1.2)
    {next : (Base × List (I × S)) × (I → S)}
    (hn : next ∈ (asyncStep (interfaceRecordingLift (.interface owner kernel)) state).support) :
    FirstOwnRecord owner (next.2 owner) next.1.2 := by
  obtain ⟨value,hv,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
  obtain ⟨actual,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
  refine ⟨state.1.2,[],?_,hno⟩
  simp [Function.update_self]

theorem actual_first_own_record_persists (owner : I) (value : S)
    (ops : List (AsyncOperation I S Base)) (state : (Base × List (I × S)) × (I → S))
    (hfirst : FirstOwnRecord owner value state.1.2)
    {next : (Base × List (I × S)) × (I → S)}
    (hn : next ∈ (asyncProgram (ops.map interfaceRecordingLift) state).support) :
    FirstOwnRecord owner value next.1.2 := by
  obtain ⟨added,he⟩ := actual_record_program_appends ops state hn
  rw [he]
  exact first_own_record_append owner value _ added hfirst

#print axioms actual_first_own_record_persists
end G1FirstOwnInterfaceRecordSupport
