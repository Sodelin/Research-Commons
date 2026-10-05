import G1PromotedFirstEntryRealSourceSupport

/-! An actual K-input support state reads the genuine first own opening
record. Later/exterior private work cannot change that coordinate or record. -/
namespace G1ActualKInputFirstRecord
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1PendingInterfaceEntryRecorder
open G1ActualSafeOwnInputRetention G1FirstOwnInterfaceRecordSupport
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

lemma find_own_after_no_records (owner : I) (value : S) (before later : List (I × S))
    (hn : NoOwnRecord owner before) :
    (before ++ (owner,value)::later).find? (fun pair => decide (pair.1 = owner)) = some (owner,value) := by
  induction before with
  | nil => simp
  | cons pair before ih =>
    have ho := hn pair List.mem_cons_self
    have ht : NoOwnRecord owner before := fun other hm => hn other (List.mem_cons_of_mem pair hm)
    simp [ho,ih ht]

lemma actual_first_own_record_unique (owner : I) (first last : S) (records : List (I × S))
    (hf : FirstOwnRecord owner first records) (hl : FirstOwnRecord owner last records) : first = last := by
  obtain ⟨beforeF,laterF,heF,hnF⟩ := hf
  obtain ⟨beforeL,laterL,heL,hnL⟩ := hl
  have hF : records.find? (fun pair => decide (pair.1 = owner)) = some (owner,first) := by
    rw [heF]; exact find_own_after_no_records owner first beforeF laterF hnF
  have hL : records.find? (fun pair => decide (pair.1 = owner)) = some (owner,last) := by
    rw [heL]; exact find_own_after_no_records owner last beforeL laterL hnL
  exact congrArg Prod.snd (Option.some.inj (hF.symm.trans hL))

/-- Genuine support immediately before its own private K has the SAME
complete entering value recorded at the real opening. No intermediate
whole original Code is assumed for an early pending output. -/
theorem actual_input_after_open_and_other_work_is_first_record (owner : I)
    (before gap : List (AsyncOperation I S Base))
    (hb : ∀ op ∈ before, InteriorSafe owner op) (hg : ∀ op ∈ gap, SafeFor owner op)
    (opening : Base × S → PMF (Base × S))
    (state : (Base × List (I × S)) × (I → S)) (hno : NoOwnRecord owner state.1.2)
    {input : (Base × List (I × S)) × (I → S)}
    (hi : input ∈ (asyncProgram ((before ++ [AsyncOperation.interface owner opening] ++ gap).map interfaceRecordingLift) state).support) :
    FirstOwnRecord owner (input.2 owner) input.1.2 := by
  rw [List.map_append,async_program_append] at hi
  obtain ⟨opened,ho,hgap⟩ := (PMF.mem_support_bind_iff _ _ _).mp hi
  rw [List.map_append,async_program_append] at ho
  obtain ⟨atOpen,hbRun,hoRun⟩ := (PMF.mem_support_bind_iff _ _ _).mp ho
  have hn := actual_no_own_record_safe_program owner before hb state hno hbRun
  have hopen : opened ∈ (asyncStep (interfaceRecordingLift (.interface owner opening)) atOpen).support :=
    by simpa only [List.map_singleton,asyncProgram,PMF.bind_pure] using hoRun
  have hfirst := actual_own_interface_first_record owner opening atOpen hn hopen
  have hrecord := actual_first_own_record_persists owner (opened.2 owner) gap opened hfirst hgap
  have hs : ∀ op ∈ gap.map interfaceRecordingLift, SafeFor owner op := by
    intro op hm
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hm
    exact safe_entry_record_lift owner old (hg old hold)
  have hvalue := actual_safe_program_own_coordinate owner (gap.map interfaceRecordingLift) hs opened hgap
  simpa only [hvalue] using hrecord

#print axioms actual_input_after_open_and_other_work_is_first_record
end G1ActualKInputFirstRecord
