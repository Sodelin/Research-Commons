import G1InitializedOpeningRuntimeAdmission

/-! Every OWN interface can retain its complete output coordinate in base.
This provides a lawful witness for entering opaque inputs through promotion:
own private computations cannot cross their own recording interface, while
other private coordinates commute with it. No cached Code state is invented. -/
namespace G1PendingInterfaceEntryRecorder
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open scoped Classical
variable {I S Base : Type*} [DecidableEq I]

noncomputable def withEntryRecords (records : List (I × S)) (state : Base × (I → S)) :
    (Base × List (I × S)) × (I → S) := ((state.1,records),state.2)

def forgetEntryRecords (state : (Base × List (I × S)) × (I → S)) : Base × (I → S) :=
  (state.1.1,state.2)

noncomputable def interfaceRecordingLift : AsyncOperation I S Base → AsyncOperation I S (Base × List (I × S))
  | .localStep owner kernel => .localStep owner kernel
  | .interface owner kernel => .interface owner (fun value =>
      (kernel (value.1.1,value.2)).map (fun next => ((next.1,value.1.2 ++ [(owner,next.2)]),next.2)))
  | .exterior kernel => .exterior (fun value => (kernel value.1).map (fun next => (next,value.2)))

/-- The recorder retains the SAME genuine interface row, jointly with its
complete new ORIGINAL private coordinate. It does not inspect other slots. -/
theorem actual_interface_output_record (owner : I) (kernel : Base × S → PMF (Base × S))
    (records : List (I × S)) (state : Base × (I → S)) :
    asyncStep (interfaceRecordingLift (.interface owner kernel)) (withEntryRecords records state) =
      (asyncStep (.interface owner kernel) state).map
        (fun next => withEntryRecords (records ++ [(owner,next.2 owner)]) next) := by
  simp only [interfaceRecordingLift,asyncStep,withEntryRecords,PMF.map_comp,Function.comp_def,Function.update_self]

lemma actual_entry_record_step_forget (op : AsyncOperation I S Base)
    (state : (Base × List (I × S)) × (I → S)) :
    (asyncStep (interfaceRecordingLift op) state).map forgetEntryRecords = asyncStep op (forgetEntryRecords state) := by
  cases op <;> simp only [interfaceRecordingLift,asyncStep,forgetEntryRecords,PMF.map_comp,Function.comp_def]

/-- Every source/interface operation is unchanged after forgetting the extra
input records. Original registers, genealogy and population rows are intact. -/
theorem actual_entry_record_program_forget (ops : List (AsyncOperation I S Base))
    (state : (Base × List (I × S)) × (I → S)) :
    (asyncProgram (ops.map interfaceRecordingLift) state).map forgetEntryRecords =
      asyncProgram ops (forgetEntryRecords state) := by
  induction ops generalizing state with
  | nil => simp [asyncProgram,PMF.pure_map]
  | cons op ops ih =>
    simp only [List.map_cons,asyncProgram,PMF.map_bind]
    simp_rw [ih]
    rw [←actual_entry_record_step_forget op state,PMF.bind_map]
    rfl

lemma owner_kernels_entry_record_lift (owner : I) (ops : List (AsyncOperation I S Base)) :
    ownerKernels owner (ops.map interfaceRecordingLift) = ownerKernels owner ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [List.map_cons,interfaceRecordingLift,ownerKernels]
    case localStep other kernel => split_ifs <;> simp [ih]
    all_goals exact ih

/-- Finite ALL-actor promotion retains EVERY recorded interface coordinate
JOINTLY with base/history, including real entering opaque inputs. Actual own
open/close identification and source support are compiler gates, not axioms. -/
theorem actual_every_actor_promotion_retains_entry_records (owners : List I)
    (ops : List (AsyncOperation I S Base)) (records : List (I × S)) (state : Base × (I → S)) :
    asyncProgram (ops.map interfaceRecordingLift) (withEntryRecords records state) =
      asyncProgram (promoteEveryActor owners (ops.map interfaceRecordingLift)) (withEntryRecords records state) :=
    actual_every_actor_promotion_row owners _ _

#print axioms actual_interface_output_record
#print axioms actual_entry_record_program_forget
#print axioms actual_every_actor_promotion_retains_entry_records
end G1PendingInterfaceEntryRecorder
