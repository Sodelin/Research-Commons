import IntervalBridge
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

theorem edgeWitness_cut (tips : List Nat) (lo len : Nat) (q : Quartet) (r a b c d : Nat)
    (hparts : q.parts r = (a,b,c,d)) :
    edgeWitness tips lo len q r = true ↔ intervalCut tips lo len a b c d := by
  simp [edgeWitness,hparts,intervalCut,Cut,Bool.or_eq_true,Bool.and_eq_true,and_assoc]

theorem whole_first_intervals (x : Nat) (rest : LTree) (hf : rest.Full) (a b c d : Nat)
    (hab : a≠b) (hcd : c≠d) :
    (LTree.fork (.tip x) rest).Witness [] a b c d ↔
      hasInterval rest.erase (x::rest.leaves) 1 a b c d := by
  rw [whole_fork]
  simp only [LTree.Witness,LTree.leaves]
  rw [or_iff_right (cut_tip_false x rest.leaves a b c d hab hcd)]
  simpa only [List.singleton_append,List.append_nil,List.length_cons,List.length_nil] using
    witness_intervals rest hf [x] [] a b c d hab hcd

/-- Direct bridge to the frozen finite provider's actual edgeWitness API,
not merely a similarly named replacement predicate. -/
theorem whole_first_edgeWitness (x : Nat) (rest : LTree) (hf : rest.Full)
    (q : Quartet) (r a b c d : Nat) (hparts : q.parts r = (a,b,c,d))
    (hab : a≠b) (hcd : c≠d) :
    (LTree.fork (.tip x) rest).Witness [] a b c d ↔
      ∃ e∈rest.erase.internalIntervals 1, edgeWitness (x::rest.leaves) e.1 e.2 q r = true := by
  rw [whole_first_intervals x rest hf a b c d hab hcd]
  simp only [hasInterval,edgeWitness_cut _ _ _ q r a b c d hparts]

#print axioms whole_first_edgeWitness
end Nanuq.Restriction
