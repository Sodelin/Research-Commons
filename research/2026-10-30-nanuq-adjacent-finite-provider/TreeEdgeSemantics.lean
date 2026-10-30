import AdjacentSemantics
set_option debug.skipKernelTC false
namespace Nanuq.AdjacentCertificate

def Tree.internalIntervals (lo : Nat) : Tree → List (Nat × Nat)
  | .tip => []
  | .fork a b => a.internalIntervals lo ++ b.internalIntervals (lo+a.size) ++
      [(lo,a.size+b.size)]

/-- A bit in the summary means an actual internal interval edge witnesses
it. The tree need not belong to a precomputed finite list. -/
theorem Tree.summary_bit (t : Tree) (c : Nat → Nat → Nat) (lo bit : Nat) :
    (t.summary c lo).testBit bit =
      (t.internalIntervals lo).any (fun e => (c e.1 e.2).testBit bit) := by
  induction t generalizing lo with
  | tip => simp [summary,internalIntervals]
  | fork a b ha hb =>
    simp only [summary,internalIntervals,Nat.testBit_or,List.any_append,List.any_cons,List.any_nil]
    rw [ha,hb]
    simp

 theorem Tree.summary_bit_iff (t : Tree) (c : Nat → Nat → Nat) (lo bit : Nat) :
    (t.summary c lo).testBit bit = true ↔
      ∃ e ∈ t.internalIntervals lo, (c e.1 e.2).testBit bit = true := by
  rw [t.summary_bit]
  exact List.any_eq_true

#print axioms Tree.summary_bit_iff
end Nanuq.AdjacentCertificate
