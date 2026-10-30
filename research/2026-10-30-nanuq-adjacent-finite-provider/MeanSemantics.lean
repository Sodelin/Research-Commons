import BitWitness
import Mathlib.Tactic.NormNum
set_option debug.skipKernelTC false
namespace Nanuq.AdjacentCertificate

theorem present_card_one_or_two (c : Nat) (h : c ∈ ([1,4,5] : List Nat)) :
    ((List.range 3).filter (fun r => c.testBit r)).length = 1 ∨
    ((List.range 3).filter (fun r => c.testBit r)).length = 2 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem double_mean_exact (k m : Nat) (hm : m = 1 ∨ m = 2) :
    ((2*k/m : Nat) : ℚ) = 2 * (k : ℚ) / (m : ℚ) := by
  rcases hm with rfl | rfl
  · simp
  · simp [Nat.mul_div_cancel_left]

/-- Exact uniform DISTINCT resolution mean, not a switching-weighted score. -/
theorem twiceMean_exact (qs : List Quartet) (pattern x y p q : Nat)
    (valid : code pattern (quartetIndex qs x y p q) ∈ ([1,4,5] : List Nat)) :
    (twiceMean qs pattern x y p q : ℚ) =
      2 * (((List.range 3).filter (fun r => (code pattern (quartetIndex qs x y p q)).testBit r)).filter
        (fun r => (quartetAt qs x y p q).side r x != (quartetAt qs x y p q).side r y)).length /
      (((List.range 3).filter (fun r => (code pattern (quartetIndex qs x y p q)).testBit r)).length : ℚ) := by
  unfold twiceMean
  exact double_mean_exact _ _ (present_card_one_or_two _ valid)
#print axioms twiceMean_exact
end Nanuq.AdjacentCertificate
