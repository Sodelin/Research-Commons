import G5CoupledQuartetKernel

/-! Exact support cases for the original two-by-two selector pair count.
No finite population alphabet or desired output equality is supplied. -/
namespace GProgram.G5.QuartetKernel
variable {α : Type*} [DecidableEq α]

def splitPositions (p : Fin 2 → α) : Prop := p 0 ≠ p 1

def sameTwoPositions (p q : Fin 2 → α) : Prop :=
  (p 0 = q 0 ∧ p 1 = q 1) ∨ (p 0 = q 1 ∧ p 1 = q 0)

theorem pairCount_zero_iff (p q : Fin 2 → α) :
    pairCount p q = 0 ↔
      p 0 ≠ q 0 ∧ p 0 ≠ q 1 ∧ p 1 ≠ q 0 ∧ p 1 ≠ q 1 := by
  unfold pairCount
  split_ifs <;> simp_all <;> grind

theorem pairCount_two_iff (p q : Fin 2 → α) :
    pairCount p q = 2 ↔
      (p 0 = p 1 ∧ q 0 ≠ q 1 ∧ (p 0 = q 0 ∨ p 0 = q 1)) ∨
      (q 0 = q 1 ∧ p 0 ≠ p 1 ∧ (q 0 = p 0 ∨ q 0 = p 1)) ∨
      (p 0 ≠ p 1 ∧ q 0 ≠ q 1 ∧ sameTwoPositions p q) := by
  unfold pairCount sameTwoPositions
  split_ifs <;> simp_all <;> grind

theorem pairCount_one_iff (p q : Fin 2 → α) :
    pairCount p q = 1 ↔
      p 0 ≠ p 1 ∧ q 0 ≠ q 1 ∧
      (p 0 = q 0 ∨ p 0 = q 1 ∨ p 1 = q 0 ∨ p 1 = q 1) ∧
      ¬sameTwoPositions p q := by
  unfold pairCount sameTwoPositions
  split_ifs <;> simp_all <;> grind

#print axioms pairCount_zero_iff
#print axioms pairCount_two_iff
#print axioms pairCount_one_iff
end GProgram.G5.QuartetKernel
