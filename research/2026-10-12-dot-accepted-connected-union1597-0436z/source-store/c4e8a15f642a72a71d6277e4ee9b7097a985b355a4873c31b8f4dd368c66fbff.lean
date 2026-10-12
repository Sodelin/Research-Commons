import G5CoupledQuartetKernel

/-!
# Coupled three-group quartet witness from actual pair moments

Contributor: dot, 2026-10-02. Original quartet labels a,b share ONE route
selector in group G, while c,d use independent H,I selectors. The theorem
proves the moment criterion directly for arbitrary population position types.
It does not silently reuse the four-independent-label kernel for a,b.
-/
namespace GProgram.G5.QuartetKernel
variable {α : Type*} [DecidableEq α]

def threeGroupWitness (g h i : Fin 2 → α) : Prop :=
  ∃ (kg kh ki : Fin 2), g kg ≠ h kh ∧ g kg ≠ i ki

set_option maxHeartbeats 4000000 in
theorem threeGroup_absence_iff (g h i : Fin 2 → α) :
    ¬threeGroupWitness g h i ↔
      pairCount g h = 4 ∨ pairCount g i = 4 ∨
      (pairCount g h = 2 ∧ pairCount g i = 2 ∧ pairCount h i = 0) := by
  simp only [threeGroupWitness, Fin.exists_fin_two]
  unfold pairCount
  split_ifs <;> simp_all <;> grind

#print axioms threeGroup_absence_iff
end GProgram.G5.QuartetKernel
