import Mathlib

set_option debug.skipKernelTC false
namespace Nanuq.CornerShear
abbrev P := EuclideanSpace ℝ (Fin 2)

def forward (p : P) : P := !₂[p 0 + p 1, p 0 - p 1 - |p 0 + p 1| + 2]
def backward (p : P) : P := !₂[(p 0 + p 1 + |p 0| - 2)/2,
  (p 0 - p 1 - |p 0| + 2)/2]

def straighten : P ≃ₜ P where
  toFun := forward
  invFun := backward
  left_inv p := by
    ext i
    fin_cases i <;> simp [forward, backward] <;> ring
  right_inv p := by
    have h : (p 0 + p 1 + |p 0| - 2)/2 +
        (p 0 - p 1 - |p 0| + 2)/2 = p 0 := by ring
    ext i
    fin_cases i <;> simp [forward, backward, h] <;> ring
  continuous_toFun := by unfold forward; fun_prop
  continuous_invFun := by unfold backward; fun_prop

def upperL : Set P := {p | (p 1 = 1 ∧ |p 0| ≤ 1) ∨ (p 0 = -1 ∧ |p 1| ≤ 1)}
def horizontal : Set P := {p | p 1 = 0 ∧ |p 0| ≤ 2}

theorem forward_mem_iff (p : P) : forward p ∈ horizontal ↔ p ∈ upperL := by
  simp only [forward, horizontal, upperL, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hb⟩
    rcases le_total 0 (p 0 + p 1) with h | h
    · rw [abs_of_nonneg h] at hz hb
      left
      constructor
      · linarith
      · rw [abs_le]; constructor <;> linarith
    · rw [abs_of_nonpos h] at hz hb
      right
      constructor
      · linarith
      · rw [abs_le]; constructor <;> linarith
  · rintro (⟨hy,hx⟩ | ⟨hx,hy⟩)
    · rcases abs_le.mp hx with ⟨hl,hr⟩
      rw [hy, abs_of_nonneg (by linarith : 0 ≤ p 0 + 1)]
      constructor <;> linarith
    · rcases abs_le.mp hy with ⟨hl,hr⟩
      rw [hx, abs_of_nonpos (by linarith : -1 + p 1 ≤ 0)]
      constructor <;> linarith

theorem image_upperL : straighten '' upperL = horizontal := by
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact (forward_mem_iff p).mpr hp
  · intro hz
    refine ⟨straighten.symm z, ?_, straighten.apply_symm_apply z⟩
    apply (forward_mem_iff _).mp
    change straighten (straighten.symm z) ∈ horizontal
    simpa using hz

#print axioms image_upperL
end Nanuq.CornerShear
