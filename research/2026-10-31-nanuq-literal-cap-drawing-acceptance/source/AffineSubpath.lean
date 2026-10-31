import Mathlib.Topology.Path
import Mathlib.Tactic

/-! Internal helper for literal subarcs of the same original cap drawing.
Unlike Path.truncate, affine restriction has no constant parameter tails. -/
namespace Nanuq.CapCurves
open Set

def affineParameter (a b t : unitInterval) : unitInterval :=
  ⟨(1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ), by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
        (mul_nonneg t.property.1 b.property.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr a.property.2),
        mul_nonneg t.property.1 (sub_nonneg.mpr b.property.2)]⟩

@[simp] theorem affineParameter_zero (a b : unitInterval) : affineParameter a b 0 = a := by
  apply Subtype.ext
  simp [affineParameter]

@[simp] theorem affineParameter_one (a b : unitInterval) : affineParameter a b 1 = b := by
  apply Subtype.ext
  simp [affineParameter]

theorem affineParameter_injective (a b : unitInterval) (hab : a ≠ b) :
    Function.Injective (affineParameter a b) := by
  intro s t h
  have he := congrArg Subtype.val h
  have hm : ((b:ℝ)-(a:ℝ))*((s:ℝ)-(t:ℝ)) = 0 := by
    dsimp [affineParameter] at he
    nlinarith
  rcases mul_eq_zero.mp hm with h | h
  · exact False.elim (hab (Subtype.ext (by linarith)))
  · exact Subtype.ext (by linarith)

def affineSubpath {A : Type*} [TopologicalSpace A] {x y : A}
    (p : Path x y) (a b : unitInterval) : Path (p a) (p b) where
  toFun t := p (affineParameter a b t)
  continuous_toFun := p.continuous.comp (by fun_prop [affineParameter])
  source' := by simp
  target' := by simp

theorem affineSubpath_injective {A : Type*} [TopologicalSpace A] {x y : A}
    (p : Path x y) (hp : Function.Injective p) (a b : unitInterval) (hab : a ≠ b) :
    Function.Injective (affineSubpath p a b) :=
  hp.comp (affineParameter_injective a b hab)

theorem affineSubpath_range_subset {A : Type*} [TopologicalSpace A] {x y : A}
    (p : Path x y) (a b : unitInterval) : range (affineSubpath p a b) ⊆ range p := by
  rintro z ⟨t,rfl⟩
  exact ⟨affineParameter a b t,rfl⟩

#print axioms affineSubpath_injective
#print axioms affineSubpath_range_subset
end Nanuq.CapCurves
