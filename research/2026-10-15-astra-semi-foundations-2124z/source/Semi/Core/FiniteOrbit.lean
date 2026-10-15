import Mathlib.Data.Finset.Max
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
import Lean.Elab.Tactic.Omega

/-! Finite orbit pseudodistance for an explicitly supplied isometric action.
SOURCE CANDIDATE, not a checked result. No observation invariance is assumed
unless supplied separately. -/

namespace Semi.Core

open Finset

structure FiniteOrbitGeometry (G X : Type*) [Group G] [Fintype G] where
  action : G →* Equiv.Perm X
  distance : X → X → ℕ
  self : ∀ x, distance x x = 0
  symmetric : ∀ x y, distance x y = distance y x
  triangle : ∀ x y z, distance x z ≤ distance x y + distance y z
  eq_zero : ∀ x y, distance x y = 0 ↔ x = y
  invariant : ∀ g x y, distance (action g x) (action g y) = distance x y

namespace FiniteOrbitGeometry

variable {G X : Type*} [Group G] [Fintype G] (M : FiniteOrbitGeometry G X)

def Related (x y : X) : Prop := ∃ g : G, M.action g x = y

def orbitSetoid : Setoid X where
  r := M.Related
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact ⟨1, by simp⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [← Equiv.Perm.mul_apply, ← map_mul]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨h * g, by simp [map_mul, Equiv.Perm.mul_apply]⟩

noncomputable def distanceValues (x y : X) : Finset ℕ :=
  Finset.univ.image (fun g : G => M.distance x (M.action g y))

theorem distanceValues_nonempty (x y : X) : (M.distanceValues x y).Nonempty := by
  classical
  exact ⟨M.distance x (M.action 1 y), Finset.mem_image.mpr ⟨1, by simp, rfl⟩⟩

noncomputable def orbitDistance (x y : X) : ℕ :=
  (M.distanceValues x y).min' (M.distanceValues_nonempty x y)

theorem orbitDistance_le (x y : X) (g : G) :
    M.orbitDistance x y ≤ M.distance x (M.action g y) := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨g, by simp, rfl⟩)

theorem exists_minimizer (x y : X) :
    ∃ g : G, M.orbitDistance x y = M.distance x (M.action g y) := by
  classical
  obtain ⟨g, _, hg⟩ := Finset.mem_image.mp
    (Finset.min'_mem (M.distanceValues x y) (M.distanceValues_nonempty x y))
  exact ⟨g, hg.symm⟩

theorem orbitDistance_le_distance (x y : X) :
    M.orbitDistance x y ≤ M.distance x y := by
  simpa using M.orbitDistance_le x y 1

@[simp] theorem orbitDistance_self (x : X) : M.orbitDistance x x = 0 := by
  exact Nat.eq_zero_of_le_zero ((M.orbitDistance_le_distance x x).trans_eq (M.self x))

theorem orbitDistance_comm (x y : X) : M.orbitDistance x y = M.orbitDistance y x := by
  have half : ∀ a b, M.orbitDistance a b ≤ M.orbitDistance b a := by
    intro a b
    obtain ⟨g, hg⟩ := M.exists_minimizer b a
    calc
      M.orbitDistance a b ≤ M.distance a (M.action g⁻¹ b) := M.orbitDistance_le _ _ _
      _ = M.distance (M.action g a) b := by
        simpa [← Equiv.Perm.mul_apply, ← map_mul] using
          (M.invariant g a (M.action g⁻¹ b)).symm
      _ = M.distance b (M.action g a) := M.symmetric _ _
      _ = M.orbitDistance b a := hg.symm
  exact le_antisymm (half x y) (half y x)

theorem orbitDistance_triangle (x y z : X) :
    M.orbitDistance x z ≤ M.orbitDistance x y + M.orbitDistance y z := by
  obtain ⟨g, hg⟩ := M.exists_minimizer x y
  obtain ⟨h, hh⟩ := M.exists_minimizer y z
  calc
    M.orbitDistance x z ≤ M.distance x (M.action (g * h) z) := M.orbitDistance_le _ _ _
    _ ≤ M.distance x (M.action g y) + M.distance (M.action g y) (M.action (g * h) z) :=
      M.triangle _ _ _
    _ = M.distance x (M.action g y) + M.distance y (M.action h z) := by
      rw [map_mul, Equiv.Perm.mul_apply, M.invariant]
    _ = M.orbitDistance x y + M.orbitDistance y z := by rw [hg, hh]

@[simp] theorem orbitDistance_eq_zero (x y : X) :
    M.orbitDistance x y = 0 ↔ M.Related x y := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := M.exists_minimizer x y
    have he := (M.eq_zero x (M.action g y)).1 (hg.symm.trans h)
    refine ⟨g⁻¹, ?_⟩
    rw [he]
    simp [← Equiv.Perm.mul_apply, ← map_mul]
  · rintro ⟨g, rfl⟩
    apply Nat.eq_zero_of_le_zero
    simpa [← Equiv.Perm.mul_apply, ← map_mul, M.self] using
      M.orbitDistance_le x (M.action g x) g⁻¹

theorem orbitDistance_congr {x x' y y' : X}
    (hx : M.Related x x') (hy : M.Related y y') :
    M.orbitDistance x y = M.orbitDistance x' y' := by
  have hxx' := (M.orbitDistance_eq_zero x x').2 hx
  have hyy' := (M.orbitDistance_eq_zero y y').2 hy
  have hx'x : M.orbitDistance x' x = 0 := by rw [M.orbitDistance_comm, hxx']
  have hy'y : M.orbitDistance y' y = 0 := by rw [M.orbitDistance_comm, hyy']
  have h1 := M.orbitDistance_triangle x x' y
  have h2 := M.orbitDistance_triangle x' y' y
  have h3 := M.orbitDistance_triangle x' x y'
  have h4 := M.orbitDistance_triangle x y y'
  omega

noncomputable def quotientDistance
    (a b : Quotient M.orbitSetoid) : ℕ :=
  Quotient.liftOn₂ a b M.orbitDistance (by
    intro x y x' y' hx hy
    exact M.orbitDistance_congr hx hy)

@[simp] theorem quotientDistance_self (a : Quotient M.orbitSetoid) :
    M.quotientDistance a a = 0 := by
  refine Quotient.inductionOn a (fun x => ?_)
  exact M.orbitDistance_self x

theorem quotientDistance_comm (a b : Quotient M.orbitSetoid) :
    M.quotientDistance a b = M.quotientDistance b a := by
  refine Quotient.inductionOn₂ a b (fun x y => ?_)
  exact M.orbitDistance_comm x y

theorem quotientDistance_triangle (a b c : Quotient M.orbitSetoid) :
    M.quotientDistance a c ≤ M.quotientDistance a b + M.quotientDistance b c := by
  refine Quotient.inductionOn a (fun x => ?_)
  refine Quotient.inductionOn b (fun y => ?_)
  refine Quotient.inductionOn c (fun z => ?_)
  exact M.orbitDistance_triangle x y z

@[simp] theorem quotientDistance_eq_zero (a b : Quotient M.orbitSetoid) :
    M.quotientDistance a b = 0 ↔ a = b := by
  refine Quotient.inductionOn₂ a b (fun x y => ?_)
  change M.orbitDistance x y = 0 ↔ Quotient.mk M.orbitSetoid x = Quotient.mk M.orbitSetoid y
  rw [M.orbitDistance_eq_zero]
  exact ⟨Quotient.sound, Quotient.exact⟩

end FiniteOrbitGeometry
end Semi.Core
