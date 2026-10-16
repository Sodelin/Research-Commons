import Mathlib.Analysis.Fourier.ZMod
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic.NormNum

/-! Classical cyclic binary example. SOURCE CANDIDATE, not yet elaborated.
This is one cyclic group, not a flattened product lattice. -/

namespace Semi.Diffraction

abbrev Grid (N : ℕ) := ZMod N
abbrev Configuration (N : ℕ) := Grid N → Bool

def spin (b : Bool) : ℝ := if b then 1 else -1
def complexSpin (b : Bool) : ℂ := (spin b : ℝ)

@[simp] theorem spin_sq (b : Bool) : spin b ^ 2 = 1 := by cases b <;> norm_num [spin]
@[simp] theorem complexSpin_conj (b : Bool) :
    starRingEnd ℂ (complexSpin b) = complexSpin b := by simp [complexSpin]
@[simp] theorem complexSpin_mul_conj (b : Bool) :
    complexSpin b * starRingEnd ℂ (complexSpin b) = 1 := by
  cases b <;> norm_num [complexSpin, spin]
@[simp] theorem complexSpin_not (b : Bool) : complexSpin (!b) = -complexSpin b := by
  cases b <;> norm_num [complexSpin, spin]

variable {N : ℕ} [NeZero N]

def shiftSite (t : Grid N) : Equiv.Perm (Grid N) where
  toFun i := i + t
  invFun i := i - t
  left_inv i := by simp
  right_inv i := by simp

def translate (t : Grid N) : Equiv.Perm (Configuration N) where
  toFun x i := x (i + t)
  invFun x i := x (i - t)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def invert : Equiv.Perm (Configuration N) where
  toFun x i := x (-i)
  invFun x i := x (-i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def globalSign : Equiv.Perm (Configuration N) where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def symmetryGenerators : Set (Equiv.Perm (Configuration N)) :=
  {g | (∃ t : Grid N, g = translate t) ∨ g = invert ∨ g = globalSign}

/-- Only these generators and their group consequences are declared symmetries.
There is no partial-axis reflection or frequency-label quotient here. -/
def symmetries (N : ℕ) [NeZero N] : Subgroup (Equiv.Perm (Configuration N)) :=
  Subgroup.closure symmetryGenerators

noncomputable instance symmetryFintype : Fintype (symmetries N) := Fintype.ofFinite _

theorem hamming_reindex (e : Equiv.Perm (Grid N)) (x y : Configuration N) :
    hammingDist (fun i => x (e i)) (fun i => y (e i)) = hammingDist x y := by
  classical
  unfold hammingDist
  exact Finset.card_bijective e e.bijective (by intro i; simp)

def hammingIsometries (N : ℕ) [NeZero N] : Subgroup (Equiv.Perm (Configuration N)) where
  carrier := {g | ∀ x y, hammingDist (g x) (g y) = hammingDist x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro g h hg hh x y
    exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    simpa using (hg (g⁻¹ x) (g⁻¹ y)).symm

theorem symmetry_preserves_hamming (g : symmetries N) (x y : Configuration N) :
    hammingDist (g.1 x) (g.1 y) = hammingDist x y := by
  have hsub : symmetries N ≤ hammingIsometries N := by
    apply (Subgroup.closure_le (K := hammingIsometries N)).mpr
    intro g hg
    rcases hg with ⟨t, rfl⟩ | rfl | rfl
    · intro x y; exact hamming_reindex (shiftSite t) x y
    · intro x y; exact hamming_reindex (Equiv.neg _) x y
    · intro x y
      exact hammingDist_comp (fun _ => Bool.not) (fun _ => by
        intro a b h; cases a <;> cases b <;> simp_all)
  exact hsub g.2 x y

end Semi.Diffraction
