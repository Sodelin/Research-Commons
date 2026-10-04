import G5ExponentialGermIdentification
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Exponential right germs identify different unsupplied rate supports

New proof contribution: dot's active Lean source-bridge lane, 2026-10-02.
Each law is an intrinsic finitely supported real exponent coefficient map.
No common rate list, calibrated hidden clocks, positivity, or event grid is
supplied. Equal right germs identify the whole map and its zero-rate mass.
Actual source routing/permanent-meeting interpretation remains separate.
-/

namespace GProgram.G5.ExponentialGerm

open scoped BigOperators

noncomputable def finiteExpSum (c : ℝ →₀ ℝ) (s : ℝ) : ℝ :=
  c.sum (fun rate weight => weight * Real.exp (rate * s))

theorem finite_coefficients_zero_of_right_germ (c : ℝ →₀ ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → finiteExpSum c s = 0) : c = 0 := by
  classical
  let e := (Fintype.equivFin {r : ℝ // r ∈ c.support}).symm
  let rate := fun i => (e i).val
  let coeff := fun i => c (rate i)
  have hrate : Function.Injective rate := Subtype.val_injective.comp e.injective
  have hpres (s : ℝ) : expSum rate coeff s = finiteExpSum c s := by
    change (∑ i, c (e i).val * Real.exp ((e i).val * s)) =
      ∑ r ∈ c.support, c r * Real.exp (r * s)
    rw [Fintype.sum_equiv e (fun i => c (e i).val * Real.exp ((e i).val * s))
      (fun r => c r.val * Real.exp (r.val * s)) (fun _ => rfl)]
    exact Finset.sum_attach c.support (fun r => c r * Real.exp (r * s))
  have hc : coeff = 0 := by
    apply coefficients_eq_of_right_germ rate coeff 0 hrate hε
    intro s hs hse
    rw [hpres, h s hs hse]
    simp [expSum]
  ext r
  by_cases hr : r ∈ c.support
  · have hi := congrFun hc (e.symm ⟨r, hr⟩)
    simpa [coeff, rate] using hi
  · exact Finsupp.notMem_support_iff.mp hr

theorem finite_coefficients_eq_of_right_germ (c d : ℝ →₀ ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → finiteExpSum c s = finiteExpSum d s) : c = d := by
  apply sub_eq_zero.mp
  apply finite_coefficients_zero_of_right_germ (c - d) hε
  intro s hs hse
  rw [finiteExpSum, Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _)]
  exact sub_eq_zero.mpr (h s hs hse)

theorem finite_constant_mass_eq_of_right_germ (c d : ℝ →₀ ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → finiteExpSum c s = finiteExpSum d s) : c 0 = d 0 := by
  exact congrArg (fun f : ℝ →₀ ℝ => f 0)
    (finite_coefficients_eq_of_right_germ c d hε h)

#print axioms finite_coefficients_zero_of_right_germ
#print axioms finite_coefficients_eq_of_right_germ
#print axioms finite_constant_mass_eq_of_right_germ

end GProgram.G5.ExponentialGerm
