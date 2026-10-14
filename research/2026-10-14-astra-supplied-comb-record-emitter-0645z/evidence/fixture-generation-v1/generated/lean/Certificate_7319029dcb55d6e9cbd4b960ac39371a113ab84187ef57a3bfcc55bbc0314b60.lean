import Astra.CommonCertificateKernel

/- Exact certificate SHA256: 7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60. Generation is not compilation. -/
namespace Astra.Generated.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60
open Astra.CommonCertificateKernel
open scoped BigOperators

noncomputable def polynomial (x : ℝ) : ℝ := (((0 : ℝ) / 1) * (x)^0 + ((0 : ℝ) / 1) * (x)^1 + ((0 : ℝ) / 1) * (x)^3 + ((0 : ℝ) / 1) * (x)^6 + ((0 : ℝ) / 1) * (x)^10 + ((0 : ℝ) / 1) * (x)^15 + ((0 : ℝ) / 1) * (x)^21 + ((1 : ℝ) / 1) * (x)^28)

theorem nonnegative (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ polynomial x := by
  have h0 := squareTerm_nonnegative ({ weight := ((1 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have hsum : 0 ≤ ((({ weight := ((1 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x) := h0
  have identity : polynomial x = ((({ weight := ((1 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x) := by
    dsimp [polynomial, SquareTerm.eval, evalPolynomial]
    ring
  rw [identity]
  exact hsum

theorem nonzero_value : polynomial 1 ≠ 0 := by
  norm_num [polynomial]

theorem annihilation : (((0 : ℝ) / 1) * ((1 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((1 : ℝ) / 1) * ((0 : ℝ) / 1)) = 0 := by
  norm_num

theorem finite_supported_bank {A : Type*} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((0 : ℝ) / 1))
    (moment2 : ∑ a, weight a * (value a)^3 = ((0 : ℝ) / 1))
    (moment3 : ∑ a, weight a * (value a)^6 = ((0 : ℝ) / 1))
    (moment4 : ∑ a, weight a * (value a)^10 = ((0 : ℝ) / 1))
    (moment5 : ∑ a, weight a * (value a)^15 = ((0 : ℝ) / 1))
    (moment6 : ∑ a, weight a * (value a)^21 = ((0 : ℝ) / 1))
    (moment7 : ∑ a, weight a * (value a)^28 = ((0 : ℝ) / 1))
    (a : A) (ha : 0 < weight a) :
    polynomial (value a) = 0 ∧ value a ∈ Set.Ioc (0 : ℝ) 1 := by
  have zero : ∑ b, weight b * polynomial (value b) = 0 := by
    calc
      _ = ∑ b, (((0 : ℝ) / 1) * (weight b * (value b)^0) + ((0 : ℝ) / 1) * (weight b * (value b)^1) + ((0 : ℝ) / 1) * (weight b * (value b)^3) + ((0 : ℝ) / 1) * (weight b * (value b)^6) + ((0 : ℝ) / 1) * (weight b * (value b)^10) + ((0 : ℝ) / 1) * (weight b * (value b)^15) + ((0 : ℝ) / 1) * (weight b * (value b)^21) + ((1 : ℝ) / 1) * (weight b * (value b)^28)) := by
        apply Finset.sum_congr rfl
        intro b _
        dsimp [polynomial]
        ring
      _ = (((0 : ℝ) / 1) * (∑ b, weight b * (value b)^0) + ((0 : ℝ) / 1) * (∑ b, weight b * (value b)^1) + ((0 : ℝ) / 1) * (∑ b, weight b * (value b)^3) + ((0 : ℝ) / 1) * (∑ b, weight b * (value b)^6) + ((0 : ℝ) / 1) * (∑ b, weight b * (value b)^10) + ((0 : ℝ) / 1) * (∑ b, weight b * (value b)^15) + ((0 : ℝ) / 1) * (∑ b, weight b * (value b)^21) + ((1 : ℝ) / 1) * (∑ b, weight b * (value b)^28)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by
        rw [moment0, moment1, moment2, moment3, moment4, moment5, moment6, moment7]
        norm_num
  exact ⟨supported_atom_is_root weight value polynomial hw
    (fun b => nonnegative (value b) (hv b).1.le (hv b).2) zero a ha, hv a⟩

#print axioms nonnegative
#print axioms nonzero_value
#print axioms annihilation
#print axioms finite_supported_bank

end Astra.Generated.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60
