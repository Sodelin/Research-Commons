import Astra.CommonCertificateKernel

/- Exact certificate SHA256: cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54. Generation is not compilation. -/
namespace Astra.Generated.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54
open Astra.CommonCertificateKernel
open scoped BigOperators

noncomputable def polynomial (x : ℝ) : ℝ := (((0 : ℝ) / 1) * (x)^0 + ((1 : ℝ) / 1) * (x)^1)

theorem nonnegative (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ polynomial x := by
  have h0 := squareTerm_nonnegative ({ weight := ((1 : ℝ) / 1), left := true, right := false, square := [((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have hsum : 0 ≤ ((({ weight := ((1 : ℝ) / 1), left := true, right := false, square := [((1 : ℝ) / 1)] } : SquareTerm)).eval x) := h0
  have identity : polynomial x = ((({ weight := ((1 : ℝ) / 1), left := true, right := false, square := [((1 : ℝ) / 1)] } : SquareTerm)).eval x) := by
    dsimp [polynomial, SquareTerm.eval, evalPolynomial]
    ring
  rw [identity]
  exact hsum

theorem nonzero_value : polynomial 1 ≠ 0 := by
  norm_num [polynomial]

theorem annihilation : (((0 : ℝ) / 1) * ((1 : ℝ) / 1) + ((1 : ℝ) / 1) * ((0 : ℝ) / 1)) = 0 := by
  norm_num

theorem finite_supported_bank {A : Type*} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((0 : ℝ) / 1))
    (a : A) (ha : 0 < weight a) :
    polynomial (value a) = 0 ∧ value a ∈ Set.Ioc (0 : ℝ) 1 := by
  have zero : ∑ b, weight b * polynomial (value b) = 0 := by
    calc
      _ = ∑ b, (((0 : ℝ) / 1) * (weight b * (value b)^0) + ((1 : ℝ) / 1) * (weight b * (value b)^1)) := by
        apply Finset.sum_congr rfl
        intro b _
        dsimp [polynomial]
        ring
      _ = (((0 : ℝ) / 1) * (∑ b, weight b * (value b)^0) + ((1 : ℝ) / 1) * (∑ b, weight b * (value b)^1)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by
        rw [moment0, moment1]
        norm_num
  exact ⟨supported_atom_is_root weight value polynomial hw
    (fun b => nonnegative (value b) (hv b).1.le (hv b).2) zero a ha, hv a⟩

#print axioms nonnegative
#print axioms nonzero_value
#print axioms annihilation
#print axioms finite_supported_bank

end Astra.Generated.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54
