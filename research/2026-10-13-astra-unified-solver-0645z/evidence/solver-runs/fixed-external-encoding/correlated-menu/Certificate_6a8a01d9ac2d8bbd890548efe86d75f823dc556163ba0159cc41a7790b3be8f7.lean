import Astra.CommonCertificateKernel

/- Exact certificate SHA256: 6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7. Generation is not compilation. -/
namespace Astra.Generated.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7
open Astra.CommonCertificateKernel
open scoped BigOperators

def polynomial (x : ℝ) : ℝ := (((1 : ℝ) / 32) * (x)^0 + ((-3 : ℝ) / 16) * (x)^1 + ((1 : ℝ) / 1) * (x)^3)

theorem nonnegative (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ polynomial x := by
  have h0 := squareTerm_nonnegative ({ weight := ((1 : ℝ) / 2), left := false, right := false, square := [((-1 : ℝ) / 4), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h1 := squareTerm_nonnegative ({ weight := ((1 : ℝ) / 1), left := true, right := false, square := [((-1 : ℝ) / 4), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have hsum : 0 ≤ ((({ weight := ((1 : ℝ) / 2), left := false, right := false, square := [((-1 : ℝ) / 4), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((1 : ℝ) / 1), left := true, right := false, square := [((-1 : ℝ) / 4), ((1 : ℝ) / 1)] } : SquareTerm)).eval x) := (add_nonneg h0 h1)
  have identity : polynomial x = ((({ weight := ((1 : ℝ) / 2), left := false, right := false, square := [((-1 : ℝ) / 4), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((1 : ℝ) / 1), left := true, right := false, square := [((-1 : ℝ) / 4), ((1 : ℝ) / 1)] } : SquareTerm)).eval x) := by
    dsimp [polynomial, SquareTerm.eval, evalPolynomial]
    ring
  rw [identity]
  exact hsum

theorem nonzero_value : polynomial 0 ≠ 0 := by
  norm_num [polynomial]

theorem annihilation : (((1 : ℝ) / 32) * ((1 : ℝ) / 1) + ((-3 : ℝ) / 16) * ((1 : ℝ) / 4) + ((1 : ℝ) / 1) * ((1 : ℝ) / 64)) = 0 := by
  norm_num

theorem finite_supported_bank {A : Type*} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 4))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 64))
    (a : A) (ha : 0 < weight a) :
    polynomial (value a) = 0 ∧ value a ∈ Set.Ioc (0 : ℝ) 1 := by
  have zero : ∑ b, weight b * polynomial (value b) = 0 := by
    calc
      _ = ∑ b, (((1 : ℝ) / 32) * (weight b * (value b)^0) + ((-3 : ℝ) / 16) * (weight b * (value b)^1) + ((1 : ℝ) / 1) * (weight b * (value b)^3)) := by
        apply Finset.sum_congr rfl
        intro b _
        dsimp [polynomial]
        ring
      _ = (((1 : ℝ) / 32) * (∑ b, weight b * (value b)^0) + ((-3 : ℝ) / 16) * (∑ b, weight b * (value b)^1) + ((1 : ℝ) / 1) * (∑ b, weight b * (value b)^3)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by
        rw [moment0, moment1, moment2]
        norm_num
  exact ⟨supported_atom_is_root weight value polynomial hw
    (fun b => nonnegative (value b) (hv b).1.le (hv b).2) zero a ha, hv a⟩

#print axioms nonnegative
#print axioms nonzero_value
#print axioms annihilation
#print axioms finite_supported_bank

end Astra.Generated.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7
