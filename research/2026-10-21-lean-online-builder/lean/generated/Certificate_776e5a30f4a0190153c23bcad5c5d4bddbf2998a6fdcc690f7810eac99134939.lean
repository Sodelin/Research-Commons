import Astra.CommonCertificateKernel

/- Exact certificate SHA256: 776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939. Generation is not compilation. -/
namespace Astra.Generated.Certificate_776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939
open Astra.CommonCertificateKernel
open scoped BigOperators

noncomputable def polynomial (x : ℝ) : ℝ := (((151168 : ℝ) / 13640319) * (x)^0 + ((-3856 : ℝ) / 72171) * (x)^1 + ((11428 : ℝ) / 56133) * (x)^3 + ((-11323 : ℝ) / 18711) * (x)^6 + ((1 : ℝ) / 1) * (x)^10)

theorem nonnegative (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ polynomial x := by
  have h0 := squareTerm_nonnegative ({ weight := ((37792 : ℝ) / 168399), left := false, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h1 := squareTerm_nonnegative ({ weight := ((17548 : ℝ) / 18711), left := true, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h2 := squareTerm_nonnegative ({ weight := ((35108 : ℝ) / 18711), left := false, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h3 := squareTerm_nonnegative ({ weight := ((8 : ℝ) / 3), left := true, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h4 := squareTerm_nonnegative ({ weight := ((23 : ℝ) / 9), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h5 := squareTerm_nonnegative ({ weight := ((2 : ℝ) / 1), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h6 := squareTerm_nonnegative ({ weight := ((1 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have hsum : 0 ≤ ((({ weight := ((37792 : ℝ) / 168399), left := false, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((17548 : ℝ) / 18711), left := true, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((35108 : ℝ) / 18711), left := false, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((8 : ℝ) / 3), left := true, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((23 : ℝ) / 9), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((2 : ℝ) / 1), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((1 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6)
  have identity : polynomial x = ((({ weight := ((37792 : ℝ) / 168399), left := false, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((17548 : ℝ) / 18711), left := true, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((35108 : ℝ) / 18711), left := false, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((8 : ℝ) / 3), left := true, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((23 : ℝ) / 9), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((2 : ℝ) / 1), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((1 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x) := by
    dsimp [polynomial, SquareTerm.eval, evalPolynomial]
    ring
  rw [identity]
  exact hsum

theorem nonzero_value : polynomial 0 ≠ 0 := by
  norm_num [polynomial]

theorem annihilation : (((151168 : ℝ) / 13640319) * ((1 : ℝ) / 1) + ((-3856 : ℝ) / 72171) * ((1 : ℝ) / 2) + ((11428 : ℝ) / 56133) * ((1 : ℝ) / 6) + ((-11323 : ℝ) / 18711) * ((65 : ℝ) / 1458) + ((1 : ℝ) / 1) * ((1025 : ℝ) / 118098)) = 0 := by
  norm_num

theorem finite_supported_bank {A : Type*} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 2))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 6))
    (moment3 : ∑ a, weight a * (value a)^6 = ((65 : ℝ) / 1458))
    (moment4 : ∑ a, weight a * (value a)^10 = ((1025 : ℝ) / 118098))
    (a : A) (ha : 0 < weight a) :
    polynomial (value a) = 0 ∧ value a ∈ Set.Ioc (0 : ℝ) 1 := by
  have zero : ∑ b, weight b * polynomial (value b) = 0 := by
    calc
      _ = ∑ b, (((151168 : ℝ) / 13640319) * (weight b * (value b)^0) + ((-3856 : ℝ) / 72171) * (weight b * (value b)^1) + ((11428 : ℝ) / 56133) * (weight b * (value b)^3) + ((-11323 : ℝ) / 18711) * (weight b * (value b)^6) + ((1 : ℝ) / 1) * (weight b * (value b)^10)) := by
        apply Finset.sum_congr rfl
        intro b _
        dsimp [polynomial]
        ring
      _ = (((151168 : ℝ) / 13640319) * (∑ b, weight b * (value b)^0) + ((-3856 : ℝ) / 72171) * (∑ b, weight b * (value b)^1) + ((11428 : ℝ) / 56133) * (∑ b, weight b * (value b)^3) + ((-11323 : ℝ) / 18711) * (∑ b, weight b * (value b)^6) + ((1 : ℝ) / 1) * (∑ b, weight b * (value b)^10)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by
        rw [moment0, moment1, moment2, moment3, moment4]
        norm_num
  exact ⟨supported_atom_is_root weight value polynomial hw
    (fun b => nonnegative (value b) (hv b).1.le (hv b).2) zero a ha, hv a⟩

#print axioms nonnegative
#print axioms nonzero_value
#print axioms annihilation
#print axioms finite_supported_bank

end Astra.Generated.Certificate_776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939
