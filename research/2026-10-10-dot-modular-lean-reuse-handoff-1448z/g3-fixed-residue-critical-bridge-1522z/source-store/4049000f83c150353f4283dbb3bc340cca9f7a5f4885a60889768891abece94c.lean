import G3CriticalSliceCoefficientData
import G3AllResiduePositivity

/-! Exact binding from the coefficient certificate G to the already proved
positive factor product. Source slice Bezout identities remain separate. -/
noncomputable section
namespace GProgram.G3.CriticalCertificates
open Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def factorCoeffs0 : List ℤ := [0, 1]

def factorCoeffs1 : List ℤ := [1, -1, 1]

def factorCoeffs2 : List ℤ := [1, 1, 1]

def factorCoeffs3 : List ℤ := [1, 1, 1, 1, 1]

def factorCoeffs4 : List ℤ := [5, 15, 25, 75, 94, 167, 246, 278, 347, 410, 351, 410, 347, 278, 246, 167, 94, 75, 25, 15, 5]

def factorCoeffs5 : List ℤ := [8, 8, 32, 52, 100, 135, 243, 308, 422, 557, 690, 735, 958, 943, 1002, 1089, 1002, 943, 958, 735, 690, 557, 422, 308, 243, 135, 100, 52, 32, 8, 8]

def factorCoeffs6 : List ℤ := [11, 33, 55, 165, 218, 401, 610, 794, 1077, 1430, 1585, 2062, 2244, 2515, 2720, 2875, 2835, 2875, 2720, 2515, 2244, 2062, 1585, 1430, 1077, 794, 610, 401, 218, 165, 55, 33, 11]

def factorCoeffs7 : List ℤ := [1, 1, -1, 9, 0, 5, 26, 6, 19, 64, 6, 66, 79, 29, 105, 84, 45, 137, 45, 84, 105, 29, 79, 66, 6, 64, 19, 6, 26, 5, 0, 9, -1, 1, 1]

def factorCoeffs8 : List ℤ := [8, 8, 40, 72, 152, 163, 503, 355, 887, 1042, 1243, 1643, 2315, 1682, 3187, 2530, 2690, 3385, 2690, 2530, 3187, 1682, 2315, 1643, 1243, 1042, 887, 355, 503, 163, 152, 72, 40, 8, 8]

def factorCoeffs9 : List ℤ := [7, 28, 64, 157, 310, 553, 933, 1505, 2217, 3252, 4490, 5973, 7718, 9670, 11567, 13672, 15465, 17018, 18246, 19047, 19191, 19047, 18246, 17018, 15465, 13672, 11567, 9670, 7718, 5973, 4490, 3252, 2217, 1505, 933, 553, 310, 157, 64, 28, 7]

def powerCoeffs (as : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n+1 => mulCoeffs as (powerCoeffs as n)

theorem ofCoeffs_power (as : List ℤ) (n : ℕ) :
    ofCoeffs (powerCoeffs as n) = (ofCoeffs as)^n := by
  induction n with
  | zero => simp [powerCoeffs, ofCoeffs]
  | succ n ih => rw [powerCoeffs, ofCoeffs_mul, ih, pow_succ]; ring

def factorProductCoeffs : List ℤ := mulCoeffs (mulCoeffs (mulCoeffs (mulCoeffs (mulCoeffs (mulCoeffs (mulCoeffs (mulCoeffs (mulCoeffs (powerCoeffs factorCoeffs0 22) (powerCoeffs factorCoeffs1 3)) (powerCoeffs factorCoeffs2 6)) (powerCoeffs factorCoeffs3 2)) (powerCoeffs factorCoeffs4 1)) (powerCoeffs factorCoeffs5 1)) (powerCoeffs factorCoeffs6 1)) (powerCoeffs factorCoeffs7 1)) (powerCoeffs factorCoeffs8 1)) (powerCoeffs factorCoeffs9 1)
theorem factor_product_coefficients : factorProductCoeffs = gCoeffs := by decide

theorem factor0_eval (r : ℝ) :
    (ofCoeffs factorCoeffs0).eval₂ (Int.castRingHom ℝ) r = AllResidue.factor0 r := by
  norm_num [factorCoeffs0, ofCoeffs, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    AllResidue.factor0, AllResidue.exceptionalJ]
  <;> ring

theorem factor1_eval (r : ℝ) :
    (ofCoeffs factorCoeffs1).eval₂ (Int.castRingHom ℝ) r = AllResidue.factor1 r := by
  norm_num [factorCoeffs1, ofCoeffs, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    AllResidue.factor1, AllResidue.exceptionalJ]
  <;> ring

theorem factor2_eval (r : ℝ) :
    (ofCoeffs factorCoeffs2).eval₂ (Int.castRingHom ℝ) r = AllResidue.factor2 r := by
  norm_num [factorCoeffs2, ofCoeffs, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    AllResidue.factor2, AllResidue.exceptionalJ]
  <;> ring

theorem factor3_eval (r : ℝ) :
    (ofCoeffs factorCoeffs3).eval₂ (Int.castRingHom ℝ) r = AllResidue.factor3 r := by
  norm_num [factorCoeffs3, ofCoeffs, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    AllResidue.factor3, AllResidue.exceptionalJ]
  <;> ring

theorem factor4_eval (r : ℝ) :
    (ofCoeffs factorCoeffs4).eval₂ (Int.castRingHom ℝ) r = AllResidue.factor4 r := by
  norm_num [factorCoeffs4, ofCoeffs, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    AllResidue.factor4, AllResidue.exceptionalJ]
  <;> ring

theorem factor5_eval (r : ℝ) :
    (ofCoeffs factorCoeffs5).eval₂ (Int.castRingHom ℝ) r = AllResidue.factor5 r := by
  norm_num [factorCoeffs5, ofCoeffs, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    AllResidue.factor5, AllResidue.exceptionalJ]
  <;> ring

theorem factor6_eval (r : ℝ) :
    (ofCoeffs factorCoeffs6).eval₂ (Int.castRingHom ℝ) r = AllResidue.factor6 r := by
  norm_num [factorCoeffs6, ofCoeffs, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    AllResidue.factor6, AllResidue.exceptionalJ]
  <;> ring

theorem factor7_eval (r : ℝ) :
    (ofCoeffs factorCoeffs7).eval₂ (Int.castRingHom ℝ) r = AllResidue.factor7 r := by
  norm_num [factorCoeffs7, ofCoeffs, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    AllResidue.factor7, AllResidue.exceptionalJ]
  <;> ring

theorem factor8_eval (r : ℝ) :
    (ofCoeffs factorCoeffs8).eval₂ (Int.castRingHom ℝ) r = AllResidue.factor8 r := by
  norm_num [factorCoeffs8, ofCoeffs, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    AllResidue.factor8, AllResidue.exceptionalJ]
  <;> ring

theorem factor9_eval (r : ℝ) :
    (ofCoeffs factorCoeffs9).eval₂ (Int.castRingHom ℝ) r = AllResidue.factor9 r := by
  norm_num [factorCoeffs9, ofCoeffs, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    AllResidue.factor9, AllResidue.exceptionalJ]
  <;> ring

theorem g_eval_eq_positive_product (r : ℝ) :
    (ofCoeffs gCoeffs).eval₂ (Int.castRingHom ℝ) r = AllResidue.criticalGcdProduct r := by
  have h := congrArg (fun p : Polynomial ℤ => p.eval₂ (Int.castRingHom ℝ) r)
    (congrArg ofCoeffs factor_product_coefficients)
  simp only [factorProductCoeffs, ofCoeffs_mul, ofCoeffs_power,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, factor0_eval, factor1_eval, factor2_eval, factor3_eval, factor4_eval, factor5_eval, factor6_eval, factor7_eval, factor8_eval, factor9_eval] at h
  simpa only [AllResidue.criticalGcdProduct] using h.symm

theorem g_eval_pos {r : ℝ} (hr : 0 < r) :
    0 < (ofCoeffs gCoeffs).eval₂ (Int.castRingHom ℝ) r := by
  rw [g_eval_eq_positive_product]
  exact AllResidue.critical_gcd_product_pos hr

#print axioms factor_product_coefficients
#print axioms g_eval_pos
end GProgram.G3.CriticalCertificates
