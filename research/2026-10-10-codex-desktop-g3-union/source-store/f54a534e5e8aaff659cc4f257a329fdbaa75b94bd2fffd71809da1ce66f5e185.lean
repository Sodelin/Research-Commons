import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring

/-! Kernel-checkable coefficient-list interfaces for the actual critical
resultant certificates. No source determinant or source finiteness is assumed. -/
namespace GProgram.G3.CriticalCertificates
open Polynomial
variable {R : Type*} [CommRing R]

noncomputable def ofCoeffs : List R → Polynomial R
  | [] => 0
  | a :: as => C a + X * ofCoeffs as

def addCoeffs : List R → List R → List R
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a+b) :: addCoeffs as bs

def scaleCoeffs (a : R) (bs : List R) : List R := bs.map (a * ·)

def mulCoeffs : List R → List R → List R
  | [], _ => []
  | a :: as, bs => addCoeffs (scaleCoeffs a bs) (0 :: mulCoeffs as bs)

theorem ofCoeffs_add (as bs : List R) :
    ofCoeffs (addCoeffs as bs) = ofCoeffs as + ofCoeffs bs := by
  induction as generalizing bs with
  | nil => simp [addCoeffs, ofCoeffs]
  | cons a as ih =>
    cases bs with
    | nil => simp [addCoeffs, ofCoeffs]
    | cons b bs => simp only [addCoeffs, ofCoeffs, ih, map_add]; ring

theorem ofCoeffs_scale (a : R) (bs : List R) :
    ofCoeffs (scaleCoeffs a bs) = C a * ofCoeffs bs := by
  induction bs with
  | nil => simp [scaleCoeffs, ofCoeffs]
  | cons b bs ih =>
    change C (a*b) + X * ofCoeffs (scaleCoeffs a bs) =
      C a * (C b + X * ofCoeffs bs)
    rw [ih, map_mul]
    ring

theorem ofCoeffs_mul (as bs : List R) :
    ofCoeffs (mulCoeffs as bs) = ofCoeffs as * ofCoeffs bs := by
  induction as with
  | nil => simp [mulCoeffs, ofCoeffs]
  | cons a as ih =>
    rw [mulCoeffs, ofCoeffs_add, ofCoeffs_scale]
    simp only [ofCoeffs, map_zero, zero_add, ih]
    ring

theorem ofCoeffs_zeros (n : ℕ) :
    ofCoeffs (List.replicate n (0 : R)) = 0 := by
  induction n with
  | zero => simp [ofCoeffs]
  | succ n ih => simp [List.replicate_succ, ofCoeffs, ih]

theorem polynomial_identity_of_coefficient_identity
    (as bs cs ds : List R) (n : ℕ)
    (h : addCoeffs (mulCoeffs as bs) (mulCoeffs cs ds) =
      1 :: List.replicate n 0) :
    ofCoeffs as * ofCoeffs bs + ofCoeffs cs * ofCoeffs ds = 1 := by
  have he := congrArg ofCoeffs h
  simpa only [ofCoeffs_add, ofCoeffs_mul, ofCoeffs, ofCoeffs_zeros,
    mul_zero, add_zero, map_one] using he

theorem coeff_ofCoeffs (as : List R) (n : ℕ) :
    (ofCoeffs as).coeff n = as.getD n 0 := by
  induction as generalizing n with
  | nil => simp [ofCoeffs]
  | cons a as ih =>
    cases n with
    | zero => simp [ofCoeffs]
    | succ n => simp [ofCoeffs, Polynomial.coeff_X_mul, ih]

theorem natDegree_ofCoeffs_le (as : List R) :
    (ofCoeffs as).natDegree ≤ as.length - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_ofCoeffs]
  have hlen : as.length ≤ n := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]

theorem natDegree_ofCoeffs_eq (as : List R) (n : ℕ)
    (hlen : as.length = n+1) (hlast : as.getD n 0 ≠ 0) :
    (ofCoeffs as).natDegree = n := by
  apply le_antisymm
  · simpa only [hlen, Nat.add_sub_cancel] using natDegree_ofCoeffs_le as
  · apply Polynomial.le_natDegree_of_ne_zero
    simpa only [coeff_ofCoeffs] using hlast

theorem map_ofCoeffs {S : Type*} [CommRing S] (f : R →+* S) (as : List R) :
    (ofCoeffs as).map f = ofCoeffs (as.map f) := by
  induction as with
  | nil => simp [ofCoeffs]
  | cons a as ih => simp [ofCoeffs, Polynomial.map_add, Polynomial.map_mul, ih]

end GProgram.G3.CriticalCertificates
