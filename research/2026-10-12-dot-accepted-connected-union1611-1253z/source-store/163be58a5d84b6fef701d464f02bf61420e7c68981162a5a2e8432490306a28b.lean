import G3CriticalCoefficientLists

/-! Exact nested coefficient arithmetic. The outer variable is the Bernoulli
probability p and the inner variable is the supplied residue r. -/
noncomputable section
namespace GProgram.G3.CriticalCertificates
open Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def ofRows (xs : List (List ℤ)) : Polynomial (Polynomial ℤ) :=
  ofCoeffs (xs.map ofCoeffs)

def addRows : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], bs => bs
  | as, [] => as
  | a::as, b::bs => addCoeffs a b :: addRows as bs

def scaleRows (a : List ℤ) (bs : List (List ℤ)) : List (List ℤ) :=
  bs.map (mulCoeffs a)

def mulRows : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], _ => []
  | a::as, bs => addRows (scaleRows a bs) ([] :: mulRows as bs)

theorem map_addRows (as bs : List (List ℤ)) :
    (addRows as bs).map ofCoeffs = addCoeffs (as.map ofCoeffs) (bs.map ofCoeffs) := by
  induction as generalizing bs with
  | nil => simp [addRows, addCoeffs]
  | cons a as ih => cases bs <;> simp [addRows, addCoeffs, ofCoeffs_add, ih]

theorem map_scaleRows (a : List ℤ) (bs : List (List ℤ)) :
    (scaleRows a bs).map ofCoeffs = scaleCoeffs (ofCoeffs a) (bs.map ofCoeffs) := by
  simp [scaleRows, scaleCoeffs, List.map_map, ofCoeffs_mul]

theorem map_mulRows (as bs : List (List ℤ)) :
    (mulRows as bs).map ofCoeffs = mulCoeffs (as.map ofCoeffs) (bs.map ofCoeffs) := by
  induction as with
  | nil => simp [mulRows, mulCoeffs]
  | cons a as ih => simp [mulRows, map_addRows, map_scaleRows, mulCoeffs, ih, ofCoeffs]

theorem ofRows_add (as bs : List (List ℤ)) :
    ofRows (addRows as bs) = ofRows as + ofRows bs := by
  rw [ofRows, map_addRows, ofCoeffs_add]; rfl

theorem ofRows_mul (as bs : List (List ℤ)) :
    ofRows (mulRows as bs) = ofRows as * ofRows bs := by
  rw [ofRows, map_mulRows, ofCoeffs_mul]; rfl

theorem coeff_ofRows (as : List (List ℤ)) (n : ℕ) :
    (ofRows as).coeff n = ofCoeffs (as.getD n []) := by
  rw [ofRows, coeff_ofCoeffs]
  induction as generalizing n with
  | nil => simp [ofCoeffs]
  | cons a as ih => cases n <;> simp_all

theorem natDegree_ofRows_le (as : List (List ℤ)) :
    (ofRows as).natDegree ≤ as.length - 1 := by
  simpa [ofRows] using natDegree_ofCoeffs_le (as.map ofCoeffs)

theorem ofCoeffs_append_zeros (as : List ℤ) (n : ℕ) :
    ofCoeffs (as ++ List.replicate n 0) = ofCoeffs as := by
  induction as with
  | nil => simp [ofCoeffs_zeros, ofCoeffs]
  | cons a as ih => simp [ofCoeffs, ih]

end GProgram.G3.CriticalCertificates
