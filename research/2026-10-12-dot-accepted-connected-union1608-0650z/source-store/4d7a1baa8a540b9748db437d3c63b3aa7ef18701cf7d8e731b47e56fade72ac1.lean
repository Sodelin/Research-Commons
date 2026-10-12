import G3CriticalBivariateLists

/-! Exact, generic reconstruction of a Bezout identity from residue blocks.
The multipliers are constructed by this proof; equality to any external
multiplier is neither assumed nor needed. -/
noncomputable section
namespace GProgram.G3.CriticalCertificates
open Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def shiftRows (n : ℕ) (as : List (List ℤ)) : List (List ℤ) :=
  as.map (fun a => List.replicate n 0 ++ a)

theorem ofCoeffs_zeros_append (n : ℕ) (as : List ℤ) :
    ofCoeffs (List.replicate n 0 ++ as) = X^n * ofCoeffs as := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ofCoeffs, ih, pow_succ]; ring

theorem ofRows_shiftRows (n : ℕ) (as : List (List ℤ)) :
    ofRows (shiftRows n as) = C (X^n) * ofRows as := by
  induction as with
  | nil => simp [shiftRows, ofRows, ofCoeffs]
  | cons a as ih =>
    change C (ofCoeffs (List.replicate n 0 ++ a)) + X * ofRows (shiftRows n as) =
      C (X^n) * (C (ofCoeffs a) + X * ofRows as)
    rw [ofCoeffs_zeros_append, ih, map_mul]
    ring

def combineRows (n : ℕ) : List (List (List ℤ)) → List (List ℤ)
  | [] => []
  | a::as => addRows a (shiftRows n (combineRows n as))

structure RowBezoutData where
  u : List (List ℤ)
  v : List (List ℤ)
  t : List (List ℤ)

theorem reconstruct_block_bezout (n : ℕ) (P Q : Polynomial (Polynomial ℤ))
    (bs : List RowBezoutData)
    (h : ∀ b ∈ bs, ofRows b.u * P + ofRows b.v * Q = ofRows b.t) :
    ofRows (combineRows n (bs.map RowBezoutData.u)) * P +
    ofRows (combineRows n (bs.map RowBezoutData.v)) * Q =
    ofRows (combineRows n (bs.map RowBezoutData.t)) := by
  induction bs with
  | nil => simp [combineRows, ofRows, ofCoeffs]
  | cons b bs ih =>
    have hb := h b (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.map_cons, combineRows, ofRows_add, ofRows_shiftRows]
    calc
      _ = (ofRows b.u * P + ofRows b.v * Q) + C (X^n) *
          (ofRows (combineRows n (bs.map RowBezoutData.u)) * P +
           ofRows (combineRows n (bs.map RowBezoutData.v)) * Q) := by ring
      _ = _ := by rw [hb, ht]

end GProgram.G3.CriticalCertificates
