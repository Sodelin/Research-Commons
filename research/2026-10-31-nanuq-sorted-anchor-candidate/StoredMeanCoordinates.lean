import QueryCoordinates

/-! UNCOMPILED exact mean/bit coordinate comparison. Left/right cut
membership and resolution multiplicities remain distinct-set semantics. -/
set_option debug.skipKernelTC false
namespace Nanuq.ActualFinite
open Nanuq.AdjacentCertificate Nanuq.Restriction

theorem three_filter_ratio (g h : Nat → Bool) :
    ((((List.range 3).filter g).filter h).length : ℚ) / (((List.range 3).filter g).length : ℚ)=
      (((presentIndices (fun r => g r.val)).filter (fun r => h r.val)).length : ℚ) /
        ((presentIndices (fun r => g r.val)).length : ℚ) := by
  change (((([0,1,2] : List Nat).filter g).filter h).length : ℚ) /
      ((([0,1,2] : List Nat).filter g).length : ℚ)=_
  cases hg0 : g 0 <;> cases hg1 : g 1 <;> cases hg2 : g 2 <;>
    cases hh0 : h 0 <;> cases hh1 : h 1 <;> cases hh2 : h 2 <;>
    simp [presentIndices,hg0,hg1,hg2,hh0,hh1,hh2]

theorem finiteWitnessMask_code (T : Tree) (tips : List Nat) (qs : List Quartet)
    (idx : Nat) (v : Fin 4 → Nat) (hv : qs[idx]?=some (coordinateQuartet v)) (r : Fin 3) :
    finiteWitnessMask T tips v r=
      (code (T.summary (edgeContribution tips qs) 1) idx).testBit r.val := by
  apply Bool.eq_iff_iff.mpr
  rw [finiteWitnessMask_iff]
  exact (summary_code_edge T tips qs idx (coordinateQuartet v) hv r.val r.isLt).symm

theorem indexedPairMean_code (T : Tree) (tips : List Nat) (qs : List Quartet)
    (idx : Nat) (v : Fin 4 ↪ Nat) (hv : qs[idx]?=some (coordinateQuartet v)) (i j : Fin 4) :
    indexedPairMean (finiteWitnessMask T tips v) i j=
      ((((List.range 3).filter (fun r => (code (T.summary (edgeContribution tips qs) 1) idx).testBit r)).filter
        (fun r => (coordinateQuartet v).side r (v i) != (coordinateQuartet v).side r (v j))).length : ℚ) /
        (((List.range 3).filter (fun r => (code (T.summary (edgeContribution tips qs) 1) idx).testBit r)).length : ℚ) := by
  rw [three_filter_ratio]
  have hg : finiteWitnessMask T tips v=
      fun r => (code (T.summary (edgeContribution tips qs) 1) idx).testBit r.val := by
    funext r
    exact finiteWitnessMask_code T tips qs idx v hv r
  simp only [indexedPairMean,hg,coordinate_side]

#print axioms indexedPairMean_code
end Nanuq.ActualFinite
