import ClosedDiskCarrierArc
import ClosedCrosscutCells

/-! UNCOMPILED. The original carriers may touch the Jordan boundary at any
number of points or arcs. Only ONE auxiliary crosscut is approximated. -/
set_option debug.skipKernelTC false
namespace Nanuq.ClosedDiskNoncrossing
open Set Schoenflies

/-- Two disjoint compact connected carriers in the CLOSED Jordan disk cannot
have alternating boundary endpoints. The original carrier Q is not perturbed
and is never assumed strictly inside C away from its two queried points. -/
theorem closed_disk_noninterlacing
    {C P Q A₁ A₂ : Set Plane} {p q r s : Plane}
    (hC : IsJordanCurve C) (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsCompact P) (hPc : IsPreconnected P)
    (hQ : IsCompact Q) (hQc : IsPreconnected Q)
    (hPQ : Disjoint P Q)
    (hPdisk : P ⊆ C ∪ inside C) (hQdisk : Q ⊆ C ∪ inside C)
    (hp : p∈P) (hq : q∈P) (hrQ : r∈Q) (hsQ : s∈Q)
    (hr : r∈A₁) (hs : s∈A₂) : False := by
  have hpq : p≠q := by
    obtain ⟨f,hf,hi,him,h0,h1⟩ := hcut.fst
    intro he
    have hz := hi zero_mem_I one_mem_I (h0.trans (he.trans h1.symm))
    norm_num at hz
  obtain ⟨A,hA,hAC,hAi,hAQ⟩ := closed_disk_carrier_proper_arc
    hC hP hPc hQ hPQ hPdisk hp hq
    (hcut.fst_subset hcut.fst.left_mem) (hcut.fst_subset hcut.fst.right_mem)
    hpq
  exact proper_crosscut_blocks_connected hC hcut hA hAC hAi
    hQc hQdisk hAQ.symm hrQ hsQ hr hs

#print axioms closed_disk_noninterlacing
end Nanuq.ClosedDiskNoncrossing
