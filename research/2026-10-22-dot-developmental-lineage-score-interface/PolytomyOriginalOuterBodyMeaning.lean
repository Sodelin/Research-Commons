/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact ORIGINAL real-block bytes and comb-cost increment for the concrete
global body, ONLY when its actually read current counter selects i<m.
-/
import PolytomyActualOuterBlockLoop

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem globalRealBlockBody_original (R : RawMSSCRecord) (hR : RawMSSCValid R) (L acc : ℕ)
    (i : Fin R.rows.length) (s : CanonicalGlobalStore) (hs : GlobalCanonicalInv R L s)
    (hindex : (s.stk (.inr .blockCounter)).length = i.val)
    (hcost : s.stk (globalFilterPort .cost) = List.replicate acc true) :
    (globalRealBlockBodyEval R s).stk (globalFilterPort .output) =
      rawRowBlockBits R (some i) ++ s.stk (globalFilterPort .output) ∧
      (globalRealBlockBodyEval R s).stk (globalFilterPort .cost) =
        List.replicate (acc + combTailCost (rawRowAlphabet R) 1 ((rawRowCodes R (some i)).length - 1)) true := by
  let p := globalRealBlockPrepared s
  have hiword : s.stk (.inr .blockCounter) = List.replicate i.val true := by
    have h := hs.counter_unary
    unfold IsUnaryWord at h
    rw [hindex] at h
    exact h
  obtain ⟨hA, hrem, hrow, hT, hblock⟩ := physicalBlockPrepare_values true .blockCounter .markerThreshold
    (rawRowAlphabet R) i.val (originalMarkerThreshold R) s hs.alphabet hiword hs.marker hs.type_empty hs.remaining_empty
  obtain ⟨hop, hu, hcnt, hf⟩ := globalRealPrepared_ready R L s hs
  have hp : OriginalBlockSemanticInv R (some i) L (rawRowAlphabet R) R.rows.length (R.rows.length + 1)
      (canonicalGlobalBase p) := by
    refine ⟨hop, ?_, ?_, ?_⟩
    · rw [show p.stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) from
        globalRealPrepared_old s _]; exact hs.parsed
    · change (p.stk (globalFilterPort .rowIndex)).length = i.val
      rw [hrow, List.length_replicate]
    · simpa [blockCode] using hblock
  have hpcost : p.stk (globalFilterPort .cost) = List.replicate acc true := by
    rw [physicalBlockPrepare_extra _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hcost
  have hpout : p.stk (globalFilterPort .output) = s.stk (globalFilterPort .output) :=
    physicalBlockPrepare_extra _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n, hn, he, hout, hcost', htype, hcount, hremaining, hscan, hquery, hrecord, hflag⟩ :=
    originalCanonicalBlock_executes R hR (some i) L R.rows.length (R.rows.length + 1) acc
      (canonicalGlobalBase p) hp hf hA hrem hcnt hpcost
  refine ⟨?_, hcost'⟩
  change (originalCanonicalBlockEval R (some i) (canonicalGlobalBase p)).stk (.inr .output) = _
  rw [hout]
  change rawRowBlockBits R (some i) ++ p.stk (globalFilterPort .output) = _
  rw [hpout]

/- The premise i<m belongs to this ORIGINAL observation theorem, not
the generic operational body contract. The actual outer pop will prove
it before every genuine real-block invocation. No row is skipped or
replaced and the cost is the original fixed-comb D_lambda contribution.
-/

end PolytomyReductionModel
