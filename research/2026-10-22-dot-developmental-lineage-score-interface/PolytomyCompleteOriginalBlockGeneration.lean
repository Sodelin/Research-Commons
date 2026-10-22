/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Complete ACTUAL original block generation from the preserved valid record:
physical scalar initialization, all descending real blocks, then the
physical anchor. Exact original ordered block bytes and ORIGINAL C0.
-/
import PolytomyGlobalAnchorBlockBody

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem globalAnchorBlockBody_original (R : RawMSSCRecord) (hR : RawMSSCValid R) (L acc : ℕ)
    (s : CanonicalGlobalStore) (hs : GlobalCanonicalInv R L s)
    (hcost : s.stk (globalFilterPort .cost) = List.replicate acc true) :
    (globalAnchorBlockBodyEval R s).stk (globalFilterPort .output) =
      rawRowBlockBits R none ++ s.stk (globalFilterPort .output) ∧
      (globalAnchorBlockBodyEval R s).stk (globalFilterPort .cost) =
        List.replicate (acc + combTailCost (rawRowAlphabet R) 1 ((rawRowCodes R none).length - 1)) true := by
  let p := globalAnchorBlockPrepared s
  obtain ⟨hA, hrem, hrow, hT, hblock⟩ := physicalBlockPrepare_values false .rowCount .universe
    (rawRowAlphabet R) R.rows.length R.N s hs.alphabet hs.rows hs.universe hs.type_empty hs.remaining_empty
  obtain ⟨hop, hu, hcnt, hf⟩ := globalAnchorPrepared_ready R L s hs
  have hp : OriginalBlockSemanticInv R none L (rawRowAlphabet R) R.rows.length (R.rows.length + 1)
      (canonicalGlobalBase p) := by
    refine ⟨hop, ?_, ?_, ?_⟩
    · rw [show p.stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) from
        globalAnchorPrepared_old s _]; exact hs.parsed
    · change (p.stk (globalFilterPort .rowIndex)).length = R.rows.length
      rw [hrow, List.length_replicate]
    · simpa [blockCode] using hblock
  have hpcost : p.stk (globalFilterPort .cost) = List.replicate acc true := by
    rw [physicalBlockPrepare_extra _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hcost
  have hpout : p.stk (globalFilterPort .output) = s.stk (globalFilterPort .output) :=
    physicalBlockPrepare_extra _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n, hn, he, hout, hcost', htype, hcount, hremaining, hscan, hquery, hrecord, hflag⟩ :=
    originalCanonicalBlock_executes R hR none L R.rows.length (R.rows.length + 1) acc
      (canonicalGlobalBase p) hp hf hA hrem hcnt hpcost
  refine ⟨?_, hcost'⟩
  change (originalCanonicalBlockEval R none (canonicalGlobalBase p)).stk (.inr .output) = _
  rw [hout]
  change rawRowBlockBits R none ++ p.stk (globalFilterPort .output) = _
  rw [hpout]

def canonicalAllBlocksRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq canonicalRealBlocksRoutine globalAnchorBlockBodyRoutine

def canonicalAllBlocksEval (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  globalAnchorBlockBodyEval R (canonicalRealBlocksEval R s)

def canonicalAllBlocksBound (R : RawMSSCRecord) (L : ℕ) :=
  canonicalGlobalsBound L + globalRealBlocksBound R L + globalAnchorBlockBodyBound R L

theorem canonicalAllBlocks_executes (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s))
    (hq : s.stk (globalScanPort (.inr .queries)) = [])
    (hglobals : ∀ k : CanonicalGlobalPort, s.stk (.inr k) = [])
    (hfilters : ∀ k : CanonicalFilterPort, s.stk (globalFilterPort k) = [])
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    ∃ n ≤ canonicalAllBlocksBound R L,
      canonicalAllBlocksRoutine.Executes s (canonicalAllBlocksEval R s) n ∧
      GlobalCanonicalInv R L (canonicalAllBlocksEval R s) ∧
      (canonicalAllBlocksEval R s).stk (.inr .blockCounter) = [] ∧
      (canonicalAllBlocksEval R s).stk (globalFilterPort .output) =
        (blockIndexList R.rows.length).flatMap (rawRowBlockBits R) ∧
      (canonicalAllBlocksEval R s).stk (globalFilterPort .cost) = List.replicate (rawRowFixedCost R) true ∧
      (canonicalAllBlocksEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) := by
  obtain ⟨a, ha, hea, hi, hcounter, hbytes, hcost, horig⟩ :=
    canonicalRealBlocks_executes R hR L s hs hq hglobals hfilters hparse
  obtain ⟨b, hb, heb, hi', horig'⟩ := globalAnchorBlockBody_executes R L (canonicalRealBlocksEval R s) hi
  obtain ⟨hanchorBytes, hanchorCost⟩ := globalAnchorBlockBody_original R hR L
    (originalRealBlocksCost R R.rows.length) (canonicalRealBlocksEval R s) hi hcost
  have hall := RoutineComposition.seq_executes _ _ hea heb
  refine ⟨a + b, by unfold canonicalAllBlocksBound; omega, hall, hi', ?_, ?_, ?_, ?_⟩
  · rw [globalAnchorBlockBody_globals]; exact hcounter
  · rw [hanchorBytes, hbytes, originalBlockList_bits]
  · rw [hanchorCost, originalFixedCost_parts, Nat.add_comm]
  · rw [horig', horig]

/- This endpoint is the COMPLETE ORIGINAL block generator and C0
accumulator from physical original-record input and fresh caller tapes.
It includes actual initialization, outer preparation/controller and every
actual real/anchor inner query/type/leaf/prefix/cleanup call. It is NOT yet
the full canonical target: original budget/header serialization, case
dispatch, final cleanup/standalone finite-control integration, independent
verifier, closed encoded hardness and all toolchain/kernel checks remain.
-/

end PolytomyReductionModel
