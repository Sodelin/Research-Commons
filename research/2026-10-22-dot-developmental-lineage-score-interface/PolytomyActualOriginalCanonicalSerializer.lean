/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Complete ACTUAL original canonical target serializer on the original
valid normalized-record branch. Physical initialization, all original
blocks/C0 and exact original budget/headers are now joined. Not yet
the total case dispatcher, standalone machine or independent verifier.
-/
import PolytomyCompleteOriginalHeaders

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def originalCanonicalSerializerRoutine :
    Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq canonicalAllBlocksRoutine canonicalHeadersRoutine

def originalCanonicalSerializerEval (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  canonicalHeadersEval R (canonicalAllBlocksEval R s)

def originalCanonicalSerializerBound (R : RawMSSCRecord) (L : ℕ) :=
  canonicalAllBlocksBound R L + canonicalHeadersBound R

theorem originalHeaderPrefix_blocks (R : RawMSSCRecord) :
    originalHeaderPrefix R ++ (blockIndexList R.rows.length).flatMap (rawRowBlockBits R) = rawRowCanonicalBits R := by
  simp [originalHeaderPrefix, originalTargetBudget, rawRowCanonicalBits, blockIndexList, List.append_assoc]

theorem originalCanonicalSerializer_executes (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s))
    (hq : s.stk (globalScanPort (.inr .queries)) = [])
    (hglobals : ∀ k : CanonicalGlobalPort, s.stk (.inr k) = [])
    (hfilters : ∀ k : CanonicalFilterPort, s.stk (globalFilterPort k) = [])
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    ∃ n ≤ originalCanonicalSerializerBound R L,
      originalCanonicalSerializerRoutine.Executes s (originalCanonicalSerializerEval R s) n ∧
      (originalCanonicalSerializerEval R s).stk (globalFilterPort .output) = rawRowCanonicalBits R ∧
      GlobalCanonicalInv R L (originalCanonicalSerializerEval R s) ∧
      (originalCanonicalSerializerEval R s).stk (.inr .blockCounter) = [] ∧
      (originalCanonicalSerializerEval R s).stk (globalFilterPort .cost) = List.replicate (rawRowFixedCost R) true ∧
      (originalCanonicalSerializerEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) := by
  obtain ⟨a, ha, hea, hi, hcounter, hbytes, hcost, horig⟩ :=
    canonicalAllBlocks_executes R hR L s hs hq hglobals hfilters hparse
  obtain ⟨b, hb, heb, hfull⟩ := canonicalHeaders_executes R L (canonicalAllBlocksEval R s) hi hcost
  have hall := RoutineComposition.seq_executes _ _ hea heb
  refine ⟨a + b, by unfold originalCanonicalSerializerBound; omega, hall, ?_,
    canonicalHeaders_inv R L _ hi, ?_, ?_, ?_⟩
  · rw [hfull, hbytes, originalHeaderPrefix_blocks]
  · rw [canonicalHeaders_extra _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hcounter
  · rw [canonicalHeaders_extra _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hcost
  · rw [canonicalHeaders_extra _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact horig

/- The exact endpoint is ORIGINAL rawRowCanonicalBits, with original
binary N/m/(C0+K-N) headers, unary m+1 count and all original blocks.
It does not yet choose the ORIGINAL fixed yes/no branches, reject invalid
records, operationally reconcile validator/constructor control, clear all
reserved global/original/cost work or package a standalone all-input TM.
Independent verifier, compatible encoded hardness and all kernel checks
remain open. No biological or arbitrary-DAG closure follows.
-/

end PolytomyReductionModel
