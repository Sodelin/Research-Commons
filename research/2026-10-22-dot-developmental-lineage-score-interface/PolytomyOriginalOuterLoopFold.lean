/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact original ascending real-block byte order and fixed-cost sum from
the ACTUAL descending physical outer countdown, with actual preparation
and complete block calls. The actual pop proves every interpreted i<m.
-/
import PolytomyOriginalBlockOrder

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem globalRealBlocks_fold (R : RawMSSCRecord) (hR : RawMSSCValid R) (L n : ℕ) :
    ∀ (s : CanonicalGlobalStore) (acc : ℕ), GlobalCanonicalInv R L s →
      (s.stk (.inr .blockCounter)).length = n → s.stk (globalFilterPort .cost) = List.replicate acc true →
      (countdownLoopEval (.inr .blockCounter) (globalRealBlockBodyEval R) n
        (countdownPeek (.inr .blockCounter) s)).stk (globalFilterPort .output) =
        originalRealBlocksBits R n ++ s.stk (globalFilterPort .output) ∧
      (countdownLoopEval (.inr .blockCounter) (globalRealBlockBodyEval R) n
        (countdownPeek (.inr .blockCounter) s)).stk (globalFilterPort .cost) =
        List.replicate (acc + originalRealBlocksCost R n) true := by
  induction n with
  | zero =>
      intro s acc hs hlen hcost
      simp [countdownLoopEval, originalRealBlocksBits, originalRealBlocksCost, countdownPeek,
        countdownPeekOp, Op.apply, hcost]
  | succ n ih =>
      intro s acc hs hlen hcost
      have hhead : (s.stk (.inr .blockCounter)).head?.isSome = true := by
        cases hw : s.stk (.inr .blockCounter) with
        | nil => simp [hw] at hlen
        | cons x xs => rfl
      have hg : countdownGuard (countdownPeek (.inr .blockCounter) s).state = true := by
        simp [countdownGuard, countdownPeek, countdownPeekOp, Op.apply, hhead, hs.success]
      let p := countdownPop (.inr CanonicalGlobalPort.blockCounter) (countdownPeek (.inr .blockCounter) s)
      have hp : GlobalCanonicalInv R L p := globalCanonical_pop R L _
        (GlobalCanonicalInv_of_stacks R L s _ hs (fun _ => rfl) rfl)
      have hplen : (p.stk (.inr .blockCounter)).length = n := by
        change ((countdownPop (.inr .blockCounter) (countdownPeek (.inr .blockCounter) s)).stk (.inr .blockCounter)).length = n
        rw [countdownPop_counter]
        change (s.stk (.inr .blockCounter)).tail.length = n
        rw [List.length_tail, hlen]; omega
      have hlt : n < R.rows.length := by
        have hb := hs.counter_bound
        rw [hlen] at hb; omega
      have hpout : p.stk (globalFilterPort .output) = s.stk (globalFilterPort .output) := by
        simp [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply, globalFilterPort]
      have hpcost : p.stk (globalFilterPort .cost) = List.replicate acc true := by
        simpa [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply, globalFilterPort] using hcost
      let t := globalRealBlockBodyEval R p
      obtain ⟨k, hk, he, ht, ho⟩ := globalRealBlockBody_executes R L p hp
      have htlen : (t.stk (.inr .blockCounter)).length = n := by
        rw [globalRealBlockBody_globals]; exact hplen
      obtain ⟨hbytes, hcharge⟩ := globalRealBlockBody_original R hR L acc ⟨n, hlt⟩ p hp hplen hpcost
      have hbytes' : t.stk (globalFilterPort .output) = originalRealBlockBitsAt R n ++ s.stk (globalFilterPort .output) := by
        simpa [originalRealBlockBitsAt, hlt, hpout] using hbytes
      have hcharge' : t.stk (globalFilterPort .cost) = List.replicate (acc + originalRealBlockCostAt R n) true := by
        simpa [originalRealBlockCostAt, hlt] using hcharge
      obtain ⟨hiout, hicost⟩ := ih t (acc + originalRealBlockCostAt R n) ht htlen hcharge'
      rw [countdownLoopEval, hg]
      simp only [↓reduceIte]
      change (countdownLoopEval (.inr .blockCounter) (globalRealBlockBodyEval R) n
        (countdownPeek (.inr .blockCounter) t)).stk (globalFilterPort .output) = _ ∧
        (countdownLoopEval (.inr .blockCounter) (globalRealBlockBodyEval R) n
        (countdownPeek (.inr .blockCounter) t)).stk (globalFilterPort .cost) = _
      refine ⟨?_, ?_⟩
      · rw [hiout, hbytes', originalRealBlocksBits_succ, List.append_assoc]
      · rw [hicost, originalRealBlocksCost_succ]
        congr 1
        omega

theorem globalRealBlocks_original (R : RawMSSCRecord) (hR : RawMSSCValid R) (L acc : ℕ)
    (s : CanonicalGlobalStore) (hs : GlobalCanonicalInv R L s)
    (hcounter : s.stk (.inr .blockCounter) = List.replicate R.rows.length true)
    (hcost : s.stk (globalFilterPort .cost) = List.replicate acc true) :
    (globalRealBlocksEval R s).stk (globalFilterPort .output) =
      originalRealBlocksBits R R.rows.length ++ s.stk (globalFilterPort .output) ∧
      (globalRealBlocksEval R s).stk (globalFilterPort .cost) =
        List.replicate (acc + originalRealBlocksCost R R.rows.length) true := by
  have h := globalRealBlocks_fold R hR L R.rows.length s acc hs (by simp [hcounter]) hcost
  simpa [globalRealBlocksEval, countdownEval, hcounter] using h

def canonicalRealBlocksRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq canonicalGlobalsRoutine globalRealBlocksRoutine

def canonicalRealBlocksEval (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  globalRealBlocksEval R (canonicalGlobalsEval R s)

theorem canonicalRealBlocks_executes (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s))
    (hq : s.stk (globalScanPort (.inr .queries)) = [])
    (hglobals : ∀ k : CanonicalGlobalPort, s.stk (.inr k) = [])
    (hfilters : ∀ k : CanonicalFilterPort, s.stk (globalFilterPort k) = [])
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    ∃ n ≤ canonicalGlobalsBound L + globalRealBlocksBound R L,
      canonicalRealBlocksRoutine.Executes s (canonicalRealBlocksEval R s) n ∧
      GlobalCanonicalInv R L (canonicalRealBlocksEval R s) ∧
      (canonicalRealBlocksEval R s).stk (.inr .blockCounter) = [] ∧
      (canonicalRealBlocksEval R s).stk (globalFilterPort .output) = originalRealBlocksBits R R.rows.length ∧
      (canonicalRealBlocksEval R s).stk (globalFilterPort .cost) = List.replicate (originalRealBlocksCost R R.rows.length) true ∧
      (canonicalRealBlocksEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) := by
  obtain ⟨a, ha, hea, hi, hcounter, hcost, hout⟩ := canonicalGlobals_starts_outer R hR L s hs hq hglobals hfilters hparse
  obtain ⟨b, hb, heb, hi', hcounter', horig⟩ := globalRealBlocks_executes R L (canonicalGlobalsEval R s) hi
  obtain ⟨hbytes, hcharge⟩ := globalRealBlocks_original R hR L 0 (canonicalGlobalsEval R s) hi hcounter hcost
  have hall := RoutineComposition.seq_executes _ _ hea heb
  refine ⟨a + b, by omega, hall, hi', hcounter', ?_, ?_, ?_⟩
  · simpa [hout] using hbytes
  · simpa using hcharge
  · rw [horig]
    exact canonicalGlobals_old_extra R s (.inr .original) (by decide) (by decide) (by decide) (by decide)

/- Initialization plus ALL real blocks is now tied to exact original
ascending bytes and original fixed-cost sum by actual loop observations.
The anchor must still execute last so that prepend order makes it FIRST
in the original blockIndexList. Budget/headers/cases/standalone machinery,
independent verifier, encoded hardness and kernel checks remain open.
-/

end PolytomyReductionModel
