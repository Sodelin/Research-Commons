/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Complete actual original scalar classifier, including operand creation,
all four physical tests and unconditional work cleanup before branching.
The original record and four finite decisions survive; all work is fresh.
-/
import PolytomyPhysicalDispatchFlags

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

def originalDispatchClassifierRoutine :=
  RoutineComposition.seq originalDispatchPrepareRoutine
    (RoutineComposition.seq originalDispatchFlagsRoutine originalDispatchCleanRoutine)

def originalDispatchClassified (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  originalDispatchCleanEval (originalDispatchFlags R (originalDispatchPrepareEval R s))

def originalDispatchClassifierBound (L : ℕ) := 8 * L ^ 2 + 53 * L + 92

theorem originalDispatchClassified_state (R : RawMSSCRecord) (s : CanonicalGlobalStore) :
    (originalDispatchClassified R s).state =
      ((⟨decide (R.N = 0), decide (R.rows.length ≤ 1), decide (R.N ≤ R.K)⟩,
        (originalDispatchPrepareEval R s).state.1.2), decide (R.N * R.rows.length ≤ R.K)) :=
  originalDispatchClean_state _

theorem originalDispatchClassifier_executes (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : OriginalConstructorEntry L s)
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    ∃ n ≤ originalDispatchClassifierBound L,
      originalDispatchClassifierRoutine.Executes s (originalDispatchClassified R s) n ∧
      OriginalConstructorEntry L (originalDispatchClassified R s) ∧
      (originalDispatchClassified R s).stk (globalScanPort (.inr .original)) =
        s.stk (globalScanPort (.inr .original)) := by
  let p := originalDispatchPrepareEval R s
  let f := originalDispatchFlags R p
  obtain ⟨a, ha, hea, hN, hm, hK, hP, hmass⟩ := originalDispatchPrepare_executes R hR L s hs hparse
  have hfilters : ∀ k : CanonicalFilterPort, p.stk (globalFilterPort k) = [] := by
    intro k; exact (originalDispatchPrepare_filter R s k).trans (hs.filters_empty k)
  obtain ⟨b, hb, heb⟩ := originalDispatchFlags_executes R p hN hm hK hP hfilters
  obtain ⟨c, hc, hec⟩ := originalDispatchClean_executes f
  have hmassf : cleanupMass canonicalCleanupOwned f ≤ L ^ 2 + 7 * L := hmass
  have horig : f.stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) :=
    originalDispatchPrepare_old R s _ (by decide) (by decide) (by decide) (by decide)
  have hL : (f.stk (globalScanPort (.inr .original))).length ≤ L := by rw [horig]; exact hs.scan.original_bound
  have hout : f.stk (globalFilterPort .output) = [] := hfilters .output
  have he := originalDispatchClean_entry L f hL hout
  have hp := (originalDispatchClean_original f).trans horig
  obtain ⟨hNb, hmb, hKb⟩ := canonicalScalarBounds R hR L s hs.scan hs.globals_empty hparse
  have hprod : R.N * R.rows.length ≤ L ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hNb hmb
  have hb' : b ≤ 4 * L ^ 2 + 16 * L + 26 := by unfold originalDispatchFlagsBound at hb; nlinarith
  exact ⟨a + (b + c), by unfold originalDispatchClassifierBound originalDispatchPrepareBound at *; omega,
    RoutineComposition.seq_executes _ _ hea (RoutineComposition.seq_executes _ _ heb hec), he, hp⟩

/- Bound: (3L^2+30L+34) preparation + (4L^2+16L+26) tests
+ (L^2+7L+32) cleanup = 8L^2+53L+92. L bounds the original
normalized word. The final decision controller must still use the four
stored Boolean tests to realize rawRowMSSCBits exactly.
-/

end PolytomyReductionModel
