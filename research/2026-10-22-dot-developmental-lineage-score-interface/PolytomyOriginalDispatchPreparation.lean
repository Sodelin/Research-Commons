/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual preparation for the ORIGINAL special-case dispatch. Reuse the
concrete header reader and multiplier, not a new encoding or arithmetic
oracle. All N,m,K,Nm operands have physical tape locations.
-/
import PolytomyOriginalDispatchCleanup

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

def originalDispatchPrepareRoutine :=
  RoutineComposition.seq canonicalGlobalHeaderRoutine canonicalGlobalProductRoutine

def originalDispatchPrepareEval (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  canonicalGlobalProductEval R.N R.rows.length (canonicalGlobalHeaderEval s)

def originalDispatchPrepareBound (L : ℕ) := 3 * L ^ 2 + 30 * L + 34

theorem originalDispatchPrepare_old (R : RawMSSCRecord) (s : CanonicalGlobalStore)
    (k : NumericStack UnaryScanPort) (hsrc : k ≠ .inl .source) (hcap : k ≠ .inl .cap)
    (hm : k ≠ .inr .headerM) (hp : k ≠ .inr .savedCount) :
    (originalDispatchPrepareEval R s).stk (globalScanPort k) = s.stk (globalScanPort k) := by
  rw [canonicalGlobalProduct_extra _ _ _ _ (by simpa [globalScanPort] using hcap)
    (by simpa [globalScanPort] using hm) (by simpa [globalScanPort] using hp)]
  exact canonicalGlobalHeader_extra s _ (by simpa [globalScanPort] using hsrc)
    (by simp [globalScanPort]) (by simp [globalScanPort]) (by simp [globalScanPort])

theorem originalDispatchPrepare_filter (R : RawMSSCRecord) (s : CanonicalGlobalStore) (k : CanonicalFilterPort) :
    (originalDispatchPrepareEval R s).stk (globalFilterPort k) = s.stk (globalFilterPort k) := by
  rw [canonicalGlobalProduct_extra _ _ _ _ (by simp [globalFilterPort, globalScanPort])
    (by simp [globalFilterPort, globalScanPort]) (by simp [globalFilterPort, globalScanPort])]
  exact canonicalGlobalHeader_extra s _ (by simp [globalFilterPort, globalScanPort])
    (by simp [globalFilterPort]) (by simp [globalFilterPort]) (by simp [globalFilterPort])

theorem originalDispatchPrepare_executes (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : OriginalConstructorEntry L s)
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    ∃ n ≤ originalDispatchPrepareBound L,
      originalDispatchPrepareRoutine.Executes s (originalDispatchPrepareEval R s) n ∧
      (originalDispatchPrepareEval R s).stk (.inr .universe) = List.replicate R.N true ∧
      (originalDispatchPrepareEval R s).stk (.inr .rowCount) = List.replicate R.rows.length true ∧
      (originalDispatchPrepareEval R s).stk (.inr .budget) = List.replicate R.K true ∧
      (originalDispatchPrepareEval R s).stk (globalScanPort (.inr .savedCount)) = List.replicate (R.N * R.rows.length) true ∧
      cleanupMass canonicalCleanupOwned (originalDispatchPrepareEval R s) ≤ L ^ 2 + 7 * L := by
  let u := canonicalGlobalHeaderEval s
  let v := originalDispatchPrepareEval R s
  obtain ⟨a, ha, hea, hsrc, hNb, hMb, hKb⟩ := canonicalGlobalHeader_executes L s hs.scan
    (hs.globals_empty .universe) (hs.globals_empty .rowCount) (hs.globals_empty .budget)
  obtain ⟨hf, hrows, hN, hM, hK⟩ := canonicalGlobalHeader_values L s hs.scan
    (hs.globals_empty .universe) (hs.globals_empty .rowCount) (hs.globals_empty .budget) R hparse
  have hM' : u.stk (.inr .rowCount) = List.replicate R.rows.length true := by simpa only [← hR.1] using hM
  have hNd : R.N ≤ L := by simpa [hN] using hNb
  have hMd : R.rows.length ≤ L := by simpa [hM'] using hMb
  have hKd : R.K ≤ L := by simpa [hK] using hKb
  have hprod : R.N * R.rows.length ≤ L ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hNd hMd
  have huold : ∀ k : NumericStack UnaryScanPort, k ≠ .inl .source →
      u.stk (globalScanPort k) = s.stk (globalScanPort k) := by
    intro k hk
    exact canonicalGlobalHeader_extra s _ (by simpa [globalScanPort] using hk)
      (by simp [globalScanPort]) (by simp [globalScanPort]) (by simp [globalScanPort])
  have hun : NumericLoopInv 0 L (canonicalGlobalNumeric u) := by
    refine ⟨?_, ?_, ?_, ?_, hsrc⟩
    · rw [huold _ (by decide)]; exact hs.scan.numeric.1
    · rw [huold _ (by decide)]; exact hs.scan.numeric.2.1
    · rw [huold _ (by decide)]; exact hs.scan.numeric.2.2.1
    · rw [huold _ (by decide)]; exact hs.scan.numeric.2.2.2.1
  have hempty : ∀ k ∈ scanWorkExtras, u.stk (globalScanPort (.inr k)) = [] := by
    intro k hk; rw [huold _ (by simp)]; exact hs.scan.empty k hk
  obtain ⟨b, hb, heb⟩ := canonicalGlobalProduct_executes R.N R.rows.length L u hun hf hN hM'
    (hempty .copyTemp (by simp [scanWorkExtras])) (hempty .headerM (by simp [scanWorkExtras]))
    (hempty .swapTemp (by simp [scanWorkExtras])) (hempty .savedCount (by simp [scanWorkExtras]))
    (hempty .outer (by simp [scanWorkExtras]))
  have hvN : v.stk (.inr .universe) = List.replicate R.N true := by
    simpa [v, originalDispatchPrepareEval, canonicalGlobalProductEval, globalScanPort] using hN
  have hvM : v.stk (.inr .rowCount) = List.replicate R.rows.length true := by
    simpa [v, originalDispatchPrepareEval, canonicalGlobalProductEval, globalScanPort] using hM'
  have hvK : v.stk (.inr .budget) = List.replicate R.K true := by
    simpa [v, originalDispatchPrepareEval, canonicalGlobalProductEval, globalScanPort] using hK
  have hvP : v.stk (globalScanPort (.inr .savedCount)) = List.replicate (R.N * R.rows.length) true := by
    simp [v, originalDispatchPrepareEval, canonicalGlobalProductEval]
  have hvcap : v.stk (globalScanPort (.inl .cap)) = List.replicate R.N true := by
    simp [v, originalDispatchPrepareEval, canonicalGlobalProductEval, globalScanPort]
  have hvheader : v.stk (globalScanPort (.inr .headerM)) = List.replicate R.rows.length true := by
    simp [v, originalDispatchPrepareEval, canonicalGlobalProductEval, globalScanPort]
  have hvsrc : v.stk (globalScanPort (.inl .source)) = u.stk (globalScanPort (.inl .source)) := by
    simp [v, u, originalDispatchPrepareEval, canonicalGlobalProductEval, globalScanPort]
  have hvo : v.stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) :=
    originalDispatchPrepare_old R s _ (by decide) (by decide) (by decide) (by decide)
  have hn : ∀ k : NumericPort, k ≠ .source → k ≠ .cap → v.stk (globalScanPort (.inl k)) = [] := by
    intro k hsource hcap
    rw [originalDispatchPrepare_old R s _ (by simpa using hsource) (by simpa using hcap) (by simp) (by simp)]
    exact OriginalConstructorEntry.numeric_empty L s hs k
  have hu : ∀ k : UnaryScanPort, k ≠ .original → k ≠ .headerM → k ≠ .savedCount →
      v.stk (globalScanPort (.inr k)) = [] := by
    intro k ho hm hp
    rw [originalDispatchPrepare_old R s _ (by simp) (by simp) (by simpa using hm) (by simpa using hp)]
    exact OriginalConstructorEntry.empty L s hs _ (by simpa [globalScanPort] using ho)
  have hg : ∀ k : CanonicalGlobalPort, k ≠ .universe → k ≠ .rowCount → k ≠ .budget → v.stk (.inr k) = [] := by
    intro k hnu hmu hku
    rw [canonicalGlobalProduct_extra _ _ _ _ (by simp [globalScanPort]) (by simp [globalScanPort]) (by simp [globalScanPort])]
    rw [canonicalGlobalHeader_extra _ _ (by simp [globalScanPort])
      (by simpa using hnu) (by simpa using hmu) (by simpa using hku)]
    exact hs.globals_empty k
  have hfilter : ∀ k : CanonicalFilterPort, v.stk (globalFilterPort k) = [] := by
    intro k; exact (originalDispatchPrepare_filter R s k).trans (hs.filters_empty k)
  refine ⟨a + b, ?_, RoutineComposition.seq_executes _ _ hea heb, hvN, hvM, hvK, hvP, ?_⟩
  · unfold originalDispatchPrepareBound; nlinarith
  · have hL := hs.scan.original_bound
    simp [cleanupMass, canonicalCleanupOwned, hn, hu, hg, hfilter, hvN, hvM, hvK, hvP,
      hvcap, hvheader, hvsrc, hvo]
    <;> nlinarith

/- Only a validated source reaches this routine. The physical product
is N*m; the original branch tests m*N, identified by commutativity in
the branch correctness proof. The full mass bound includes BOTH original
and copied row suffix, every duplicate operand and the product itself.
-/

end PolytomyReductionModel
