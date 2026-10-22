/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual clearing of EVERY public constructor work tape except the final
output, followed by an actual fixed finite-state reset. Private routine
work is already empty by each concrete Executes boundary. Original-record
work is deliberately cleared only after its exact output is constructed.
-/
import PolytomyCanonicalUniformTime

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def canonicalCleanupOwned : List CanonicalGlobalStack :=
  [globalScanPort (.inl .source), globalScanPort (.inl .payload), globalScanPort (.inl .cap),
   globalScanPort (.inl .work), globalScanPort (.inl .output),
   globalScanPort (.inr .original), globalScanPort (.inr .copyTemp), globalScanPort (.inr .headerN),
   globalScanPort (.inr .headerM), globalScanPort (.inr .headerK), globalScanPort (.inr .observed),
   globalScanPort (.inr .swapTemp), globalScanPort (.inr .residual), globalScanPort (.inr .right),
   globalScanPort (.inr .inner), globalScanPort (.inr .outer), globalScanPort (.inr .savedCount),
   globalScanPort (.inr .queries),
   globalFilterPort .typeIndex, globalFilterPort .rowIndex, globalFilterPort .threshold,
   globalFilterPort .blockCode, globalFilterPort .remaining, globalFilterPort .count,
   globalFilterPort .cost, globalFilterPort .temp,
   .inr .universe, .inr .rowCount, .inr .budget, .inr .alphabet, .inr .markerThreshold, .inr .blockCounter]

theorem canonicalCleanupOwned_complete (k : CanonicalGlobalStack) :
    k ∈ canonicalCleanupOwned ↔ k ≠ globalFilterPort .output := by
  rcases k with k | g
  · rcases k with k | f
    · rcases k with n | u
      · cases n <;> decide
      · cases u <;> decide
    · cases f <;> decide
  · cases g <;> decide

theorem canonicalCleanupOwned_length : canonicalCleanupOwned.length = 32 := rfl

def canonicalCleanState : CountdownState SelectedRowFrame := ((⟨false, false, false⟩, false), false)

def canonicalResetOp : Op CanonicalGlobalStack Bool (CountdownState SelectedRowFrame) :=
  .load (fun _ => canonicalCleanState)

def canonicalCleanStore (bits : List Bool) : CanonicalGlobalStore :=
  ⟨canonicalCleanState, Function.update (fun _ => []) (globalFilterPort .output) bits⟩

def canonicalCleanupEval (s : CanonicalGlobalStore) := canonicalResetOp.apply (clearManyEval canonicalCleanupOwned s)

def canonicalCleanupRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (clearManyRoutine canonicalCleanupOwned) (Atom.routine canonicalResetOp)

theorem canonicalCleanup_result (s : CanonicalGlobalStore) :
    canonicalCleanupEval s = canonicalCleanStore (s.stk (globalFilterPort .output)) := by
  apply countdownStore_ext
  · rfl
  · funext k
    by_cases hk : k = globalFilterPort .output
    · subst k
      have h := clearMany_outside canonicalCleanupOwned (globalFilterPort .output)
        (by rw [canonicalCleanupOwned_complete]; simp) s
      simpa [canonicalCleanupEval, canonicalResetOp, Op.apply, canonicalCleanStore] using h
    · have h := clearMany_member canonicalCleanupOwned k ((canonicalCleanupOwned_complete k).mpr hk) s
      simpa [canonicalCleanupEval, canonicalResetOp, Op.apply, canonicalCleanStore, hk] using h

theorem canonicalCleanup_executes (s : CanonicalGlobalStore) :
    ∃ n ≤ cleanupMass canonicalCleanupOwned s + 34,
      canonicalCleanupRoutine.Executes s (canonicalCleanStore (s.stk (globalFilterPort .output))) n := by
  obtain ⟨a, ha, he⟩ := clearMany_executes canonicalCleanupOwned s
  rw [canonicalCleanupOwned_length] at ha
  have hr := Atom.executes canonicalResetOp (clearManyEval canonicalCleanupOwned s)
  have hall := RoutineComposition.seq_executes _ _ he hr
  change canonicalCleanupRoutine.Executes s (canonicalCleanupEval s) (a + 1) at hall
  rw [canonicalCleanup_result] at hall
  exact ⟨a + 1, by omega, hall⟩

theorem canonicalCleanup_mass (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s) (hc : s.stk (.inr .blockCounter) = [])
    (hcost : s.stk (globalFilterPort .cost) = List.replicate (rawRowFixedCost R) true) :
    cleanupMass canonicalCleanupOwned s ≤ L + R.N + R.K + 3 * R.rows.length +
      3 * rawRowAlphabet R + rawRowFixedCost R + 1 := by
  have hn : ∀ k : NumericPort, s.stk (globalScanPort (.inl k)) = [] := by
    intro k
    cases k with
    | source => exact hs.scan.source_empty
    | payload => exact hs.scan.numeric.1
    | cap => simpa using hs.scan.numeric.2.2.2.1
    | work => exact hs.scan.numeric.2.1
    | output => exact hs.scan.numeric.2.2.1
  have hu : ∀ k ∈ scanWorkExtras, s.stk (globalScanPort (.inr k)) = [] := hs.scan.empty
  have hrecord : (s.stk (globalScanPort (.inr .original))).length ≤ L := hs.scan.original_bound
  have hrow := hs.row_bound
  have hthreshold := hs.threshold_bound
  have hblock := hs.block_bound
  have hmarker := originalMarker_le_alphabet R
  simp [cleanupMass, canonicalCleanupOwned, hn, hu, scanWorkExtras, hs.query_empty,
    hs.type_empty, hs.remaining_empty, hs.count_empty, hs.temp_empty, hc, hcost,
    hs.universe, hs.rows, hs.budget, hs.alphabet, hs.marker]
  <;> omega

def canonicalCleanupPolynomial : Polynomial ℕ :=
  6 * Polynomial.X + 3 * canonicalAlphabetPolynomial + canonicalCostPolynomial + 35

theorem canonicalCleanup_uniform (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s) (hc : s.stk (.inr .blockCounter) = [])
    (hcost : s.stk (globalFilterPort .cost) = List.replicate (rawRowFixedCost R) true)
    (hN : R.N ≤ L) (hm : R.rows.length ≤ L) (hK : R.K ≤ L) :
    ∃ n ≤ canonicalCleanupPolynomial.eval L,
      canonicalCleanupRoutine.Executes s (canonicalCleanStore (s.stk (globalFilterPort .output))) n := by
  obtain ⟨hA, hC⟩ := canonicalAlphabetCostBounds R L hN hm
  have hmass := canonicalCleanup_mass R L s hs hc hcost
  obtain ⟨n, hn, he⟩ := canonicalCleanup_executes s
  refine ⟨n, ?_, he⟩
  have heval : canonicalCleanupPolynomial.eval L = 6 * L + 3 * rawRowAlphabetBound L + rawRowCostBound L + 35 := by
    simp [canonicalCleanupPolynomial, canonicalCostPolynomial, canonicalAlphabetPolynomial,
      rawRowCostBound, rawRowAlphabetBound]
  rw [heval]
  omega

/- The 32-port list is proved exhaustive except for the final output.
The generic cleanup contract covers arbitrary incoming work contents;
the uniform valid-canonical bound uses actual post-state observations.
Reset success=false is an actual fixed instruction, not a claim that
the previous true success flag was already the final machine state.
-/

end PolytomyReductionModel
