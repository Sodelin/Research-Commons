/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The complete SAME original normalized-record constructor on ALL words:
actual original validity first, original special cases second, unchanged
canonical output last. Every exit is the clean original output boundary.
-/
import PolytomyOriginalDecisionController

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

def originalNormalRecordRoutine := RoutineComposition.seq globalOriginalValidationRoutine
  (RoutineControl.branch dispatchSuccess originalValidRecordRoutine originalNoRoutine)

def originalNormalRecordPolynomial : Polynomial ℕ := originalValidRecordPolynomial +
  17 * Polynomial.X ^ 4 + 44 * Polynomial.X ^ 3 + 63 * Polynomial.X ^ 2 + 90 * Polynomial.X + 56

theorem originalNormalRecordPolynomial_eval (L : ℕ) :
    originalNormalRecordPolynomial.eval L =
      originalUnaryValidationBound L + originalValidRecordPolynomial.eval L + 1 := by
  simp [originalNormalRecordPolynomial, originalUnaryValidationBound]
  <;> ring

theorem normalRecordConstructor_invalid (bits : List Bool) (h : originalUnaryValidity bits = false) :
    normalRecordConstructor bits = originalFixedNoBits := by
  cases hp : readNormalizedSource bits with
  | none => simp [normalRecordConstructor, hp, originalFixedNoBits]
  | some R =>
      have hv : scanSourceValid R = false := by
        simpa [originalUnaryValidity, hp, unaryRangeValid_eq_original] using h
      simp [normalRecordConstructor, hp, rawRowRecordBits, hv, originalFixedNoBits]

theorem normalRecordConstructor_valid (bits : List Bool) (R : RawMSSCRecord)
    (hp : readNormalizedSource bits = some R) (hR : RawMSSCValid R) :
    normalRecordConstructor bits = rawRowMSSCBits R := by
  have hv := (scanSourceValid_spec R).mpr hR
  simp [normalRecordConstructor, hp, rawRowRecordBits, hv]

theorem originalValidRecordPolynomial_covers_no (L : ℕ) :
    originalFixedNoBits.length + L + 36 ≤ originalValidRecordPolynomial.eval L := by
  rw [originalValidRecordPolynomial_eval]
  unfold originalDispatchClassifierBound originalDispatchChooseBound originalLiteralSize
  omega

theorem originalNormalRecord_executes (L : ℕ) (s : CanonicalGlobalStore)
    (hs : OriginalConstructorEntry L s) :
    ∃ n ≤ originalNormalRecordPolynomial.eval L,
      originalNormalRecordRoutine.Executes s
        (canonicalCleanStore (normalRecordConstructor (s.stk (globalScanPort (.inr .original))))) n := by
  let v := globalOriginalValidationEval s
  obtain ⟨a, ha, hea, hr, hq, hp, hf⟩ := globalOriginalValidation_executes L s hs.scan hs.query_empty
  have hv : OriginalConstructorEntry L v := originalValidation_preserves_entry L s hs
  cases hflag : v.state.2 with
  | false =>
      obtain ⟨b, hb, heb⟩ := originalEntryLiteral_executes originalFixedNoBits L v hv
      have hchoose := RoutineControl.branch_false dispatchSuccess originalValidRecordRoutine originalNoRoutine hflag heb
      have hinvalid : originalUnaryValidity (s.stk (globalScanPort (.inr .original))) = false := hf.symm.trans hflag
      have hout := normalRecordConstructor_invalid _ hinvalid
      rw [← hout] at hchoose
      have hb' := hb.trans (originalValidRecordPolynomial_covers_no L)
      exact ⟨a + (b + 1), by rw [originalNormalRecordPolynomial_eval]; omega,
        RoutineComposition.seq_executes _ _ hea hchoose⟩
  | true =>
      obtain ⟨R, hparse, hR⟩ := globalOriginalValidation_success L s hs.scan hs.query_empty hflag
      have hpv : readNormalizedSource (v.stk (globalScanPort (.inr .original))) = some R := by rw [hp]; exact hparse
      obtain ⟨b, hb, heb⟩ := originalValidRecord_executes R hR L v hv hpv
      have hchoose := RoutineControl.branch_true dispatchSuccess originalValidRecordRoutine originalNoRoutine hflag heb
      have hout := normalRecordConstructor_valid _ R hparse hR
      rw [← hout] at hchoose
      exact ⟨a + (b + 1), by rw [originalNormalRecordPolynomial_eval]; omega,
        RoutineComposition.seq_executes _ _ hea hchoose⟩

theorem originalNormalRecord_all_words (bits : List Bool) :
    ∃ n ≤ originalNormalRecordPolynomial.eval bits.length,
      originalNormalRecordRoutine.Executes (originalConstructorInput bits)
        (canonicalCleanStore (normalRecordConstructor bits)) n := by
  simpa [originalConstructorInput] using originalNormalRecord_executes bits.length
    (originalConstructorInput bits) (originalConstructorInput_entry bits)

/- This all-word routine theorem has no external parse/validity or
bounded-scalar premise. The polynomial uses the ACTUAL normalized input
word length. Its proof chain includes invalid/tag/count/range/coverage
cases and every original boundary case. Standalone finite-machine
packaging, external normalization composition, independent target verifier,
encoded hardness, pinned compatibility and kernel checks remain distinct.
-/

end PolytomyReductionModel
