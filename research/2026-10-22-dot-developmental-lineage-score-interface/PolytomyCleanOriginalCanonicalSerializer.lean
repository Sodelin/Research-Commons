/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Complete actual original valid-canonical branch, now including ALL
public work cleanup and exact finite-state reset, with a fixed uniform
polynomial in normalized-record length. Total dispatch is still separate.
-/
import PolytomyCanonicalFinalCleanup

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

def cleanOriginalCanonicalRoutine :
    Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq originalCanonicalSerializerRoutine canonicalCleanupRoutine

def cleanOriginalCanonicalPolynomial : Polynomial ℕ := canonicalSerializerPolynomial + canonicalCleanupPolynomial

theorem cleanOriginalCanonical_executes (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s))
    (hq : s.stk (globalScanPort (.inr .queries)) = [])
    (hglobals : ∀ k : CanonicalGlobalPort, s.stk (.inr k) = [])
    (hfilters : ∀ k : CanonicalFilterPort, s.stk (globalFilterPort k) = [])
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    ∃ n ≤ cleanOriginalCanonicalPolynomial.eval L,
      cleanOriginalCanonicalRoutine.Executes s (canonicalCleanStore (rawRowCanonicalBits R)) n := by
  obtain ⟨hN, hm, hK⟩ := canonicalScalarBounds R hR L s hs hglobals hparse
  obtain ⟨a, ha, hea, hout, hi, hcounter, hcost, horig⟩ :=
    originalCanonicalSerializer_uniform R hR L s hs hq hglobals hfilters hparse
  obtain ⟨b, hb, heb⟩ := canonicalCleanup_uniform R L (originalCanonicalSerializerEval R s)
    hi hcounter hcost hN hm hK
  rw [hout] at heb
  exact ⟨a + b, by simpa [cleanOriginalCanonicalPolynomial] using Nat.add_le_add ha hb,
    RoutineComposition.seq_executes _ _ hea heb⟩

/- This exact endpoint has ONLY the ORIGINAL final target byte string
on its output port; every other public tape is empty and all public/
private finite control is at the actual specified reset boundary.
It remains conditional on original validity, parsed input and fresh
caller entry. The original total yes/no branches, invalid-record path,
operational validator control transport, standalone all-input packaging,
normalization composition, independent verifier and encoded-hardness/
kernel checks remain open. It is not a whole-reduction certificate.
-/

end PolytomyReductionModel
