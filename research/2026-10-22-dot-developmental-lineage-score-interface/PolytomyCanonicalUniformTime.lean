/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Uniform polynomial time for the ACTUAL original canonical serializer,
in the preserved tagged-unary normalized-record length bound L. Scalar
bounds are recovered from the actual header, not external binary-value
promises. Whole external-input normalization/composition remains distinct.
-/
import PolytomyActualOriginalCanonicalSerializer

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine

theorem canonicalScalarBounds (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s))
    (hg : ∀ k : CanonicalGlobalPort, s.stk (.inr k) = [])
    (hp : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    R.N ≤ L ∧ R.rows.length ≤ L ∧ R.K ≤ L := by
  obtain ⟨n, hn, he, hrows, hN, hM, hK⟩ := canonicalGlobalHeader_executes L s hs
    (hg .universe) (hg .rowCount) (hg .budget)
  obtain ⟨hf, hsuffix, hvN, hvM, hvK⟩ := canonicalGlobalHeader_values L s hs
    (hg .universe) (hg .rowCount) (hg .budget) R hp
  rw [hvN, List.length_replicate] at hN
  rw [hvM, List.length_replicate, ← hR.1] at hM
  rw [hvK, List.length_replicate] at hK
  exact ⟨hN, hM, hK⟩

theorem canonicalAlphabetCostBounds (R : RawMSSCRecord) (L : ℕ)
    (hN : R.N ≤ L) (hm : R.rows.length ≤ L) :
    rawRowAlphabet R ≤ rawRowAlphabetBound L ∧ rawRowFixedCost R ≤ rawRowCostBound L := by
  have hp := Nat.mul_le_mul hm hN
  have hA : rawRowAlphabet R ≤ rawRowAlphabetBound L := by
    unfold rawRowAlphabet rawRowAlphabetBound
    nlinarith
  have hsquare : rawRowAlphabet R ^ 2 ≤ rawRowAlphabetBound L ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hA hA
  have hprod := Nat.mul_le_mul (Nat.add_le_add_right hm 1) hsquare
  exact ⟨hA, (rawRowFixedCost_bound R).trans hprod⟩

theorem selectedQueryBound_mono (L C D I J : ℕ) (hC : C ≤ D) (hI : I ≤ J) :
    selectedQueryBound C L I ≤ selectedQueryBound D L J := by
  have hmul := Nat.mul_le_mul_right (L ^ 2) (Nat.mul_le_mul_left 7 hC)
  unfold selectedQueryBound
  omega

theorem realTypeBodyBound_mono (L S S' I I' T T' B B' : ℕ)
    (hS : S ≤ S') (hI : I ≤ I') (hT : T ≤ T') (hB : B ≤ B') :
    realTypeBodyBound L S I T B ≤ realTypeBodyBound L S' I' T' B' := by
  have h := selectedQueryBound_mono L S S' I I' hS hI
  unfold realTypeBodyBound
  omega

theorem operationalBlockBound_mono (L S S' I I' T T' B B' : ℕ)
    (hS : S ≤ S') (hI : I ≤ I') (hT : T ≤ T') (hB : B ≤ B') :
    operationalBlockBound L S I T B ≤ operationalBlockBound L S' I' T' B' := by
  have h := realTypeBodyBound_mono L S S' I I' T T' B B' hS hI hT hB
  have hm := Nat.mul_le_mul hS (Nat.add_le_add_right h 3)
  unfold operationalBlockBound
  omega

def canonicalBodyEnvelope (L : ℕ) := 10 * rawRowAlphabetBound L + 8 * L + 21 +
  operationalBlockBound L (rawRowAlphabetBound L) L (rawRowAlphabetBound L) (L + 1)

def canonicalBlocksEnvelope (L : ℕ) := canonicalGlobalsBound L +
  L * (canonicalBodyEnvelope L + 3) + 3 + canonicalBodyEnvelope L

def canonicalHeadersEnvelope (L : ℕ) :=
  (3 * rawRowCostBound L + 3 * L + 4 * L + 11) + (7 * L + 13) +
    (2 * (rawRowCostBound L + L) ^ 2 + 18 * (rawRowCostBound L + L) + 18) +
    (2 * L ^ 2 + 21 * L + 21) + (2 * L ^ 2 + 21 * L + 21)

def canonicalSerializerEnvelope (L : ℕ) := canonicalBlocksEnvelope L + canonicalHeadersEnvelope L

theorem canonicalBlocks_bound_envelope (R : RawMSSCRecord) (L : ℕ)
    (hm : R.rows.length ≤ L) (hA : rawRowAlphabet R ≤ rawRowAlphabetBound L) :
    canonicalAllBlocksBound R L ≤ canonicalBlocksEnvelope L := by
  have hT := (originalMarker_le_alphabet R).trans hA
  have hN := (originalUniverse_le_alphabet R).trans hA
  have hrealOp := operationalBlockBound_mono L (rawRowAlphabet R) (rawRowAlphabetBound L)
    R.rows.length L (originalMarkerThreshold R) (rawRowAlphabetBound L) (R.rows.length + 1) (L + 1)
    hA hm hT (Nat.add_le_add_right hm 1)
  have hanchorOp := operationalBlockBound_mono L (rawRowAlphabet R) (rawRowAlphabetBound L)
    R.rows.length L R.N (rawRowAlphabetBound L) (R.rows.length + 1) (L + 1)
    hA hm hN (Nat.add_le_add_right hm 1)
  have hreal : globalRealBlockBodyBound R L ≤ canonicalBodyEnvelope L := by
    unfold globalRealBlockBodyBound canonicalBodyEnvelope
    omega
  have hanchor : globalAnchorBlockBodyBound R L ≤ canonicalBodyEnvelope L := by
    unfold globalAnchorBlockBodyBound canonicalBodyEnvelope
    omega
  have hmul := Nat.mul_le_mul hm (Nat.add_le_add_right hreal 3)
  unfold canonicalAllBlocksBound globalRealBlocksBound canonicalBlocksEnvelope
  omega

theorem canonicalHeaders_bound_envelope (R : RawMSSCRecord) (L : ℕ)
    (hN : R.N ≤ L) (hm : R.rows.length ≤ L) (hK : R.K ≤ L)
    (hC : rawRowFixedCost R ≤ rawRowCostBound L) :
    canonicalHeadersBound R ≤ canonicalHeadersEnvelope L := by
  have hB : originalTargetBudget R ≤ rawRowCostBound L + L :=
    (Nat.sub_le _ _).trans (Nat.add_le_add hC hK)
  have hB2 : originalTargetBudget R ^ 2 ≤ (rawRowCostBound L + L) ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hB hB
  have hN2 : R.N ^ 2 ≤ L ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hN hN
  have hm2 : R.rows.length ^ 2 ≤ L ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hm hm
  unfold canonicalHeadersBound canonicalHeadersEnvelope
  omega

def canonicalAlphabetPolynomial : Polynomial ℕ := (Polynomial.X + 1) ^ 2 + 3
def canonicalCostPolynomial : Polynomial ℕ := (Polynomial.X + 1) * canonicalAlphabetPolynomial ^ 2
def canonicalTypePolynomial : Polynomial ℕ :=
  7 * canonicalAlphabetPolynomial * Polynomial.X ^ 2 + 10 * Polynomial.X ^ 3 + 27 * Polynomial.X ^ 2 +
    30 * Polynomial.X + 14 * canonicalAlphabetPolynomial + 4 * Polynomial.X +
    4 * canonicalAlphabetPolynomial + 3 * (Polynomial.X + 1) + 75
def canonicalBodyPolynomial : Polynomial ℕ :=
  10 * canonicalAlphabetPolynomial + 8 * Polynomial.X + 21 +
    canonicalAlphabetPolynomial * (canonicalTypePolynomial + 3) + 2 * canonicalAlphabetPolynomial + 6
def canonicalBlocksPolynomial : Polynomial ℕ :=
  10 * Polynomial.X ^ 2 + 42 * Polynomial.X + 58 +
    Polynomial.X * (canonicalBodyPolynomial + 3) + 3 + canonicalBodyPolynomial
def canonicalHeadersPolynomial : Polynomial ℕ :=
  (3 * canonicalCostPolynomial + 3 * Polynomial.X + 4 * Polynomial.X + 11) +
    (7 * Polynomial.X + 13) +
    (2 * (canonicalCostPolynomial + Polynomial.X) ^ 2 + 18 * (canonicalCostPolynomial + Polynomial.X) + 18) +
    (2 * Polynomial.X ^ 2 + 21 * Polynomial.X + 21) + (2 * Polynomial.X ^ 2 + 21 * Polynomial.X + 21)
def canonicalSerializerPolynomial : Polynomial ℕ := canonicalBlocksPolynomial + canonicalHeadersPolynomial

theorem canonicalSerializerEnvelope_eval (L : ℕ) :
    canonicalSerializerEnvelope L = canonicalSerializerPolynomial.eval L := by
  simp [canonicalSerializerEnvelope, canonicalBlocksEnvelope, canonicalHeadersEnvelope, canonicalBodyEnvelope,
    canonicalGlobalsBound, operationalBlockBound, realTypeBodyBound, selectedQueryBound,
    rawRowAlphabetBound, rawRowCostBound, canonicalSerializerPolynomial, canonicalBlocksPolynomial,
    canonicalHeadersPolynomial, canonicalBodyPolynomial, canonicalTypePolynomial, canonicalAlphabetPolynomial,
    canonicalCostPolynomial]
  <;> ring

theorem originalCanonicalSerializer_uniform (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s))
    (hq : s.stk (globalScanPort (.inr .queries)) = [])
    (hglobals : ∀ k : CanonicalGlobalPort, s.stk (.inr k) = [])
    (hfilters : ∀ k : CanonicalFilterPort, s.stk (globalFilterPort k) = [])
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    ∃ n ≤ canonicalSerializerPolynomial.eval L,
      originalCanonicalSerializerRoutine.Executes s (originalCanonicalSerializerEval R s) n ∧
      (originalCanonicalSerializerEval R s).stk (globalFilterPort .output) = rawRowCanonicalBits R ∧
      GlobalCanonicalInv R L (originalCanonicalSerializerEval R s) ∧
      (originalCanonicalSerializerEval R s).stk (.inr .blockCounter) = [] ∧
      (originalCanonicalSerializerEval R s).stk (globalFilterPort .cost) = List.replicate (rawRowFixedCost R) true ∧
      (originalCanonicalSerializerEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) := by
  obtain ⟨hN, hm, hK⟩ := canonicalScalarBounds R hR L s hs hglobals hparse
  obtain ⟨hA, hC⟩ := canonicalAlphabetCostBounds R L hN hm
  have hblocks := canonicalBlocks_bound_envelope R L hm hA
  have hheaders := canonicalHeaders_bound_envelope R L hN hm hK hC
  have htime : originalCanonicalSerializerBound R L ≤ canonicalSerializerPolynomial.eval L := by
    rw [← canonicalSerializerEnvelope_eval]
    unfold originalCanonicalSerializerBound canonicalSerializerEnvelope
    omega
  obtain ⟨n, hn, he, hout, hi, hcounter, hcost, horig⟩ :=
    originalCanonicalSerializer_executes R hR L s hs hq hglobals hfilters hparse
  exact ⟨n, hn.trans htime, he, hout, hi, hcounter, hcost, horig⟩

/- The explicit polynomial has degree at most ten by its displayed
expression. Its input variable is NORMALIZED-record length, not a free
numeric bound on unchecked binary headers. The actual outer binary-input
normalizer, original cases, validator/control integration, final cleanup,
standalone machine, independent verifier/encoded hardness/kernel checks
remain separate whole-claim obligations. No polynomial-time oracle or
certificate of successful elaboration is asserted.
-/

end PolytomyReductionModel
