/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

All-input INTERNAL unary-record bounds and an exactly equivalent original
validator using bounded range coverage instead of a deduplication oracle.
Actual repeated scans/range-loop machinery remains to be constructed.
-/
import PolytomyPreservingUnaryCompare

namespace PolytomyReductionModel

theorem readNormalizedSource_sound (bits : List Bool) (R : RawMSSCRecord)
    (h : readNormalizedSource bits = some R) : bits = true :: encodeUnaryRaw R := by
  cases bits with
  | nil => simp [readNormalizedSource] at h
  | cons b rest =>
      cases b with
      | false => simp [readNormalizedSource] at h
      | true =>
          have hr : parseUnaryRaw rest = some R := h
          rw [parseUnaryRaw_sound rest R hr]

theorem readNormalizedSource_mass (bits : List Bool) (R : RawMSSCRecord)
    (h : readNormalizedSource bits = some R) :
    sourceUnaryValueMass R + rawRecordSize R + 3 = bits.length := by
  rw [readNormalizedSource_sound bits R h, List.length_cons, encodeUnaryRaw_length]
  omega

theorem downstream_member_le_sum (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp
      · have h := ih hx
        simp only [List.sum_cons]
        omega

/-- Bounds precede semantic validity: malformed dimensions and repeated
    identifiers are included whenever the unary grammar parses. -/
theorem unary_downstream_dimensions (bits : List Bool) (R : RawMSSCRecord)
    (h : readNormalizedSource bits = some R) :
    R.N ≤ bits.length ∧ R.declaredM ≤ bits.length ∧ R.K ≤ bits.length ∧
      R.rows.length ≤ bits.length ∧ R.rows.flatten.length ≤ bits.length ∧
      (∀ x ∈ R.rows.flatten, x ≤ bits.length) := by
  have hm := readNormalizedSource_mass bits R h
  unfold sourceUnaryValueMass rawRecordSize at hm
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  intro x hx
  have hs := downstream_member_le_sum R.rows.flatten x hx
  omega

def unaryDownstreamAlphabetBound (M : ℕ) : ℕ := M ^ 2 + M + 3
def unaryDownstreamCostBound (M : ℕ) : ℕ := (M + 1) * unaryDownstreamAlphabetBound M ^ 2

theorem unary_downstream_arithmetic_bounds (bits : List Bool) (R : RawMSSCRecord)
    (h : readNormalizedSource bits = some R) :
    R.rows.length * R.N ≤ bits.length ^ 2 ∧
      rawRowAlphabet R ≤ unaryDownstreamAlphabetBound bits.length ∧
      rawRowFixedCost R ≤ unaryDownstreamCostBound bits.length ∧
      rawRowFixedCost R + R.K - R.N ≤ unaryDownstreamCostBound bits.length + bits.length := by
  obtain ⟨hN, hm, hK, hrows, hids, hvalues⟩ := unary_downstream_dimensions bits R h
  have hproduct : R.rows.length * R.N ≤ bits.length ^ 2 := by
    have hp := Nat.mul_le_mul hrows hN
    simpa only [pow_two] using hp
  have halpha : rawRowAlphabet R ≤ unaryDownstreamAlphabetBound bits.length := by
    unfold rawRowAlphabet unaryDownstreamAlphabetBound
    omega
  have hcost := rawRowFixedCost_bound R
  have hsquare : rawRowAlphabet R ^ 2 ≤ unaryDownstreamAlphabetBound bits.length ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul (Nat.add_le_add_right hrows 1) hsquare
  have hc : rawRowFixedCost R ≤ unaryDownstreamCostBound bits.length := hcost.trans hmul
  exact ⟨hproduct, halpha, hc, by omega⟩

/-- Safe to enumerate after INTERNAL unary parsing because N≤word length.
    This is a semantic rewrite, not yet an emitted machine routine. -/
def unaryRangeValid (R : RawMSSCRecord) : Bool :=
  decide (R.rows.length = R.declaredM) &&
    R.rows.flatten.all (fun x => decide (x < R.N)) &&
    (List.range R.N).all (fun x => decide (x ∈ R.rows.flatten))

theorem unaryRangeValid_spec (R : RawMSSCRecord) :
    unaryRangeValid R = true ↔ RawMSSCValid R := by
  simp only [unaryRangeValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]
  constructor
  · rintro ⟨hcount, hbound, hcover⟩
    have hsets : rawElements R = Finset.range R.N := by
      apply Finset.ext
      intro x
      constructor
      · intro hx
        exact Finset.mem_range.mpr (hbound x (by simpa [rawElements] using hx))
      · intro hx
        have hm := hcover x (List.mem_range.mpr (Finset.mem_range.mp hx))
        simpa [rawElements] using hm
    exact ⟨hcount, hbound, by rw [hsets]; simp⟩
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro x hx
    have hm : x ∈ rawElements R := by
      rw [rawElements_eq_range R h]
      exact Finset.mem_range.mpr (List.mem_range.mp hx)
    simpa [rawElements] using hm

theorem unaryRangeValid_eq_original (R : RawMSSCRecord) : unaryRangeValid R = scanSourceValid R := by
  have he : unaryRangeValid R = true ↔ scanSourceValid R = true :=
    (unaryRangeValid_spec R).trans (scanSourceValid_spec R).symm
  cases h1 : unaryRangeValid R <;> cases h2 : scanSourceValid R <;> simp_all

def rangeNormalRecordConstructor (bits : List Bool) : List Bool :=
  match readNormalizedSource bits with
  | none => scanEncodeTarget scanFixedNoTarget
  | some R => if unaryRangeValid R then rawRowMSSCBits R else scanEncodeTarget scanFixedNoTarget

theorem rangeNormalRecordConstructor_eq (bits : List Bool) :
    rangeNormalRecordConstructor bits = normalRecordConstructor bits := by
  unfold rangeNormalRecordConstructor normalRecordConstructor
  cases hp : readNormalizedSource bits with
  | none => rfl
  | some R => simp only [unaryRangeValid_eq_original, rawRowRecordBits]

theorem range_normalized_original (input : List Bool) :
    rangeNormalRecordConstructor (normalizedSource input) = scanEncodedConstructor input := by
  rw [rangeNormalRecordConstructor_eq, normalized_constructor_original]

/-- Exact transfer only; the remaining total downstream machine is NOT
    supplied by the range-scan semantic rewrite or arithmetic primitives. -/
def normalRecordMachineOfRange
    (h : Turing.TM2ComputableInPolyTime (fun bits : List Bool => bits)
      (fun bits : List Bool => bits) rangeNormalRecordConstructor) : NormalRecordMachineWitness := by
  have he : rangeNormalRecordConstructor = normalRecordConstructor := funext rangeNormalRecordConstructor_eq
  simpa only [he] using h

/- Complete range coverage plus no out-of-range ID is EXACTLY the original
distinct-count test, including duplicates, N=0 and invalid declared counts.
At most M range values and M explicitly encoded entries are traversed per
coverage pass after successful internal parsing. Actual finite scan/copy/
comparison/loop composition and its global bounds are still required;
this is not a polynomial-machine witness or a changed source language.
-/

end PolytomyReductionModel
