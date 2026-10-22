/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No execution or kernel certificate.

The SAME total constructor expressed directly in supplied raw rows.
No MSSCInstance, set image, source coverage proof or canonical sort is
evaluated by the new algorithm bodies. Finite block indices merely index
the actual row list. Exact byte equality retains every original branch,
actual D_lambda and every admissible joining refinement.
This is not yet a complete emitted TM2 constructor or verifier.
-/
import PolytomyBinaryCounterEncoder

namespace PolytomyReductionModel

def rawRowAlphabet (R : RawMSSCRecord) : ℕ := R.N + R.rows.length * R.N + 3

/-- The only source-dependent membership operation is a supplied-list scan.
    The caller filters the bounded range [0,S), so the marker upper bound
    need not be tested a second time inside this predicate. -/
def rawRowMember (R : RawMSSCRecord) : Block R.rows.length → ℕ → Bool
  | none, n => decide (R.N ≤ n)
  | some i, n => decide ((n < R.N ∧ n ∈ R.rows.get i) ∨
      R.N + privateCount R.N R.rows.length ≤ n)

def rawRowCodes (R : RawMSSCRecord) (b : Block R.rows.length) : List ℕ :=
  (List.range (rawRowAlphabet R)).filter (rawRowMember R b)

theorem terminalCode_surjective_bounded (N m n : ℕ) (hn : n < N + m * N + 3) :
    ∃ s : Terminal N m, terminalCode N m s = n := by
  by_cases hx : n < N
  · exact ⟨Sum.inl ⟨n, hx⟩, rfl⟩
  · by_cases hz : n - N < privateCount N m
    · refine ⟨Sum.inr (Sum.inl ⟨n - N, hz⟩), ?_⟩
      simp only [terminalCode]
      omega
    · have hk : n - N - privateCount N m < 2 := by
        unfold privateCount at *
        omega
      refine ⟨Sum.inr (Sum.inr ⟨n - N - privateCount N m, hk⟩), ?_⟩
      simp only [terminalCode]
      omega

theorem rawRowMember_code (R : RawMSSCRecord) (h : RawMSSCValid R)
    (b : Block R.rows.length) (s : Terminal R.N R.rows.length) :
    rawRowMember R b (terminalCode R.N R.rows.length s) =
      decide (s ∈ blockTypes (scanSourceModel R h) b) := by
  cases b with
  | none =>
      rcases s with x | (z | k)
      · have hx : ¬ R.N ≤ x.val := by have := x.isLt; omega
        simp [rawRowMember, terminalCode, blockTypes, markers, hx]
      · simp [rawRowMember, terminalCode, blockTypes, markers]
      · simp [rawRowMember, terminalCode, blockTypes, markers, Nat.add_assoc]
  | some i =>
      rcases s with x | (z | k)
      · have hx : ¬ R.N + privateCount R.N R.rows.length ≤ x.val := by
          have := x.isLt
          omega
        simp [rawRowMember, terminalCode, blockTypes, markers, scanSourceModel,
          x.isLt, hx]
      · have hlow : ¬ R.N + z.val < R.N := by omega
        have hhigh : ¬ R.N + privateCount R.N R.rows.length ≤ R.N + z.val := by
          have := z.isLt
          omega
        simp [rawRowMember, terminalCode, blockTypes, markers, hlow, hhigh]
      · have hlow : ¬ R.N + privateCount R.N R.rows.length + k.val < R.N := by omega
        simp [rawRowMember, terminalCode, blockTypes, markers, hlow]

/-- Equality of predicates on the enumerated range, including the two
    markers and all private anchor types. It is not an oracle premise. -/
theorem rawRowMember_eq_on_range (R : RawMSSCRecord) (h : RawMSSCValid R)
    (b : Block R.rows.length) (n : ℕ) (hn : n < rawRowAlphabet R) :
    rawRowMember R b n =
      decide (n ∈ (blockTypes (scanSourceModel R h) b).image
        (terminalCode R.N R.rows.length)) := by
  obtain ⟨s, rfl⟩ := terminalCode_surjective_bounded R.N R.rows.length n hn
  rw [rawRowMember_code R h b s]
  have hmem : s ∈ blockTypes (scanSourceModel R h) b ↔
      terminalCode R.N R.rows.length s ∈
        (blockTypes (scanSourceModel R h) b).image (terminalCode R.N R.rows.length) := by
    constructor
    · intro hs
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    · intro hs
      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hs
      have hts := terminalCode_injective R.N R.rows.length he
      simpa only [hts] using ht
  simp only [hmem]

theorem rawRowCodes_eq (R : RawMSSCRecord) (h : RawMSSCValid R)
    (b : Block R.rows.length) :
    rawRowCodes R b = directBlockCodes (scanSourceModel R h) b := by
  unfold rawRowCodes directBlockCodes rawRowAlphabet
  apply List.filter_congr
  intro n hn
  exact rawRowMember_eq_on_range R h b n (List.mem_range.mp hn)

theorem rawRowCodes_length_le (R : RawMSSCRecord) (b : Block R.rows.length) :
    (rawRowCodes R b).length ≤ rawRowAlphabet R := by
  simpa only [rawRowCodes, List.length_range] using
    List.length_filter_le (rawRowMember R b) (List.range (rawRowAlphabet R))

def rawRowBlockBits (R : RawMSSCRecord) (b : Block R.rows.length) : List Bool :=
  let codes := rawRowCodes R b
  List.replicate (codes.length - 1) false ++
    codes.flatMap (fun n => true :: (unaryFrame (blockCode b) ++ unaryFrame n))

def rawRowFixedCost (R : RawMSSCRecord) : ℕ :=
  ((blockIndexList R.rows.length).map fun b =>
    combTailCost (rawRowAlphabet R) 1 ((rawRowCodes R b).length - 1)).sum

theorem rawRowBlockBits_eq (R : RawMSSCRecord) (h : RawMSSCValid R)
    (b : Block R.rows.length) :
    rawRowBlockBits R b = directBlockBits (scanSourceModel R h) b := by
  simp only [rawRowBlockBits, rawRowCodes_eq R h, directBlockBits]

theorem rawRowFixedCost_eq (R : RawMSSCRecord) (h : RawMSSCValid R) :
    rawRowFixedCost R = directFixedCost (scanSourceModel R h) := by
  simp only [rawRowFixedCost, rawRowCodes_eq R h, rawRowAlphabet, directFixedCost]

theorem rawRowFixedCost_bound (R : RawMSSCRecord) :
    rawRowFixedCost R ≤ (R.rows.length + 1) * rawRowAlphabet R ^ 2 := by
  unfold rawRowFixedCost
  have h := list_sum_le_length_mul
    ((blockIndexList R.rows.length).map fun b =>
      combTailCost (rawRowAlphabet R) 1 ((rawRowCodes R b).length - 1))
    (rawRowAlphabet R ^ 2) (by
      intro c hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      have ht := combTailCost_le (rawRowAlphabet R) 1 ((rawRowCodes R b).length - 1)
      have hl := rawRowCodes_length_le R b
      have hs : (rawRowCodes R b).length - 1 ≤ rawRowAlphabet R := by omega
      exact ht.trans (by nlinarith))
  simpa only [List.length_map, blockIndexList, List.length_cons, List.length_finRange] using h

def rawRowCanonicalBits (R : RawMSSCRecord) : List Bool :=
  binaryNatFrame R.N ++ binaryNatFrame R.rows.length ++
    binaryNatFrame (rawRowFixedCost R + R.K - R.N) ++
      unaryFrame (blockIndexList R.rows.length).length ++
        (blockIndexList R.rows.length).flatMap (rawRowBlockBits R)

theorem rawRowCanonicalBits_eq (R : RawMSSCRecord) (h : RawMSSCValid R) :
    rawRowCanonicalBits R = directCanonicalBits (scanSourceModel R h) R.K := by
  have hb : rawRowBlockBits R = directBlockBits (scanSourceModel R h) :=
    funext (rawRowBlockBits_eq R h)
  simp only [rawRowCanonicalBits, rawRowFixedCost_eq R h, hb,
    directCanonicalBits]

/-- All branches are the ORIGINAL branches. No source-model construction
    or proof argument occurs in this algorithm. -/
def rawRowMSSCBits (R : RawMSSCRecord) : List Bool :=
  if R.N = 0 then scanEncodeTarget scanFixedYesTarget
  else if R.rows.length ≤ 1 then
    (if R.N ≤ R.K then scanEncodeTarget scanFixedYesTarget else scanEncodeTarget scanFixedNoTarget)
  else if R.K < R.N then scanEncodeTarget scanFixedNoTarget
  else if R.rows.length * R.N ≤ R.K then scanEncodeTarget scanFixedYesTarget
  else rawRowCanonicalBits R

theorem rawRowMSSCBits_eq (R : RawMSSCRecord) (h : RawMSSCValid R) :
    rawRowMSSCBits R = directMSSCBits (scanSourceModel R h) R.K := by
  simp only [rawRowMSSCBits, directMSSCBits, rawRowCanonicalBits_eq R h]

def rawRowRecordBits (R : RawMSSCRecord) : List Bool :=
  if scanSourceValid R then rawRowMSSCBits R else scanEncodeTarget scanFixedNoTarget

theorem rawRowRecordBits_eq (R : RawMSSCRecord) :
    rawRowRecordBits R = directRawSourceBits R := by
  by_cases h : scanSourceValid R = true
  · simp only [rawRowRecordBits, directRawSourceBits, h, ↓reduceIte,
      rawRowMSSCBits_eq R ((scanSourceValid_spec R).mp h)]
  · simp [rawRowRecordBits, directRawSourceBits, h]

def rawRowConstructor (bits : List Bool) : List Bool :=
  match parseSaturatedSource bits with
  | none => scanEncodeTarget scanFixedNoTarget
  | some R => rawRowRecordBits R

/-- Byte equality on ALL source words, including malformed dimensions,
    repeated identifiers, noncanonical binary numerals and trivial cases. -/
theorem rawRowConstructor_eq (bits : List Bool) :
    rawRowConstructor bits = scanEncodedConstructor bits := by
  rw [← directBoundedConstructor_eq]
  unfold rawRowConstructor directBoundedConstructor
  cases h : parseSaturatedSource bits with
  | none => rfl
  | some R => exact rawRowRecordBits_eq R

def rawRowAlphabetBound (L : ℕ) : ℕ := (L + 1) ^ 2 + 3
def rawRowCostBound (L : ℕ) : ℕ := (L + 1) * rawRowAlphabetBound L ^ 2

/-- Polynomial numeric bounds are consequences of the actual total parser,
    not promises that raw binary headers denote small numbers. -/
theorem parsed_raw_row_bounds (bits : List Bool) (R : RawMSSCRecord)
    (h : parseSaturatedSource bits = some R) :
    rawRowAlphabet R ≤ rawRowAlphabetBound bits.length ∧
      rawRowFixedCost R ≤ rawRowCostBound bits.length ∧
      rawRowFixedCost R + R.K - R.N ≤ rawRowCostBound bits.length + (bits.length + 1) ^ 2 := by
  obtain ⟨hs, hN, hm, hK, hx⟩ := parsed_saturated_source_bounds bits R h
  have hrows : R.rows.length + 1 ≤ bits.length + 1 := by
    unfold rawRecordSize at hs
    omega
  have halpha : rawRowAlphabet R ≤ rawRowAlphabetBound bits.length := by
    have hp := Nat.mul_le_mul hrows hN
    unfold rawRowAlphabet rawRowAlphabetBound
    nlinarith
  have hcost := rawRowFixedCost_bound R
  have hsquare : rawRowAlphabet R ^ 2 ≤ rawRowAlphabetBound bits.length ^ 2 := by nlinarith
  have hprod := Nat.mul_le_mul hrows hsquare
  have hc : rawRowFixedCost R ≤ rawRowCostBound bits.length := by
    unfold rawRowCostBound
    exact hcost.trans hprod
  exact ⟨halpha, hc, by omega⟩

def originalConstructorMachineOfRawRows
    (h : Turing.TM2ComputableInPolyTime
      (fun bits : List Bool => bits) (fun bits : List Bool => bits)
      rawRowConstructor) : ConstructorMachineWitness := by
  have he : rawRowConstructor = scanEncodedConstructor := funext rawRowConstructor_eq
  simpa only [he] using h

theorem full_raw_row_constructor_interface (input : List Bool) (lambda : ℝ) :
    (rawRowConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (rawRowConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (rawRowConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (rawRowConstructor input).length ∧
          boundedEncodedTarget (rawRowConstructor input) cert = true) := by
  simpa only [rawRowConstructor_eq, boundedEncodedTarget_eq] using
    full_explicit_encoded_reduction input lambda

/- The new algorithm bodies expose concrete supplied-list membership and
bounded arithmetic, but are not emitted finite-TM2 code. Concrete nested
parsing, row scans, arithmetic, primitive/caller composition, total step and
cleanup bounds, the independent clade verifier, closed upstream encoded
hardness and every kernel check remain open. No biological model changes.
-/

end PolytomyReductionModel
