/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/machine certificate.

All-string binary-width bounds for the explicit source constructor. These
control the representation of enormous malformed headers and budgets,
without pretending their numeric values are input-length bounded. The full
actual-label/all-refinement endpoint is retained. TM2 programs and their
step bounds remain separate open obligations.
-/
import PolytomyConcreteMachineInterface
import Mathlib.Data.Nat.Size

namespace PolytomyReductionModel
universe u

theorem fromBinaryBits_lt_pow (bits : List Bool) :
    fromBinaryBits bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [fromBinaryBits]
  | cons b bits ih =>
      change Nat.bit b (fromBinaryBits bits) < 2 ^ (bits.length + 1)
      rw [Nat.pow_succ]
      cases b <;> simp only [Nat.bit] <;> omega

/-- A noncanonical high-zero payload can be longer, but never shorter,
    than the canonical binary representation of the value it denotes. -/
theorem fromBinaryBits_width_le (bits : List Bool) :
    (fromBinaryBits bits).bits.length ≤ bits.length := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  exact fromBinaryBits_lt_pow bits

/-- Both the actual unary width frame and its payload have been consumed.
    This holds for every successful parse, not only canonical encodings. -/
theorem readBinaryNatFrame_width_consumption (bits : List Bool) (n : ℕ)
    (rest : List Bool) (h : readBinaryNatFrame bits = some (n, rest)) :
    2 * n.bits.length + 1 + rest.length ≤ bits.length := by
  cases hp : readUnaryFrame bits with
  | none => simp [readBinaryNatFrame, hp] at h
  | some pair =>
      obtain ⟨width, tail⟩ := pair
      have hc := readUnaryFrame_consumption bits width tail hp
      by_cases hw : width ≤ tail.length
      · simp only [readBinaryNatFrame, hp, if_pos hw, Option.some.injEq,
          Prod.mk.injEq] at h
        have hn := fromBinaryBits_width_le (tail.take width)
        have he : (tail.take width).length = width := by
          simp only [List.length_take, Nat.min_eq_left hw]
        rw [h.1, he] at hn
        have hr : (tail.drop width).length = rest.length := congrArg List.length h.2
        rw [List.length_drop] at hr
        omega
      · simp [readBinaryNatFrame, hp, hw] at h

theorem readBinaryNatFrame_width_remaining (bits : List Bool) (n : ℕ)
    (rest : List Bool) (h : readBinaryNatFrame bits = some (n, rest)) :
    n.bits.length + rest.length ≤ bits.length := by
  have hc := readBinaryNatFrame_width_consumption bits n rest h
  omega

/-- Canonical bit widths of every number explicitly present in a row. -/
def rowNumericWidth (row : List ℕ) : ℕ :=
  (row.map (fun n => n.bits.length)).sum

def rowsNumericWidth (rows : List (List ℕ)) : ℕ :=
  (rows.map rowNumericWidth).sum

def rawNumericWidth (R : RawMSSCRecord) : ℕ :=
  R.N.bits.length + R.declaredM.bits.length + R.K.bits.length +
    rowsNumericWidth R.rows

theorem readNatRow_width_remaining (bits : List Bool) (row : List ℕ)
    (rest : List Bool)
    (h : readFramedList readBinaryNatFrame bits = some (row, rest)) :
    rowNumericWidth row + rest.length ≤ bits.length := by
  have hc := readFramedList_consumption readBinaryNatFrame
    (fun n => n.bits.length) readBinaryNatFrame_width_remaining bits row rest h
  change row.length + 1 + rowNumericWidth row + rest.length ≤ bits.length at hc
  omega

theorem readRows_width_remaining (bits : List Bool) (rows : List (List ℕ))
    (rest : List Bool)
    (h : readFramedList (readFramedList readBinaryNatFrame) bits = some (rows, rest)) :
    rowsNumericWidth rows + rest.length ≤ bits.length := by
  have hc := readFramedList_consumption (readFramedList readBinaryNatFrame)
    rowNumericWidth readNatRow_width_remaining bits rows rest h
  change rows.length + 1 + rowsNumericWidth rows + rest.length ≤ bits.length at hc
  omega

theorem parseRawMSSCPrefix_width (bits : List Bool) (R : RawMSSCRecord)
    (rest : List Bool) (h : parseRawMSSCPrefix bits = some (R, rest)) :
    rawNumericWidth R + rest.length ≤ bits.length := by
  cases h1 : readBinaryNatFrame bits with
  | none => simp [parseRawMSSCPrefix, h1] at h
  | some pair =>
      obtain ⟨N, r1⟩ := pair
      cases h2 : readBinaryNatFrame r1 with
      | none => simp [parseRawMSSCPrefix, h1, h2] at h
      | some pair =>
          obtain ⟨m, r2⟩ := pair
          cases h3 : readBinaryNatFrame r2 with
          | none => simp [parseRawMSSCPrefix, h1, h2, h3] at h
          | some pair =>
              obtain ⟨K, r3⟩ := pair
              cases h4 : readFramedList (readFramedList readBinaryNatFrame) r3 with
              | none => simp [parseRawMSSCPrefix, h1, h2, h3, h4] at h
              | some pair =>
                  obtain ⟨rows, after⟩ := pair
                  simp only [parseRawMSSCPrefix, h1, h2, h3, h4, Option.some.injEq,
                    Prod.mk.injEq] at h
                  have hb1 := readBinaryNatFrame_width_remaining bits N r1 h1
                  have hb2 := readBinaryNatFrame_width_remaining r1 m r2 h2
                  have hb3 := readBinaryNatFrame_width_remaining r2 K r3 h3
                  have hb4 := readRows_width_remaining r3 rows after h4
                  rw [← h.1, ← h.2]
                  simp only [rawNumericWidth]
                  omega

/-- Raw dimensions and budgets may have exponential VALUE. Their total
    canonical numeric BIT LENGTH is bounded before validity is checked. -/
theorem parseRawMSSC_width_bound (bits : List Bool) (R : RawMSSCRecord)
    (h : parseRawMSSC bits = some R) : rawNumericWidth R ≤ bits.length := by
  cases hp : parseRawMSSCPrefix bits with
  | none => simp [parseRawMSSC, hp] at h
  | some pair =>
      obtain ⟨Q, rest⟩ := pair
      cases rest with
      | cons b rest => simp [parseRawMSSC, hp] at h
      | nil =>
          have he : Q = R := by simpa [parseRawMSSC, hp] using h
          subst Q
          simpa using parseRawMSSCPrefix_width bits R [] hp

theorem parsed_source_header_widths (bits : List Bool) (R : RawMSSCRecord)
    (h : parseRawMSSC bits = some R) :
    R.N.bits.length ≤ bits.length ∧ R.declaredM.bits.length ≤ bits.length ∧
      R.K.bits.length ≤ bits.length := by
  have hw := parseRawMSSC_width_bound bits R h
  unfold rawNumericWidth at hw
  omega

/-- The explicit guard bounds enumerable dimensions in VALUE, while the
    budget remains bounded only in BIT LENGTH before branch selection. -/
theorem scanned_valid_source_resources (bits : List Bool) (R : RawMSSCRecord)
    (hp : parseRawMSSC bits = some R) (hv : scanSourceValid R = true) :
    R.N ≤ bits.length ∧ R.rows.length ≤ bits.length ∧
      rawNumericWidth R ≤ bits.length := by
  obtain ⟨hN, hm, hr⟩ := parsed_valid_dimensions_bounded bits R hp
    ((scanSourceValid_spec R).mp hv)
  exact ⟨hN, hr, parseRawMSSC_width_bound bits R hp⟩

/-- The independent target parser also permits large binary budgets and
    dimensions before its guard. Their widths, not values, are bounded. -/
def rawTargetHeaderWidth (R : AnyRawTargetRows) : ℕ :=
  R.1.bits.length + R.2.1.bits.length + R.2.2.budget.bits.length

theorem parseRawTargetPrefix_header_width (bits : List Bool) (R : AnyRawTargetRows)
    (rest : List Bool) (h : parseRawTargetPrefix bits = some (R, rest)) :
    rawTargetHeaderWidth R + rest.length ≤ bits.length := by
  cases h1 : readBinaryNatFrame bits with
  | none => simp [parseRawTargetPrefix, h1] at h
  | some pair =>
      obtain ⟨N, r1⟩ := pair
      cases h2 : readBinaryNatFrame r1 with
      | none => simp [parseRawTargetPrefix, h1, h2] at h
      | some pair =>
          obtain ⟨m, r2⟩ := pair
          cases h3 : readBinaryNatFrame r2 with
          | none => simp [parseRawTargetPrefix, h1, h2, h3] at h
          | some pair =>
              obtain ⟨budget, r3⟩ := pair
              cases h4 : readFramedList (readTargetTree N m) r3 with
              | none => simp [parseRawTargetPrefix, h1, h2, h3, h4] at h
              | some pair =>
                  obtain ⟨rows, after⟩ := pair
                  simp only [parseRawTargetPrefix, h1, h2, h3, h4,
                    Option.some.injEq, Prod.mk.injEq] at h
                  have hb1 := readBinaryNatFrame_width_remaining bits N r1 h1
                  have hb2 := readBinaryNatFrame_width_remaining r1 m r2 h2
                  have hb3 := readBinaryNatFrame_width_remaining r2 budget r3 h3
                  have hb4 := readFramedList_consumption (readTargetTree N m)
                    vertexCount (readTargetTree_consumption N m) r3 rows after h4
                  rw [← h.1, ← h.2]
                  simp only [rawTargetHeaderWidth]
                  omega

theorem parseRawTarget_header_width_bound (bits : List Bool) (R : AnyRawTargetRows)
    (h : parseRawTarget bits = some R) : rawTargetHeaderWidth R ≤ bits.length := by
  cases hp : parseRawTargetPrefix bits with
  | none => simp [parseRawTarget, hp] at h
  | some pair =>
      obtain ⟨Q, rest⟩ := pair
      cases rest with
      | cons b rest => simp [parseRawTarget, hp] at h
      | nil =>
          have he : Q = R := by simpa [parseRawTarget, hp] using h
          subst Q
          simpa using parseRawTargetPrefix_header_width bits R [] hp

theorem scanned_target_header_widths (bits : List Bool) (R : AnyRawTargetRows)
    (h : scanParseTarget bits = some R) :
    R.1.bits.length ≤ bits.length ∧ R.2.1.bits.length ≤ bits.length ∧
      R.2.2.budget.bits.length ≤ bits.length := by
  have hp : parseRawTarget bits = some R := by simpa only [scanParseTarget_eq] using h
  have hw := parseRawTarget_header_width_bound bits R hp
  unfold rawTargetHeaderWidth at hw
  omega

/-- This supplements, rather than weakens, the entire byte-level theorem.
    No abstract unit-cost arithmetic convention or machine witness is used. -/
theorem full_explicit_binary_resource_interface (input : List Bool) (lambda : ℝ) :
    (∀ R, parseRawMSSC input = some R → rawNumericWidth R ≤ input.length) ∧
    (scanEncodedConstructor input).length ≤ sourceOutputSizeBound input.length ∧
    (SourceBitMSSCDecision input ↔
      EncodedTargetCartaDecision (scanEncodedConstructor input) lambda) ∧
    (EncodedTargetCartaDecision (scanEncodedConstructor input) lambda ↔
      ∃ cert : List Bool,
        cert.length ≤ targetBitCertificateBound (scanEncodedConstructor input).length ∧
        scanPairVerifier (verifierPairBits (scanEncodedConstructor input) cert) = true) := by
  exact ⟨fun R h => parseRawMSSC_width_bound input R h,
    full_explicit_pair_interface input lambda⟩

/- Still OPEN: finite TM2 programs implementing the full constructor and
independent verifier, all-input step bounds including binary arithmetic,
copying and clean halting, compatible formal hardness/composition, and
authorized elaboration. Width/storage bounds are NOT time certificates. -/

end PolytomyReductionModel
