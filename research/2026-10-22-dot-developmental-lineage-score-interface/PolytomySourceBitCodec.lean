/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/certificate.

Explicit fixed-Boolean source records. Numeric headers/indices have binary
payloads, not unary numeric values. Only their bit widths and actual list
record counts use unary framing. Huge declared dimensions therefore remain
possible on short malformed inputs and are handled by the preceding guard.
-/
import PolytomyRawInstanceValidation
import Mathlib.Data.Nat.Bits

namespace PolytomyReductionModel
universe u

def fromBinaryBits (bits : List Bool) : ℕ := bits.foldr Nat.bit 0

theorem fromBinaryBits_bits (n : ℕ) : fromBinaryBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [fromBinaryBits]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      change Nat.bit b (fromBinaryBits n.bits) = Nat.bit b n
      rw [ih]

def binaryNatFrame (n : ℕ) : List Bool := unaryFrame n.bits.length ++ n.bits

def readBinaryNatFrame (bits : List Bool) : Option (ℕ × List Bool) :=
  match readUnaryFrame bits with
  | none => none
  | some (width, rest) =>
      if width ≤ rest.length then
        some (fromBinaryBits (rest.take width), rest.drop width)
      else none

theorem readBinaryNatFrame_encode (n : ℕ) (rest : List Bool) :
    readBinaryNatFrame (binaryNatFrame n ++ rest) = some (n, rest) := by
  simp [binaryNatFrame, List.append_assoc, readBinaryNatFrame,
    readUnaryFrame_encode, fromBinaryBits_bits]

/-- List lengths are actual explicit record counts, each unary-framed in
    the input. They are distinct from a separately declared binary m. -/
def encodeFramedList {A : Type u} (encode : A → List Bool) (xs : List A) : List Bool :=
  unaryFrame xs.length ++ xs.flatMap encode

def readMany {A : Type u} (read : List Bool → Option (A × List Bool)) :
    ℕ → List Bool → Option (List A × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits =>
      match read bits with
      | none => none
      | some (a, rest) =>
          match readMany read count rest with
          | none => none
          | some (xs, after) => some (a :: xs, after)

def readFramedList {A : Type u} (read : List Bool → Option (A × List Bool))
    (bits : List Bool) : Option (List A × List Bool) :=
  match readUnaryFrame bits with
  | none => none
  | some (count, rest) => readMany read count rest

theorem readMany_encode {A : Type u} (encode : A → List Bool)
    (read : List Bool → Option (A × List Bool))
    (hinv : ∀ a rest, read (encode a ++ rest) = some (a, rest)) (xs : List A) :
    ∀ rest, readMany read xs.length (xs.flatMap encode ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => intro rest; simp [readMany]
  | cons a xs ih =>
      intro rest
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readMany]
      rw [hinv a (xs.flatMap encode ++ rest), ih rest]

theorem readFramedList_encode {A : Type u} (encode : A → List Bool)
    (read : List Bool → Option (A × List Bool))
    (hinv : ∀ a rest, read (encode a ++ rest) = some (a, rest))
    (xs : List A) (rest : List Bool) :
    readFramedList read (encodeFramedList encode xs ++ rest) = some (xs, rest) := by
  simp only [encodeFramedList, List.append_assoc, readFramedList, readUnaryFrame_encode]
  exact readMany_encode encode read hinv xs rest

def encodeRawMSSC (R : RawMSSCRecord) : List Bool :=
  binaryNatFrame R.N ++ binaryNatFrame R.declaredM ++ binaryNatFrame R.K ++
    encodeFramedList (encodeFramedList binaryNatFrame) R.rows

def parseRawMSSCPrefix (bits : List Bool) : Option (RawMSSCRecord × List Bool) :=
  match readBinaryNatFrame bits with
  | none => none
  | some (N, r1) =>
      match readBinaryNatFrame r1 with
      | none => none
      | some (m, r2) =>
          match readBinaryNatFrame r2 with
          | none => none
          | some (K, r3) =>
              match readFramedList (readFramedList readBinaryNatFrame) r3 with
              | none => none
              | some (rows, rest) => some (⟨N, m, K, rows⟩, rest)

theorem parseRawMSSCPrefix_encode (R : RawMSSCRecord) (rest : List Bool) :
    parseRawMSSCPrefix (encodeRawMSSC R ++ rest) = some (R, rest) := by
  have hr : ∀ row rest,
      readFramedList readBinaryNatFrame (encodeFramedList binaryNatFrame row ++ rest) =
        some (row, rest) := readFramedList_encode _ _ readBinaryNatFrame_encode
  have hrows := readFramedList_encode (encodeFramedList binaryNatFrame)
    (readFramedList readBinaryNatFrame) hr R.rows rest
  simp only [encodeRawMSSC, List.append_assoc, parseRawMSSCPrefix,
    readBinaryNatFrame_encode, hrows]

def parseRawMSSC (bits : List Bool) : Option RawMSSCRecord :=
  match parseRawMSSCPrefix bits with
  | some (R, []) => some R
  | _ => none

theorem parseRawMSSC_encode (R : RawMSSCRecord) :
    parseRawMSSC (encodeRawMSSC R) = some R := by
  have h := parseRawMSSCPrefix_encode R []
  simp only [List.append_nil] at h
  simp [parseRawMSSC, h]

/-- Arbitrary malformed strings are not assumed to be canonical encodings.
    A successful parse must still pass the dimension/range/coverage guard. -/
def SourceBitMSSCDecision (bits : List Bool) : Prop :=
  ∃ R : RawMSSCRecord, parseRawMSSC bits = some R ∧ RawMSSCDecision R

theorem sourceBitMSSCDecision_encode_iff (R : RawMSSCRecord) :
    SourceBitMSSCDecision (encodeRawMSSC R) ↔ RawMSSCDecision R := by
  simp [SourceBitMSSCDecision, parseRawMSSC_encode]

theorem sourceBitMSSCDecision_parse_failure (bits : List Bool)
    (h : parseRawMSSC bits = none) : ¬ SourceBitMSSCDecision bits := by
  simp [SourceBitMSSCDecision, h]

theorem sourceBitMSSCDecision_invalid_record (bits : List Bool) (R : RawMSSCRecord)
    (hp : parseRawMSSC bits = some R) (hv : ¬ RawMSSCValid R) :
    ¬ SourceBitMSSCDecision bits := by
  simp [SourceBitMSSCDecision, hp, rawMSSCDecision_invalid R hv]

/-- Canonical source serialization connected to the FULL existing finite
    reduction. A target instance serializer/machine is still not supplied. -/
theorem full_source_record_bit_reduction (R : RawMSSCRecord) (h : RawMSSCValid R)
    (hN : 0 < R.N) (hm : 2 ≤ R.rows.length)
    (hNK : R.N ≤ R.K) (hKmN : R.K ≤ R.rows.length * R.N) :
    SourceBitMSSCDecision (encodeRawMSSC R) ↔
      ∃ bits : List Bool, bits.length ≤ bitCertificateBound R.N R.rows.length ∧
        checkBlockTargetBits (canonicalBlockTarget (rawToMSSC R h) R.K) bits = true := by
  exact (sourceBitMSSCDecision_encode_iff R).trans
    (full_rawMSSC_bit_reduction R h hN hm hNK hKmN)

/- Source parsing/validation is now specified on arbitrary bit strings, but
its machine cost and parser-consumption/input-size theorems remain unproved.
Canonical encode/decode inversion does not alone certify those bounds.
The later SourceSizeBounds and TotalSourceReduction companions address
consumption and finite boundary cases. Target-instance encoding and concrete
polynomial-machine composition still prevent a formal NP-completeness claim. -/

end PolytomyReductionModel
