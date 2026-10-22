/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/certificate.

Independent target bit encoding/decoding and full total bit-to-bit finite
reduction. The target decoder validates supplied target records; it does not
reconstruct or consult an MSSC source. Noncomputable semantic definitions
are not presented as executable polynomial machines.
-/
import PolytomyRawTargetValidation

namespace PolytomyReductionModel
noncomputable section

def readTargetTree (N m : ℕ) (bits : List Bool) :
    Option (BTree (Cell N m) × List Bool) := parseBitPrefix N m bits.length bits

theorem readTargetTree_encode {N m : ℕ} (T : BTree (Cell N m)) (rest : List Bool) :
    readTargetTree N m (treeBits T ++ rest) = some (T, rest) := by
  apply parseBitPrefix_encode
  have h := vertexCount_le_treeBits_length T
  simp only [List.length_append]
  omega

abbrev AnyRawTargetRows := Σ N : ℕ, Σ m : ℕ, RawTargetRows N m

def encodeRawTargetRows {N m : ℕ} (R : RawTargetRows N m) : List Bool :=
  binaryNatFrame N ++ binaryNatFrame m ++ binaryNatFrame R.budget ++
    encodeFramedList treeBits R.rows

def parseRawTargetPrefix (bits : List Bool) : Option (AnyRawTargetRows × List Bool) :=
  match readBinaryNatFrame bits with
  | none => none
  | some (N, r1) =>
      match readBinaryNatFrame r1 with
      | none => none
      | some (m, r2) =>
          match readBinaryNatFrame r2 with
          | none => none
          | some (budget, r3) =>
              match readFramedList (readTargetTree N m) r3 with
              | none => none
              | some (rows, rest) => some (⟨N, m, ⟨budget, rows⟩⟩, rest)

theorem parseRawTargetPrefix_encode {N m : ℕ} (R : RawTargetRows N m) (rest : List Bool) :
    parseRawTargetPrefix (encodeRawTargetRows R ++ rest) = some (⟨N, m, R⟩, rest) := by
  have hrows := readFramedList_encode treeBits (readTargetTree N m)
    readTargetTree_encode R.rows rest
  simp only [encodeRawTargetRows, List.append_assoc, parseRawTargetPrefix,
    readBinaryNatFrame_encode, hrows]

def parseRawTarget (bits : List Bool) : Option AnyRawTargetRows :=
  match parseRawTargetPrefix bits with
  | some (R, []) => some R
  | _ => none

theorem parseRawTarget_encode {N m : ℕ} (R : RawTargetRows N m) :
    parseRawTarget (encodeRawTargetRows R) = some ⟨N, m, R⟩ := by
  have h := parseRawTargetPrefix_encode R []
  simp only [List.append_nil] at h
  simp [parseRawTarget, h]

def decodeTargetBits (bits : List Bool) : Option AnyBlockTarget :=
  match parseRawTarget bits with
  | none => none
  | some ⟨N, m, R⟩ =>
      match decodeRawTargetRows R with
      | none => none
      | some G => some ⟨N, m, G⟩

def encodeAnyTarget (G : AnyBlockTarget) : List Bool :=
  encodeRawTargetRows (targetToRows G.2.2)

theorem decodeTargetBits_encode (G : AnyBlockTarget) (h : MarkedTargetDomain G.2.2) :
    decodeTargetBits (encodeAnyTarget G) = some G := by
  rcases G with ⟨N, m, G⟩
  simp [encodeAnyTarget, decodeTargetBits, parseRawTarget_encode,
    decodeRawTargetRows_targetToRows G h]

theorem decodeTargetBits_marked (bits : List Bool) (G : AnyBlockTarget)
    (h : decodeTargetBits bits = some G) : MarkedTargetDomain G.2.2 := by
  cases hp : parseRawTarget bits with
  | none => simp [decodeTargetBits, hp] at h
  | some R =>
      rcases R with ⟨N, m, R⟩
      cases hr : decodeRawTargetRows R with
      | none => simp [decodeTargetBits, hp, hr] at h
      | some Q =>
          have he : (⟨N, m, Q⟩ : AnyBlockTarget) = G := by
            simpa [decodeTargetBits, hp, hr] using h
          rw [← he]
          exact decodeRawTargetRows_marked R Q hr

def EncodedTargetCartaDecision (input : List Bool) (lambda : ℝ) : Prop :=
  ∃ G : AnyBlockTarget, decodeTargetBits input = some G ∧ AnyTargetCartaDecision G lambda

def checkEncodedTarget (input cert : List Bool) : Bool :=
  match decodeTargetBits input with
  | none => false
  | some G => checkBlockTargetBits G.2.2 cert

/-- Every target string is handled. Successful validation certifies the
    independent marked-star domain, so actual compatible labels are soundly
    eliminated. The verifier never receives a source construction witness. -/
theorem encoded_target_actual_iff_checked (input : List Bool) (lambda : ℝ) :
    EncodedTargetCartaDecision input lambda ↔
      ∃ cert : List Bool, checkEncodedTarget input cert = true := by
  constructor
  · rintro ⟨G, hd, hG⟩
    have hm := decodeTargetBits_marked input G hd
    obtain ⟨cert, hc⟩ := (marked_target_actual_iff_bits G.2.2 hm lambda).mp hG
    exact ⟨cert, by simpa [checkEncodedTarget, hd] using hc⟩
  · rintro ⟨cert, hc⟩
    cases hd : decodeTargetBits input with
    | none => simp [checkEncodedTarget, hd] at hc
    | some G =>
        have hm := decodeTargetBits_marked input G hd
        refine ⟨G, hd, (marked_target_actual_iff_bits G.2.2 hm lambda).mpr ?_⟩
        exact ⟨cert, by simpa [checkEncodedTarget, hd] using hc⟩

def encodedSourceToTarget (input : List Bool) : List Bool :=
  encodeAnyTarget (totalSourceBitTarget input)

/-- FULL total fixed-Boolean-source to fixed-Boolean-target FINITE semantic
    reduction, with every malformed and boundary source case included. -/
theorem full_encoded_source_actual_reduction (input : List Bool) (lambda : ℝ) :
    SourceBitMSSCDecision input ↔
      EncodedTargetCartaDecision (encodedSourceToTarget input) lambda := by
  have hd := decodeTargetBits_encode (totalSourceBitTarget input)
    (totalSourceBitTarget_marked input)
  simpa [EncodedTargetCartaDecision, encodedSourceToTarget, hd] using
    full_total_source_actual_reduction input lambda

theorem full_encoded_source_checked_reduction (input : List Bool) :
    SourceBitMSSCDecision input ↔
      ∃ cert : List Bool, checkEncodedTarget (encodedSourceToTarget input) cert = true := by
  exact (full_encoded_source_actual_reduction input 0).trans
    (encoded_target_actual_iff_checked (encodedSourceToTarget input) 0)

/- No encoded polynomial-time reduction has been certified. The definitions
are a noncomputable semantic specification. Target-parser consumption and
encoded output/certificate bounds must be connected to a concrete machine;
formal source hardness and all elaboration also remain outstanding. -/

end
end PolytomyReductionModel
