/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No execution or kernel certificate.

An INTERNAL unary record representation for the original saturated source
parser. The external source/target encodings are unchanged. Exact inverse,
all-successful-parse soundness, physical length, and all-input constructor
factorization are supplied. The complete emitted normalizer and downstream
constructor remain operational obligations, not consequences of this codec.
-/
import PolytomyUnaryCountCaller

namespace PolytomyReductionModel
universe u

def encodeUnaryRaw (R : RawMSSCRecord) : List Bool :=
  unaryFrame R.N ++ unaryFrame R.declaredM ++ unaryFrame R.K ++
    encodeFramedList (encodeFramedList unaryFrame) R.rows

def parseUnaryRawPrefix (bits : List Bool) : Option (RawMSSCRecord × List Bool) :=
  match readUnaryFrame bits with
  | none => none
  | some (N, r1) =>
      match readUnaryFrame r1 with
      | none => none
      | some (m, r2) =>
          match readUnaryFrame r2 with
          | none => none
          | some (K, r3) =>
              match readFramedList (readFramedList readUnaryFrame) r3 with
              | none => none
              | some (rows, rest) => some (⟨N, m, K, rows⟩, rest)

def parseUnaryRaw (bits : List Bool) : Option RawMSSCRecord :=
  match parseUnaryRawPrefix bits with
  | some (R, []) => some R
  | _ => none

theorem parseUnaryRawPrefix_encode (R : RawMSSCRecord) (rest : List Bool) :
    parseUnaryRawPrefix (encodeUnaryRaw R ++ rest) = some (R, rest) := by
  have hr : ∀ row rest,
      readFramedList readUnaryFrame (encodeFramedList unaryFrame row ++ rest) =
        some (row, rest) := readFramedList_encode _ _ readUnaryFrame_encode
  have hrows := readFramedList_encode (encodeFramedList unaryFrame)
    (readFramedList readUnaryFrame) hr R.rows rest
  simp only [encodeUnaryRaw, List.append_assoc, parseUnaryRawPrefix,
    readUnaryFrame_encode, hrows]

theorem parseUnaryRaw_encode (R : RawMSSCRecord) :
    parseUnaryRaw (encodeUnaryRaw R) = some R := by
  have h := parseUnaryRawPrefix_encode R []
  simp only [List.append_nil] at h
  simp [parseUnaryRaw, h]

/-- Unlike an encoder inverse alone, this proves what EVERY successful
    read means. Both exact count and untouched suffix are retained. -/
theorem readMany_encoding_sound {A : Type u}
    (read : List Bool → Option (A × List Bool)) (encode : A → List Bool)
    (hs : ∀ bits a rest, read bits = some (a, rest) → bits = encode a ++ rest)
    (count : ℕ) : ∀ bits xs rest, readMany read count bits = some (xs, rest) →
      xs.length = count ∧ bits = xs.flatMap encode ++ rest := by
  induction count with
  | zero =>
      intro bits xs rest h
      simp only [readMany, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | succ count ih =>
      intro bits xs rest h
      cases hp : read bits with
      | none => simp [readMany, hp] at h
      | some p =>
          rcases p with ⟨a, tail⟩
          cases hq : readMany read count tail with
          | none => simp [readMany, hp, hq] at h
          | some q =>
              rcases q with ⟨ys, after⟩
              simp only [readMany, hp, hq, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hlen, htail⟩ := ih tail ys after hq
              have hfirst := hs bits a tail hp
              rw [← h.1, ← h.2]
              constructor
              · simp [hlen]
              · simpa only [List.flatMap_cons, List.append_assoc] using
                  hfirst.trans (congrArg (fun z => encode a ++ z) htail)

theorem readFramedList_encoding_sound {A : Type u}
    (read : List Bool → Option (A × List Bool)) (encode : A → List Bool)
    (hs : ∀ bits a rest, read bits = some (a, rest) → bits = encode a ++ rest)
    (bits : List Bool) (xs : List A) (rest : List Bool)
    (h : readFramedList read bits = some (xs, rest)) :
    bits = encodeFramedList encode xs ++ rest := by
  cases hp : readUnaryFrame bits with
  | none => simp [readFramedList, hp] at h
  | some p =>
      rcases p with ⟨count, tail⟩
      have hm : readMany read count tail = some (xs, rest) := by
        simpa only [readFramedList, hp] using h
      obtain ⟨hlen, htail⟩ := readMany_encoding_sound read encode hs count tail xs rest hm
      rw [readUnaryFrame_sound bits count tail hp, htail, ← hlen]
      simp only [encodeFramedList, List.append_assoc]

theorem parseUnaryRawPrefix_sound (bits : List Bool) (R : RawMSSCRecord)
    (rest : List Bool) (h : parseUnaryRawPrefix bits = some (R, rest)) :
    bits = encodeUnaryRaw R ++ rest := by
  cases h1 : readUnaryFrame bits with
  | none => simp [parseUnaryRawPrefix, h1] at h
  | some p1 =>
      rcases p1 with ⟨N, r1⟩
      cases h2 : readUnaryFrame r1 with
      | none => simp [parseUnaryRawPrefix, h1, h2] at h
      | some p2 =>
          rcases p2 with ⟨m, r2⟩
          cases h3 : readUnaryFrame r2 with
          | none => simp [parseUnaryRawPrefix, h1, h2, h3] at h
          | some p3 =>
              rcases p3 with ⟨K, r3⟩
              cases h4 : readFramedList (readFramedList readUnaryFrame) r3 with
              | none => simp [parseUnaryRawPrefix, h1, h2, h3, h4] at h
              | some p4 =>
                  rcases p4 with ⟨rows, after⟩
                  have hr : ∀ xs row tail,
                      readFramedList readUnaryFrame xs = some (row, tail) →
                        xs = encodeFramedList unaryFrame row ++ tail :=
                    readFramedList_encoding_sound _ _ readUnaryFrame_sound
                  have hrows := readFramedList_encoding_sound
                    (readFramedList readUnaryFrame) (encodeFramedList unaryFrame)
                    hr r3 rows after h4
                  simp only [parseUnaryRawPrefix, h1, h2, h3, h4,
                    Option.some.injEq, Prod.mk.injEq] at h
                  rw [← h.1, ← h.2]
                  rw [readUnaryFrame_sound bits N r1 h1,
                    readUnaryFrame_sound r1 m r2 h2,
                    readUnaryFrame_sound r2 K r3 h3, hrows]
                  simp only [encodeUnaryRaw, List.append_assoc]

theorem parseUnaryRaw_sound (bits : List Bool) (R : RawMSSCRecord)
    (h : parseUnaryRaw bits = some R) : bits = encodeUnaryRaw R := by
  cases hp : parseUnaryRawPrefix bits with
  | none => simp [parseUnaryRaw, hp] at h
  | some p =>
      rcases p with ⟨Q, rest⟩
      cases rest with
      | nil =>
          have he : Q = R := by simpa [parseUnaryRaw, hp] using h
          subst Q
          simpa only [List.append_nil] using parseUnaryRawPrefix_sound bits R [] hp
      | cons b rest => simp [parseUnaryRaw, hp] at h

theorem unaryItems_length (row : List ℕ) :
    (row.flatMap unaryFrame).length = row.sum + row.length := by
  induction row with
  | nil => simp
  | cons n row ih =>
      simp only [List.flatMap_cons, List.length_append, List.sum_cons,
        List.length_cons, ih]
      have hu : (unaryFrame n).length = n + 1 := by simp [unaryFrame]
      rw [hu]
      omega

theorem unaryRow_length (row : List ℕ) :
    (encodeFramedList unaryFrame row).length = 2 * row.length + row.sum + 1 := by
  simp only [encodeFramedList, List.length_append, unaryItems_length,
    unaryFrame, List.length_replicate, List.length_singleton]
  omega

theorem unaryRowsPayload_length (rows : List (List ℕ)) :
    (rows.flatMap (encodeFramedList unaryFrame)).length =
      2 * rows.flatten.length + rows.flatten.sum + rows.length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp only [List.flatMap_cons, List.length_append, unaryRow_length,
        List.flatten_cons, List.sum_append, List.length_cons, ih]
      omega

theorem unaryRows_length (rows : List (List ℕ)) :
    (encodeFramedList (encodeFramedList unaryFrame) rows).length =
      2 * rows.length + 2 * rows.flatten.length + rows.flatten.sum + 1 := by
  simp only [encodeFramedList, List.length_append, unaryRowsPayload_length,
    unaryFrame, List.length_replicate, List.length_singleton]
  omega

theorem encodeUnaryRaw_length (R : RawMSSCRecord) :
    (encodeUnaryRaw R).length = sourceUnaryValueMass R + rawRecordSize R + 2 := by
  simp only [encodeUnaryRaw, List.length_append, unaryRows_length,
    unaryFrame, List.length_replicate, List.length_singleton]
  unfold sourceUnaryValueMass rawRecordSize
  omega

/-- An arbitrary successful INTERNAL unary parse already bounds every
    represented number physically. No source-validity promise is used. -/
theorem parsed_unary_raw_mass (bits : List Bool) (R : RawMSSCRecord)
    (h : parseUnaryRaw bits = some R) :
    sourceUnaryValueMass R + rawRecordSize R + 2 = bits.length := by
  rw [parseUnaryRaw_sound bits R h, encodeUnaryRaw_length]

def normalizedSource (bits : List Bool) : List Bool :=
  match parseSaturatedSource bits with
  | none => [false]
  | some R => true :: encodeUnaryRaw R

/-- This internal format is tagged. A malformed representation, including
    extra bits after either a failure tag or a complete record, is rejected. -/
def readNormalizedSource : List Bool → Option RawMSSCRecord
  | true :: bits => parseUnaryRaw bits
  | _ => none

theorem readNormalizedSource_normalized (bits : List Bool) :
    readNormalizedSource (normalizedSource bits) = parseSaturatedSource bits := by
  cases hp : parseSaturatedSource bits with
  | none => simp [normalizedSource, hp, readNormalizedSource]
  | some R => simp [normalizedSource, hp, readNormalizedSource, parseUnaryRaw_encode]

def unaryNormalSizeBound (L : ℕ) : ℕ := 3 * (L + 1) ^ 2 + L + 3

theorem normalizedSource_length (bits : List Bool) :
    (normalizedSource bits).length ≤ unaryNormalSizeBound bits.length := by
  cases hp : parseSaturatedSource bits with
  | none =>
      simp only [normalizedSource, hp, List.length_singleton]
      unfold unaryNormalSizeBound
      omega
  | some R =>
      have hm := parsed_saturated_unary_mass bits R hp
      have hs := (parsed_saturated_source_bounds bits R hp).1
      simp only [normalizedSource, hp, List.length_cons, encodeUnaryRaw_length]
      unfold unaryNormalSizeBound
      omega

def normalRecordConstructor (bits : List Bool) : List Bool :=
  match readNormalizedSource bits with
  | none => scanEncodeTarget scanFixedNoTarget
  | some R => rawRowRecordBits R

/-- The factorization is byte-exact on ALL original input words, not only
    valid instances, and does not alter either external language. -/
theorem normalRecordConstructor_normalized (bits : List Bool) :
    normalRecordConstructor (normalizedSource bits) = rawRowConstructor bits := by
  unfold normalRecordConstructor rawRowConstructor
  rw [readNormalizedSource_normalized]

theorem normalized_constructor_original (bits : List Bool) :
    normalRecordConstructor (normalizedSource bits) = scanEncodedConstructor bits := by
  rw [normalRecordConstructor_normalized, rawRowConstructor_eq]

theorem full_reduction_with_unary_normal_form (input : List Bool) (lambda : ℝ) :
    (normalizedSource input).length ≤ unaryNormalSizeBound input.length ∧
      (normalRecordConstructor (normalizedSource input)).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (normalRecordConstructor (normalizedSource input)) lambda) ∧
      (EncodedTargetCartaDecision (normalRecordConstructor (normalizedSource input)) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (normalRecordConstructor (normalizedSource input)).length ∧
          boundedEncodedTarget (normalRecordConstructor (normalizedSource input)) cert = true) := by
  rw [normalRecordConstructor_normalized]
  exact ⟨normalizedSource_length input, full_raw_row_constructor_interface input lambda⟩

/- Neither normalizedSource nor normalRecordConstructor has an emitted
whole-machine witness here. The actual primitive readers do not by
themselves realize the nested grammar: physical loop counters, partial
storage, copying, cap creation, suffix checks and failure cleanup still
need code and transition bounds. This is an internal codec specification
for that construction, not a substitute target or a machine-time theorem.
The original full constructor/checker, closed compatible source hardness
and all kernel checks remain open. No execution or biological-model change.
-/

end PolytomyReductionModel
