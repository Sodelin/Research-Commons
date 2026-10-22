/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/certificate.

Consumption bounds for EVERY successfully parsed source string, including
noncanonical binary payloads. Validation bounds numeric dimensions before
the finite-universe constructor. This is a size proof, not a machine-time
proof or a replacement for the full target/source-hardness interface.
-/
import PolytomySourceBitCodec

namespace PolytomyReductionModel
universe u

theorem readUnaryFrame_sound (bits : List Bool) :
    ∀ n rest, readUnaryFrame bits = some (n, rest) → bits = unaryFrame n ++ rest := by
  induction bits with
  | nil => intro n rest h; simp [readUnaryFrame] at h
  | cons b bits ih =>
      intro n rest h
      cases b with
      | false =>
          simp only [readUnaryFrame, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [unaryFrame]
      | true =>
          cases hp : readUnaryFrame bits with
          | none => simp [readUnaryFrame, hp] at h
          | some pair =>
              obtain ⟨k, after⟩ := pair
              simp only [readUnaryFrame, hp, Option.some.injEq, Prod.mk.injEq] at h
              have hi := ih k after hp
              calc
                true :: bits = true :: (unaryFrame k ++ after) := by rw [hi]
                _ = unaryFrame (k + 1) ++ after := by
                  simp [unaryFrame, List.replicate_succ]
                _ = unaryFrame n ++ rest := by rw [h.1, h.2]

theorem readUnaryFrame_consumption (bits : List Bool) (n : ℕ) (rest : List Bool)
    (h : readUnaryFrame bits = some (n, rest)) :
    n + 1 + rest.length = bits.length := by
  have he := congrArg List.length (readUnaryFrame_sound bits n rest h)
  simpa [unaryFrame, Nat.add_assoc] using he.symm

theorem readBinaryNatFrame_remaining (bits : List Bool) (n : ℕ) (rest : List Bool)
    (h : readBinaryNatFrame bits = some (n, rest)) : rest.length ≤ bits.length := by
  cases hp : readUnaryFrame bits with
  | none => simp [readBinaryNatFrame, hp] at h
  | some pair =>
      obtain ⟨width, tail⟩ := pair
      have hc := readUnaryFrame_consumption bits width tail hp
      by_cases hw : width ≤ tail.length
      · simp only [readBinaryNatFrame, hp, if_pos hw, Option.some.injEq,
          Prod.mk.injEq] at h
        have hr : (tail.drop width).length = rest.length := congrArg List.length h.2
        rw [List.length_drop] at hr
        omega
      · simp [readBinaryNatFrame, hp, hw] at h

theorem readMany_consumption {A : Type u}
    (read : List Bool → Option (A × List Bool)) (weight : A → ℕ)
    (hc : ∀ bits a rest, read bits = some (a, rest) →
      weight a + rest.length ≤ bits.length) (count : ℕ) :
    ∀ bits xs rest, readMany read count bits = some (xs, rest) →
      xs.length = count ∧ (xs.map weight).sum + rest.length ≤ bits.length := by
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
      | some pair =>
          obtain ⟨a, tail⟩ := pair
          cases hq : readMany read count tail with
          | none => simp [readMany, hp, hq] at h
          | some pair =>
              obtain ⟨ys, after⟩ := pair
              simp only [readMany, hp, hq, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hlen, hweight⟩ := ih tail ys after hq
              have ha := hc bits a tail hp
              rw [← h.1, ← h.2]
              simp only [List.length_cons, List.map_cons, List.sum_cons]
              constructor <;> omega

theorem readFramedList_consumption {A : Type u}
    (read : List Bool → Option (A × List Bool)) (weight : A → ℕ)
    (hc : ∀ bits a rest, read bits = some (a, rest) →
      weight a + rest.length ≤ bits.length)
    (bits : List Bool) (xs : List A) (rest : List Bool)
    (h : readFramedList read bits = some (xs, rest)) :
    xs.length + 1 + (xs.map weight).sum + rest.length ≤ bits.length := by
  cases hp : readUnaryFrame bits with
  | none => simp [readFramedList, hp] at h
  | some pair =>
      obtain ⟨count, tail⟩ := pair
      have hu := readUnaryFrame_consumption bits count tail hp
      have hm : readMany read count tail = some (xs, rest) := by
        simpa [readFramedList, hp] using h
      obtain ⟨hlen, hweight⟩ := readMany_consumption read weight hc count tail xs rest hm
      omega

theorem readNatRow_consumption (bits : List Bool) (row : List ℕ) (rest : List Bool)
    (h : readFramedList readBinaryNatFrame bits = some (row, rest)) :
    row.length + 1 + rest.length ≤ bits.length := by
  have hc : ∀ bits n rest, readBinaryNatFrame bits = some (n, rest) →
      (fun _ : ℕ => 0) n + rest.length ≤ bits.length := by
    intro bits n rest hn
    simpa using readBinaryNatFrame_remaining bits n rest hn
  simpa using readFramedList_consumption readBinaryNatFrame (fun _ => 0) hc bits row rest h

theorem flatten_length_le_rowWeight (rows : List (List ℕ)) :
    rows.flatten.length ≤ (rows.map (fun row => row.length + 1)).sum := by
  induction rows with
  | nil => simp
  | cons row rows ih => simp only [List.flatten_cons, List.length_append,
      List.map_cons, List.sum_cons]; omega

theorem readRows_consumption (bits : List Bool) (rows : List (List ℕ)) (rest : List Bool)
    (h : readFramedList (readFramedList readBinaryNatFrame) bits = some (rows, rest)) :
    rows.length + rows.flatten.length + 1 + rest.length ≤ bits.length := by
  have hc := readFramedList_consumption (readFramedList readBinaryNatFrame)
    (fun row => row.length + 1) readNatRow_consumption bits rows rest h
  have hf := flatten_length_le_rowWeight rows
  omega

theorem parseRawMSSCPrefix_consumption (bits : List Bool) (R : RawMSSCRecord)
    (rest : List Bool) (h : parseRawMSSCPrefix bits = some (R, rest)) :
    rawRecordSize R + rest.length ≤ bits.length := by
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
                  have hb1 := readBinaryNatFrame_remaining bits N r1 h1
                  have hb2 := readBinaryNatFrame_remaining r1 m r2 h2
                  have hb3 := readBinaryNatFrame_remaining r2 K r3 h3
                  have hb4 := readRows_consumption r3 rows after h4
                  rw [← h.1, ← h.2]
                  simp only [rawRecordSize]
                  omega

theorem parseRawMSSC_size_bound (bits : List Bool) (R : RawMSSCRecord)
    (h : parseRawMSSC bits = some R) : rawRecordSize R ≤ bits.length := by
  cases hp : parseRawMSSCPrefix bits with
  | none => simp [parseRawMSSC, hp] at h
  | some pair =>
      obtain ⟨Q, rest⟩ := pair
      cases rest with
      | cons b rest => simp [parseRawMSSC, hp] at h
      | nil =>
          have he : Q = R := by simpa [parseRawMSSC, hp] using h
          subst Q
          simpa using parseRawMSSCPrefix_consumption bits R [] hp

/-- Crucially quantified over ALL parsed strings, not only encodeRawMSSC R.
    Noncanonical binary payloads cannot conceal an enormous valid universe. -/
theorem parsed_valid_dimensions_bounded (bits : List Bool) (R : RawMSSCRecord)
    (hp : parseRawMSSC bits = some R) (hv : RawMSSCValid R) :
    R.N ≤ bits.length ∧ R.declaredM ≤ bits.length ∧ R.rows.length ≤ bits.length := by
  have hs := parseRawMSSC_size_bound bits R hp
  obtain ⟨hn, hmBound⟩ := raw_valid_dimensions_bounded R hv
  have hm := hv.1
  unfold rawRecordSize at hs hmBound
  omega

theorem bitCertificateBound_mono {N m N' m' : ℕ} (hN : N ≤ N') (hm : m ≤ m') :
    bitCertificateBound N m ≤ bitCertificateBound N' m' := by
  have hprod : m * N ≤ m' * N' := Nat.mul_le_mul hm hN
  have hs : N + m * N + 3 ≤ N' + m' * N' + 3 := by omega
  have hb : (m + 1) * (N + m * N + 3) ≤ (m' + 1) * (N' + m' * N' + 3) :=
    Nat.mul_le_mul (by omega) hs
  have hp : cellPayloadBound N m + 2 ≤ cellPayloadBound N' m' + 2 := by
    unfold cellPayloadBound
    omega
  exact Nat.mul_le_mul hb hp

def sourceBitCertificateBound (inputLength : ℕ) : ℕ :=
  bitCertificateBound inputLength inputLength

theorem full_parsed_source_bit_reduction (input : List Bool) (R : RawMSSCRecord)
    (hparse : parseRawMSSC input = some R) (h : RawMSSCValid R)
    (hN : 0 < R.N) (hm : 2 ≤ R.rows.length)
    (hNK : R.N ≤ R.K) (hKmN : R.K ≤ R.rows.length * R.N) :
    SourceBitMSSCDecision input ↔
      ∃ cert : List Bool, cert.length ≤ sourceBitCertificateBound input.length ∧
        checkBlockTargetBits (canonicalBlockTarget (rawToMSSC R h) R.K) cert = true := by
  have hsource : SourceBitMSSCDecision input ↔ RawMSSCDecision R := by
    simp [SourceBitMSSCDecision, hparse]
  have hd := parsed_valid_dimensions_bounded input R hparse h
  have hb : bitCertificateBound R.N R.rows.length ≤ sourceBitCertificateBound input.length :=
    bitCertificateBound_mono hd.1 hd.2.2
  constructor
  · intro hs
    obtain ⟨cert, hc, hcheck⟩ := (full_rawMSSC_bit_reduction R h hN hm hNK hKmN).mp
      (hsource.mp hs)
    exact ⟨cert, hc.trans hb, hcheck⟩
  · rintro ⟨cert, hc, hcheck⟩
    have ht := checkCanonicalBits_sound (rawToMSSC R h) R.K cert hcheck
    have hmssc := (full_mssc_checked_tree_reduction (rawToMSSC R h) R.K
      hN hm hNK hKmN).mpr ht
    exact hsource.mpr ((rawMSSCDecision_valid_iff R h).mpr hmssc)

/- The size bound is a degree-five polynomial, but there is still NO
certified total polynomial constructor/verifier machine, target-instance bit
codec, formal source hardness or elaboration. The later TotalSourceReduction
companion proposes the missing total FINITE boundary-case mapping.
These terms preserve the full reduction and expose, rather than assume,
those remaining whole-claim dependencies. -/

end PolytomyReductionModel
