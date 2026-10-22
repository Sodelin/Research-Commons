/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/certificate.

All-string target-parser consumption and validated numerical dimension
bounds. These are finite size terms, not a polynomial machine realization.
-/
import PolytomyTargetBitCodec

namespace PolytomyReductionModel
noncomputable section

theorem readCellBits_consumption (N m : ℕ) (bits : List Bool)
    (a : Cell N m) (rest : List Bool) (h : readCellBits N m bits = some (a, rest)) :
    2 + rest.length ≤ bits.length := by
  cases h1 : readUnaryFrame bits with
  | none => simp [readCellBits, h1] at h
  | some pair =>
      obtain ⟨b, r1⟩ := pair
      cases h2 : readUnaryFrame r1 with
      | none => simp [readCellBits, h1, h2] at h
      | some pair =>
          obtain ⟨s, r2⟩ := pair
          cases hb : decodeBlock m b with
          | none => simp [readCellBits, h1, h2, hb] at h
          | some bi =>
              cases hs : decodeTerminal N m s with
              | none => simp [readCellBits, h1, h2, hb, hs] at h
              | some si =>
                  simp only [readCellBits, h1, h2, hb, hs, Option.some.injEq,
                    Prod.mk.injEq] at h
                  have hrest : r2 = rest := h.2
                  have hc1 := readUnaryFrame_consumption bits b r1 h1
                  have hc2 := readUnaryFrame_consumption r1 s r2 h2
                  rw [hrest] at hc2
                  omega

theorem parseBitPrefix_consumption (N m fuel : ℕ) :
    ∀ bits (T : BTree (Cell N m)) rest,
      parseBitPrefix N m fuel bits = some (T, rest) →
      vertexCount T + rest.length ≤ bits.length := by
  induction fuel with
  | zero => intro bits T rest h; simp [parseBitPrefix] at h
  | succ fuel ih =>
      intro bits T rest h
      cases bits with
      | nil => simp [parseBitPrefix] at h
      | cons b bits =>
          cases b with
          | true =>
              cases hp : readCellBits N m bits with
              | none => simp [parseBitPrefix, hp] at h
              | some pair =>
                  obtain ⟨a, after⟩ := pair
                  simp only [parseBitPrefix, hp, Option.some.injEq, Prod.mk.injEq] at h
                  have hc := readCellBits_consumption N m bits a after hp
                  rw [← h.1, ← h.2]
                  simp only [vertexCount, List.length_cons]
                  omega
          | false =>
              cases hl : parseBitPrefix N m fuel bits with
              | none => simp [parseBitPrefix, hl] at h
              | some pair =>
                  obtain ⟨l, afterLeft⟩ := pair
                  cases hr : parseBitPrefix N m fuel afterLeft with
                  | none => simp [parseBitPrefix, hl, hr] at h
                  | some pair =>
                      obtain ⟨r, afterRight⟩ := pair
                      simp only [parseBitPrefix, hl, hr, Option.some.injEq, Prod.mk.injEq] at h
                      have hcl := ih bits l afterLeft hl
                      have hcr := ih afterLeft r afterRight hr
                      rw [← h.1, ← h.2]
                      simp only [vertexCount, List.length_cons]
                      omega

theorem readTargetTree_consumption (N m : ℕ) (bits : List Bool)
    (T : BTree (Cell N m)) (rest : List Bool)
    (h : readTargetTree N m bits = some (T, rest)) :
    vertexCount T + rest.length ≤ bits.length :=
  parseBitPrefix_consumption N m bits.length bits T rest h

theorem leaves_length_le_vertices {A : Type*} (T : BTree A) :
    (leaves T).length ≤ vertexCount T := by
  induction T with
  | leaf a => simp [leaves, vertexCount]
  | node l r ihl ihr => simp only [leaves, List.length_append, vertexCount]; omega

theorem forest_leaves_le_vertices {A : Type*} (rows : List (BTree A)) :
    (rows.flatMap leaves).length ≤ (rows.map vertexCount).sum := by
  induction rows with
  | nil => simp
  | cons T rows ih =>
      have h := leaves_length_le_vertices T
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
      omega

def rawAnyTargetSize (R : AnyRawTargetRows) : ℕ :=
  R.2.2.rows.length + (rawTargetLeaves R.2.2).length + 1

theorem parseRawTargetPrefix_consumption (bits : List Bool) (R : AnyRawTargetRows)
    (rest : List Bool) (h : parseRawTargetPrefix bits = some (R, rest)) :
    rawAnyTargetSize R + rest.length ≤ bits.length := by
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
                  simp only [parseRawTargetPrefix, h1, h2, h3, h4, Option.some.injEq,
                    Prod.mk.injEq] at h
                  have hb1 := readBinaryNatFrame_remaining bits N r1 h1
                  have hb2 := readBinaryNatFrame_remaining r1 m r2 h2
                  have hb3 := readBinaryNatFrame_remaining r2 budget r3 h3
                  have hb4 := readFramedList_consumption (readTargetTree N m) vertexCount
                    (readTargetTree_consumption N m) r3 rows after h4
                  have hleaves := forest_leaves_le_vertices rows
                  rw [← h.1, ← h.2]
                  simp only [rawAnyTargetSize, rawTargetLeaves]
                  omega

theorem parseRawTarget_size_bound (bits : List Bool) (R : AnyRawTargetRows)
    (h : parseRawTarget bits = some R) : rawAnyTargetSize R ≤ bits.length := by
  cases hp : parseRawTargetPrefix bits with
  | none => simp [parseRawTarget, hp] at h
  | some pair =>
      obtain ⟨Q, rest⟩ := pair
      cases rest with
      | cons b rest => simp [parseRawTarget, hp] at h
      | nil =>
          have he : Q = R := by simpa [parseRawTarget, hp] using h
          subst Q
          simpa using parseRawTargetPrefix_consumption bits R [] hp

theorem decodeRawTargetRows_valid_of_success {N m : ℕ} (R : RawTargetRows N m)
    (G : BlockTargetData N m) (h : decodeRawTargetRows R = some G) : RawTargetRowsValid R := by
  unfold decodeRawTargetRows at h
  split_ifs at h with hv
  · exact (rawTargetRowsValidBool_spec R).mp hv
  · cases h

/-- Every successfully decoded target, not just a canonical encoding, has
    its declared terminal universe and block count bounded by input length. -/
theorem decoded_target_dimensions_bounded (bits : List Bool) (G : AnyBlockTarget)
    (h : decodeTargetBits bits = some G) :
    G.1 + G.2.1 * G.1 + 3 ≤ bits.length ∧ G.2.1 < bits.length := by
  cases hp : parseRawTarget bits with
  | none => simp [decodeTargetBits, hp] at h
  | some R =>
      rcases R with ⟨N, m, R⟩
      cases hr : decodeRawTargetRows R with
      | none => simp [decodeTargetBits, hp, hr] at h
      | some Q =>
          have he : (⟨N, m, Q⟩ : AnyBlockTarget) = G := by
            simpa [decodeTargetBits, hp, hr] using h
          have hv := decodeRawTargetRows_valid_of_success R Q hr
          obtain ⟨hs, hm⟩ := raw_target_dimensions_bounded R hv
          have hc := parseRawTarget_size_bound bits ⟨N, m, R⟩ hp
          rw [← he]
          simp only [rawAnyTargetSize] at hc
          simp only
          omega

theorem decoded_refinement_leaf_bound (bits : List Bool) (G : AnyBlockTarget)
    (hd : decodeTargetBits bits = some G) (T : BTree (Cell G.1 G.2.1))
    (hT : StandardBlockRefinement G.2.2.blocks T) : (leaves T).length ≤ bits.length := by
  cases hp : parseRawTarget bits with
  | none => simp [decodeTargetBits, hp] at hd
  | some R =>
      rcases R with ⟨N, m, R⟩
      cases hr : decodeRawTargetRows R with
      | none => simp [decodeTargetBits, hp, hr] at hd
      | some Q =>
          have he : (⟨N, m, Q⟩ : AnyBlockTarget) = G := by
            simpa [decodeTargetBits, hp, hr] using hd
          subst G
          have hv := decodeRawTargetRows_valid_of_success R Q hr
          have hQ : rawRowsToTarget R hv = Q := by
            rw [decodeRawTargetRows_valid R hv] at hr
            exact Option.some.inj hr
          rw [← hQ] at hT
          have hl := raw_target_refinement_leaf_bound R hv T hT
          have hs := parseRawTarget_size_bound bits ⟨N, m, R⟩ hp
          simp only [rawAnyTargetSize] at hs
          omega

def targetBitCertificateBound (inputLength : ℕ) : ℕ := inputLength * (2 * inputLength + 3)

theorem decoded_refinement_bit_bound (bits : List Bool) (G : AnyBlockTarget)
    (hd : decodeTargetBits bits = some G) (T : BTree (Cell G.1 G.2.1))
    (hT : StandardBlockRefinement G.2.2.blocks T) :
    (treeBits T).length ≤ targetBitCertificateBound bits.length := by
  obtain ⟨hs, hm⟩ := decoded_target_dimensions_bounded bits G hd
  have hl := decoded_refinement_leaf_bound bits G hd T hT
  have hp : cellPayloadBound G.1 G.2.1 ≤ 2 * bits.length + 1 := by
    unfold cellPayloadBound
    omega
  have hprod := Nat.mul_le_mul hl hp
  have hv := vertexCount_add_one T
  have hb := treeBits_length_le T
  unfold targetBitCertificateBound
  nlinarith

/-- Polynomial certificate SIZE for every independently validated target
    string. No origin/source witness is required and all lambda are retained. -/
theorem encoded_target_actual_iff_bounded (input : List Bool) (lambda : ℝ) :
    EncodedTargetCartaDecision input lambda ↔
      ∃ cert : List Bool, cert.length ≤ targetBitCertificateBound input.length ∧
        checkEncodedTarget input cert = true := by
  constructor
  · rintro ⟨G, hd, L, hT, hf, hs⟩
    have hdom := decodeTargetBits_marked input G hd
    have hm := marked_refinement_mixed G.2.2 hdom (eraseStar L) hT
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm] at hs
    have hc : checkBlockTarget G.2.2 (eraseStar L) = true :=
      (checkBlockTarget_spec G.2.2 _).mpr ⟨hT, by exact_mod_cast hs⟩
    refine ⟨treeBits (eraseStar L), decoded_refinement_bit_bound input G hd _ hT, ?_⟩
    simpa [checkEncodedTarget, hd, checkBlockTargetBits, parseBitTree_encode] using hc
  · rintro ⟨cert, hlen, hc⟩
    exact (encoded_target_actual_iff_checked input lambda).mpr ⟨cert, hc⟩

theorem full_encoded_source_bounded_reduction (input : List Bool) :
    SourceBitMSSCDecision input ↔
      ∃ cert : List Bool,
        cert.length ≤ targetBitCertificateBound (encodedSourceToTarget input).length ∧
        checkEncodedTarget (encodedSourceToTarget input) cert = true := by
  exact (full_encoded_source_actual_reduction input 0).trans
    (encoded_target_actual_iff_bounded (encodedSourceToTarget input) 0)

/- A polynomial machine implementation, encoded OUTPUT-length theorem and
formal source hardness still require their own connections. The certificate
SIZE theorem and successful parsing are not time-complexity certificates.
All source and dependencies remain unelaborated. -/

end
end PolytomyReductionModel
