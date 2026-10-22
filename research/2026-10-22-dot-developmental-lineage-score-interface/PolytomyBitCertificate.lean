/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/certificate.

Fixed Boolean-alphabet certificate serialization, bounded cell decoding,
total tree parsing and composition with the full Carta refinement endpoint.
Unary payloads are deliberate: all VALID explicit source dimensions and
constructed cell codes are polynomially bounded. This is not a polynomial
machine proof, and it does not parse/validate the source instance itself.
-/
import PolytomyCertificateChecker

namespace PolytomyReductionModel

def blockCode {m : ℕ} : Block m → ℕ
  | none => 0
  | some i => i.val + 1

def decodeBlock (m : ℕ) (n : ℕ) : Option (Block m) :=
  if hn : n = 0 then some none
  else if hi : n - 1 < m then some (some ⟨n - 1, hi⟩) else none

theorem decodeBlock_code {m : ℕ} (b : Block m) :
    decodeBlock m (blockCode b) = some b := by
  cases b with
  | none => simp [blockCode, decodeBlock]
  | some i => simp [blockCode, decodeBlock, i.isLt]

def decodeTerminal (N m n : ℕ) : Option (Terminal N m) :=
  if hx : n < N then some (.inl ⟨n, hx⟩)
  else if hz : n - N < privateCount N m then some (.inr (.inl ⟨n - N, hz⟩))
  else if hk : n - N - privateCount N m < 2 then
    some (.inr (.inr ⟨n - N - privateCount N m, hk⟩))
  else none

theorem decodeTerminal_code (N m : ℕ) (s : Terminal N m) :
    decodeTerminal N m (terminalCode N m s) = some s := by
  rcases s with x | (z | k)
  · simp [terminalCode, decodeTerminal, x.isLt]
  · have hx : ¬ N + z.val < N := by omega
    simp [terminalCode, decodeTerminal, hx, z.isLt]
  · have hx : ¬ N + privateCount N m + k.val < N := by omega
    have hz : ¬ (N + privateCount N m + k.val) - N < privateCount N m := by omega
    have hk : (N + privateCount N m + k.val) - N - privateCount N m = k.val := by omega
    simp [terminalCode, decodeTerminal, hx, hz, hk, k.isLt]

def unaryFrame (n : ℕ) : List Bool := List.replicate n true ++ [false]

def readUnaryFrame : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
      match readUnaryFrame rest with
      | none => none
      | some (n, after) => some (n + 1, after)

theorem readUnaryFrame_encode (n : ℕ) (rest : List Bool) :
    readUnaryFrame (unaryFrame n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [unaryFrame, readUnaryFrame]
  | succ n ih =>
      simp only [unaryFrame, List.replicate_succ, List.cons_append]
      change (match readUnaryFrame (unaryFrame n ++ rest) with
        | none => none | some (k, after) => some (k + 1, after)) = _
      rw [ih]

def cellBits {N m : ℕ} (a : Cell N m) : List Bool :=
  unaryFrame (blockCode a.1) ++ unaryFrame (terminalCode N m a.2)

def readCellBits (N m : ℕ) (bits : List Bool) : Option (Cell N m × List Bool) :=
  match readUnaryFrame bits with
  | none => none
  | some (b, afterBlock) =>
      match readUnaryFrame afterBlock with
      | none => none
      | some (s, afterType) =>
          match decodeBlock m b, decodeTerminal N m s with
          | some bi, some si => some ((bi, si), afterType)
          | _, _ => none

theorem readCellBits_encode {N m : ℕ} (a : Cell N m) (rest : List Bool) :
    readCellBits N m (cellBits a ++ rest) = some (a, rest) := by
  simp only [cellBits, List.append_assoc, readCellBits, readUnaryFrame_encode,
    decodeBlock_code, decodeTerminal_code]

def treeBits {N m : ℕ} : BTree (Cell N m) → List Bool
  | .leaf a => true :: cellBits a
  | .node l r => false :: (treeBits l ++ treeBits r)

def parseBitPrefix (N m : ℕ) : ℕ → List Bool → Option (BTree (Cell N m) × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, true :: rest =>
      match readCellBits N m rest with
      | none => none
      | some (a, after) => some (.leaf a, after)
  | fuel + 1, false :: rest =>
      match parseBitPrefix N m fuel rest with
      | none => none
      | some (l, afterLeft) =>
          match parseBitPrefix N m fuel afterLeft with
          | none => none
          | some (r, afterRight) => some (.node l r, afterRight)

theorem vertexCount_le_treeBits_length {N m : ℕ} (T : BTree (Cell N m)) :
    vertexCount T ≤ (treeBits T).length := by
  induction T with
  | leaf a => simp [vertexCount, treeBits]
  | node l r ihl ihr => simp only [vertexCount, treeBits, List.length_cons,
      List.length_append]; omega

theorem parseBitPrefix_encode {N m : ℕ} (T : BTree (Cell N m)) :
    ∀ (fuel : ℕ) (rest : List Bool), vertexCount T ≤ fuel →
      parseBitPrefix N m fuel (treeBits T ++ rest) = some (T, rest) := by
  induction T with
  | leaf a =>
      intro fuel rest hf
      cases fuel with
      | zero => simp [vertexCount] at hf
      | succ fuel => simp [treeBits, parseBitPrefix, readCellBits_encode]
  | node l r ihl ihr =>
      intro fuel rest hf
      cases fuel with
      | zero => simp [vertexCount] at hf
      | succ fuel =>
          have hl : vertexCount l ≤ fuel := by simp only [vertexCount] at hf; omega
          have hr : vertexCount r ≤ fuel := by simp only [vertexCount] at hf; omega
          simp only [treeBits, List.cons_append, List.append_assoc, parseBitPrefix]
          rw [ihl fuel (treeBits r ++ rest) hl, ihr fuel rest hr]

def parseBitTree (N m : ℕ) (bits : List Bool) : Option (BTree (Cell N m)) :=
  match parseBitPrefix N m bits.length bits with
  | some (T, []) => some T
  | _ => none

theorem parseBitTree_encode {N m : ℕ} (T : BTree (Cell N m)) :
    parseBitTree N m (treeBits T) = some T := by
  have hp := parseBitPrefix_encode T (treeBits T).length [] (vertexCount_le_treeBits_length T)
  simp only [List.append_nil] at hp
  simp [parseBitTree, hp]

noncomputable def checkBlockTargetBits {N m : ℕ} (G : BlockTargetData N m)
    (bits : List Bool) : Bool :=
  match parseBitTree N m bits with
  | none => false
  | some T => checkBlockTarget G T

noncomputable def checkCanonicalBits {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (bits : List Bool) : Bool := checkBlockTargetBits (canonicalBlockTarget D K) bits

theorem checkBlockTargetBits_spec {N m : ℕ} (G : BlockTargetData N m)
    (bits : List Bool) : checkBlockTargetBits G bits = true ↔
      ∃ T : BTree (Cell N m), parseBitTree N m bits = some T ∧
        StandardBlockRefinement G.blocks T ∧ starScore Finset.univ Prod.snd T ≤ G.budget := by
  constructor
  · intro h
    cases hp : parseBitTree N m bits with
    | none => simp [checkBlockTargetBits, hp] at h
    | some T =>
        have hc : checkBlockTarget G T = true := by
          simpa [checkBlockTargetBits, hp] using h
        exact ⟨T, hp, (checkBlockTarget_spec G T).mp hc⟩
  · rintro ⟨T, hp, hT⟩
    have hc := (checkBlockTarget_spec G T).mpr hT
    simpa [checkBlockTargetBits, hp] using hc

/-- Soundness applies to EVERY Boolean certificate, not just encoded valid
    trees. Successful parsing supplies the independently checked typed tree. -/
theorem checkCanonicalBits_sound {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (bits : List Bool) (h : checkCanonicalBits D K bits = true) :
    ∃ T : BTree (Cell N m), checkCanonicalTree D K T = true := by
  cases hp : parseBitTree N m bits with
  | none => simp [checkCanonicalBits, checkBlockTargetBits, hp] at h
  | some T => exact ⟨T, by simpa [checkCanonicalBits, checkBlockTargetBits,
      checkCanonicalTree, hp] using h⟩

theorem checkCanonicalBits_complete {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (T : BTree (Cell N m)) (h : checkCanonicalTree D K T = true) :
    checkCanonicalBits D K (treeBits T) = true := by
  simpa [checkCanonicalBits, checkBlockTargetBits, checkCanonicalTree,
    parseBitTree_encode] using h

def cellPayloadBound (N m : ℕ) : ℕ := m + (N + m * N + 3) + 1

theorem cellBits_length_le {N m : ℕ} (a : Cell N m) :
    (cellBits a).length ≤ cellPayloadBound N m := by
  have hb : blockCode a.1 ≤ m := by
    cases hblock : a.1 with
    | none => simp [hblock, blockCode]
    | some i =>
        have hi := i.isLt
        simp only [hblock, blockCode]
        omega
  have hs := terminalCode_lt N m a.2
  simp only [cellBits, unaryFrame, List.length_append, List.length_replicate,
    List.length_singleton, cellPayloadBound]
  omega

theorem treeBits_length_le {N m : ℕ} (T : BTree (Cell N m)) :
    (treeBits T).length ≤ vertexCount T + (leaves T).length * cellPayloadBound N m := by
  induction T with
  | leaf a => simpa [treeBits, vertexCount, leaves, Nat.add_comm] using
      Nat.add_le_add_left (cellBits_length_le a) 1
  | node l r ihl ihr =>
      simp only [treeBits, List.length_cons, List.length_append, vertexCount, leaves]
      nlinarith

def bitCertificateBound (N m : ℕ) : ℕ :=
  ((m + 1) * (N + m * N + 3)) * (cellPayloadBound N m + 2)

theorem checked_tree_bitLength_bound {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (T : BTree (Cell N m)) (h : checkCanonicalTree D K T = true) :
    (treeBits T).length ≤ bitCertificateBound N m := by
  have hl := checked_tree_leaf_bound D K T h
  have he := vertexCount_add_one T
  have hb := treeBits_length_le T
  have hm := Nat.mul_le_mul_right (cellPayloadBound N m) hl
  unfold bitCertificateBound
  nlinarith

/-- All real lambda choices have the same bounded Boolean certificate
    language on this gadget; the compatible-label quantifier is preserved. -/
theorem standardCanonicalCartaDecision_iff_bounded_bits {N m : ℕ}
    (D : MSSCInstance N m) (lambda : ℝ) (K : ℕ) :
    StandardCanonicalCartaDecision D lambda K ↔
      ∃ bits : List Bool, bits.length ≤ bitCertificateBound N m ∧
        checkCanonicalBits D K bits = true := by
  rw [standardCanonicalCartaDecision_iff_checked_tree]
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨treeBits T, checked_tree_bitLength_bound D K T hT,
      checkCanonicalBits_complete D K T hT⟩
  · rintro ⟨bits, hlen, hbits⟩
    exact checkCanonicalBits_sound D K bits hbits

/-- FULL finite proof chain from X3C through arbitrary standard refinements
    and actual D_lambda to a fixed Boolean-alphabet bounded certificate. -/
theorem full_mssc_bit_reduction {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (hN : 0 < N) (hm : 2 ≤ m) (hNK : N ≤ K) (hKmN : K ≤ m * N) :
    MSSCDecision D K ↔
      ∃ bits : List Bool, bits.length ≤ bitCertificateBound N m ∧
        checkCanonicalBits D K bits = true := by
  exact (full_standard_canonical_carta_reduction D 0 K hN hm hNK hKmN).trans
    (standardCanonicalCartaDecision_iff_bounded_bits D 0 K)

/-- The upstream exact-cover equivalence composes with the same full target,
    not with a restricted topology or an ordering-only certificate. -/
theorem full_exactTripleCover_bit_reduction {q m : ℕ}
    (D : TripleCoverInstance q m) (hq : 0 < q) (hm : 2 ≤ m) :
    ExactTripleCoverDecision D ↔
      ∃ bits : List Bool, bits.length ≤ bitCertificateBound (3 * q) m ∧
        checkCanonicalBits D.toMSSCInstance (tripleThreshold q m) bits = true := by
  exact (full_exactTripleCover_carta_reduction D 0 hq hm).trans
    (standardCanonicalCartaDecision_iff_bounded_bits D.toMSSCInstance 0
      (tripleThreshold q m))

/- The bound is polynomial in N,m and hence in VALID explicit source input
length after the validation argument. No encoded constructor/verifier machine,
source-instance parser, formal X3C-hardness theorem or elaboration is supplied. -/

end PolytomyReductionModel
