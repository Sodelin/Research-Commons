/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

WORK IN PROGRESS toward the ONE ORIGINAL bounded-pair verifier controller.
Its final decision language is the RESTRICTED encoded marked-star language:
independently supplied targets satisfying the explicit dimensions, marker,
mixedness, uniqueness and coverage guards, with the actual D_lambda score.
Even all-word completeness for that language would NOT verify arbitrary
differentiation-DAG/Carta inputs. Names such as full_carta do not broaden
the domain established by the definitions and guards.
This file supplies its composed original forest grammar/range PHASE,
not the full controller or VerifierMachineWitness. The target forest
has ONE unary count and concatenated self-delimiting binary trees. There
is no length frame per tree and no enclosing-row/block-tag restriction.

The range cursor, original unframed certificate adapter, and target count/
whole-word joins are emitted below. The full headers/guards/clades/score/
final cleanup remain to be composed. No
unspecified routine or machine is assumed to exist.
-/
import PolytomyIndexedLeafCellQuery
import PolytomyIndexedSubtreeQuery
import PolytomySaturatedVerifier
import PolytomyFramedRowsParser
import PolytomyOwnedStackCleanup

namespace PolytomyReductionModel.WholeVerifierController

/- Only the generic readMany_length_exact theorem is reused from the
source rows module. Its NUMERIC row parser is not a target forest parser. -/

def decodeRawCell (N m : ℕ) (c : ℕ × ℕ) : Option (Cell N m) :=
  (decodeBlock m c.1).bind (fun b => (decodeTerminal N m c.2).map (fun t => (b, t)))

def rawCellValid (N m : ℕ) (c : ℕ × ℕ) : Prop := c.1 ≤ m ∧ c.2 < N + m * N + 3

theorem decodeRawCell_isSome (N m : ℕ) (c : ℕ × ℕ) :
    (decodeRawCell N m c).isSome = true ↔ rawCellValid N m c := by
  unfold rawCellValid
  rw [← decodeBlock_isSome_iff, ← decodeTerminal_isSome_iff]
  cases hb : decodeBlock m c.1 <;> cases ht : decodeTerminal N m c.2 <;>
    simp [decodeRawCell, hb, ht]

theorem decodeRawCell_code {N m : ℕ} (a : Cell N m) :
    decodeRawCell N m (cellNatCode a) = some a := by
  simp [decodeRawCell, cellNatCode, decodeBlock_code, decodeTerminal_code]

theorem decodeRawCell_sound {N m : ℕ} (c : ℕ × ℕ) (a : Cell N m)
    (h : decodeRawCell N m c = some a) : cellNatCode a = c := by
  cases hb : decodeBlock m c.1 with
  | none => simp [decodeRawCell, hb] at h
  | some b =>
      cases ht : decodeTerminal N m c.2 with
      | none => simp [decodeRawCell, hb, ht] at h
      | some t =>
          have ha : (b, t) = a := by simpa [decodeRawCell, hb, ht] using h
          rw [← ha]
          exact Prod.ext (blockCode_of_decode hb) (terminalCode_of_decode ht)

def decodeRawTree (N m : ℕ) : BTree (ℕ × ℕ) → Option (BTree (Cell N m))
  | .leaf c => (decodeRawCell N m c).map BTree.leaf
  | .node l r => (decodeRawTree N m l).bind (fun L =>
      (decodeRawTree N m r).map (fun R => BTree.node L R))

def rawTreeValid (N m : ℕ) (R : BTree (ℕ × ℕ)) : Prop :=
  ∀ c ∈ scanLeaves R, rawCellValid N m c

theorem decodeRawTree_code {N m : ℕ} (T : BTree (Cell N m)) :
    decodeRawTree N m (rawTreeCodes T) = some T := by
  induction T with
  | leaf a => simpa [decodeRawTree, rawTreeCodes, cellNatCode] using
      congrArg (Option.map BTree.leaf) (decodeRawCell_code a)
  | node l r ihl ihr => simp [decodeRawTree, rawTreeCodes, ihl, ihr]

theorem decodeRawTree_sound (N m : ℕ) (R : BTree (ℕ × ℕ)) :
    ∀ T, decodeRawTree N m R = some T → rawTreeCodes T = R := by
  induction R with
  | leaf c =>
      intro T h
      cases hc : decodeRawCell N m c with
      | none => simp [decodeRawTree, hc] at h
      | some a =>
          have he : BTree.leaf a = T := by simpa [decodeRawTree, hc] using h
          rw [← he]
          change BTree.leaf (cellNatCode a) = BTree.leaf c
          rw [decodeRawCell_sound c a hc]
  | node l r ihl ihr =>
      intro T h
      cases hl : decodeRawTree N m l with
      | none => simp [decodeRawTree, hl] at h
      | some L =>
          cases hr : decodeRawTree N m r with
          | none => simp [decodeRawTree, hl, hr] at h
          | some R =>
              have he : BTree.node L R = T := by simpa [decodeRawTree, hl, hr] using h
              rw [← he]
              simp only [rawTreeCodes, ihl L hl, ihr R hr]

theorem decodeRawTree_exists (N m : ℕ) (R : BTree (ℕ × ℕ)) (hv : rawTreeValid N m R) :
    ∃ T, decodeRawTree N m R = some T := by
  revert hv
  induction R with
  | leaf c =>
      intro hv
      have hc : rawCellValid N m c := hv c (by simp [scanLeaves])
      have hs := (decodeRawCell_isSome N m c).mpr hc
      cases hp : decodeRawCell N m c with
      | none => simp [hp] at hs
      | some a => exact ⟨.leaf a, by simp [decodeRawTree, hp]⟩
  | node l r ihl ihr =>
      intro hv
      have hl : rawTreeValid N m l := by
        intro c hc
        exact hv c (by simp [scanLeaves, hc])
      have hr : rawTreeValid N m r := by
        intro c hc
        exact hv c (by simp [scanLeaves, hc])
      obtain ⟨L, hL⟩ := ihl hl
      obtain ⟨R, hR⟩ := ihr hr
      exact ⟨.node L R, by simp [decodeRawTree, hL, hR]⟩

theorem rawTreeCodes_valid {N m : ℕ} (T : BTree (Cell N m)) :
    rawTreeValid N m (rawTreeCodes T) := by
  induction T with
  | leaf a =>
      intro c hc
      have he : c = cellNatCode a := by simpa [scanLeaves, rawTreeCodes, cellNatCode] using hc
      subst c
      apply (decodeRawCell_isSome N m (cellNatCode a)).mp
      rw [decodeRawCell_code]
      rfl
  | node l r ihl ihr =>
      intro c hc
      have hm : c ∈ scanLeaves (rawTreeCodes l) ∨ c ∈ scanLeaves (rawTreeCodes r) := by
        simpa [rawTreeCodes, scanLeaves] using hc
      exact hm.elim (ihl c) (ihr c)

theorem rawTreeValid_iff_typed (N m : ℕ) (R : BTree (ℕ × ℕ)) :
    rawTreeValid N m R ↔ ∃ T : BTree (Cell N m), rawTreeCodes T = R := by
  constructor
  · intro hv
    obtain ⟨T, hT⟩ := decodeRawTree_exists N m R hv
    exact ⟨T, decodeRawTree_sound N m R T hT⟩
  · rintro ⟨T, rfl⟩
    exact rawTreeCodes_valid T

theorem rawForestWord_map_codes {N m : ℕ} (Ts : List (BTree (Cell N m))) :
    rawForestWord (Ts.map rawTreeCodes) = Ts.flatMap treeBits := by
  induction Ts with
  | nil => rfl
  | cons T Ts ih =>
      change rawCellTreeBits (rawTreeCodes T) ++ rawForestWord (Ts.map rawTreeCodes) =
        treeBits T ++ Ts.flatMap treeBits
      rw [rawTreeCodes_bits, ih]

theorem rawForestValid_iff_typed (N m : ℕ) (Rs : List (BTree (ℕ × ℕ))) :
    (∀ R ∈ Rs, rawTreeValid N m R) ↔
      ∃ Ts : List (BTree (Cell N m)), Ts.map rawTreeCodes = Rs := by
  constructor
  · intro h
    revert h
    induction Rs with
    | nil => intro h; exact ⟨[], rfl⟩
    | cons R Rs ih =>
        intro h
        obtain ⟨T, hT⟩ := (rawTreeValid_iff_typed N m R).mp (h R (by simp))
        obtain ⟨Ts, hTs⟩ := ih (fun U hU => h U (by simp [hU]))
        exact ⟨T :: Ts, by simp [hT, hTs]⟩
  · rintro ⟨Ts, rfl⟩ R hR
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hR
    exact rawTreeCodes_valid T

/-- Byte-EXACT soundness, stronger than merely bounding consumption. -/
theorem cellPrefix_sound (N m : ℕ) (bits : List Bool) (a : Cell N m) (rest : List Bool)
    (h : readCellBits N m bits = some (a, rest)) : bits = cellBits a ++ rest := by
  cases h1 : readUnaryFrame bits with
  | none => simp [readCellBits, h1] at h
  | some p1 =>
      rcases p1 with ⟨B, r1⟩
      cases h2 : readUnaryFrame r1 with
      | none => simp [readCellBits, h1, h2] at h
      | some p2 =>
          rcases p2 with ⟨T, r2⟩
          cases hb : decodeBlock m B with
          | none => simp [readCellBits, h1, h2, hb] at h
          | some b =>
              cases ht : decodeTerminal N m T with
              | none => simp [readCellBits, h1, h2, hb, ht] at h
              | some t =>
                  have hp : ((b, t), r2) = (a, rest) :=
                    Option.some.inj (by simpa only [readCellBits, h1, h2, hb, ht] using h)
                  have ha : (b, t) = a := congrArg Prod.fst hp
                  have hr : r2 = rest := congrArg Prod.snd hp
                  rw [← ha, ← hr]
                  rw [readUnaryFrame_decomposition bits B r1 h1,
                    readUnaryFrame_decomposition r1 T r2 h2]
                  simp only [cellBits, blockCode_of_decode hb, terminalCode_of_decode ht, List.append_assoc]

theorem typedPrefix_sound (N m fuel : ℕ) :
    ∀ bits (T : BTree (Cell N m)) rest,
      parseBitPrefix N m fuel bits = some (T, rest) → bits = treeBits T ++ rest := by
  induction fuel with
  | zero => intro bits T rest h; simp [parseBitPrefix] at h
  | succ fuel ih =>
      intro bits T rest h
      cases bits with
      | nil => simp [parseBitPrefix] at h
      | cons tag bits =>
          cases tag with
          | true =>
              cases hp : readCellBits N m bits with
              | none => simp [parseBitPrefix, hp] at h
              | some pair =>
                  rcases pair with ⟨a, after⟩
                  simp only [parseBitPrefix, hp, Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  rw [cellPrefix_sound N m bits a after hp]
                  rfl
          | false =>
              cases hl : parseBitPrefix N m fuel bits with
              | none => simp [parseBitPrefix, hl] at h
              | some pair =>
                  rcases pair with ⟨l, afterLeft⟩
                  cases hr : parseBitPrefix N m fuel afterLeft with
                  | none => simp [parseBitPrefix, hl, hr] at h
                  | some pair =>
                      rcases pair with ⟨r, afterRight⟩
                      simp only [parseBitPrefix, hl, hr, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      rw [ih bits l afterLeft hl, ih afterLeft r afterRight hr]
                      simp only [treeBits, List.cons_append, List.append_assoc]

theorem targetTreePrefix_iff (N m : ℕ) (bits : List Bool) (T : BTree (Cell N m)) (rest : List Bool) :
    readTargetTree N m bits = some (T, rest) ↔ bits = treeBits T ++ rest := by
  constructor
  · exact typedPrefix_sound N m bits.length bits T rest
  · intro h
    rw [h]
    exact readTargetTree_encode T rest

theorem manyPrefix_sound {A : Type} (encode : A → List Bool)
    (read : List Bool → Option (A × List Bool))
    (hs : ∀ bits a rest, read bits = some (a, rest) → bits = encode a ++ rest)
    (q : ℕ) : ∀ bits values rest, readMany read q bits = some (values, rest) →
      bits = values.flatMap encode ++ rest := by
  induction q with
  | zero =>
      intro bits values rest h
      simp only [readMany, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | succ q ih =>
      intro bits values rest h
      cases hp : read bits with
      | none => simp [readMany, hp] at h
      | some pair =>
          rcases pair with ⟨a, tail⟩
          cases hq : readMany read q tail with
          | none => simp [readMany, hp, hq] at h
          | some pair =>
              rcases pair with ⟨xs, after⟩
              simp only [readMany, hp, hq, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              rw [hs bits a tail hp, ih tail xs after hq]
              simp only [List.flatMap_cons, List.append_assoc]

/-- EXACT original target forest framing: one count, then raw tree bytes.
    This does not introduce a length header on each tree. -/
theorem typedForestPrefix_iff (N m : ℕ) (bits rest : List Bool) (Ts : List (BTree (Cell N m))) :
    readFramedList (readTargetTree N m) bits = some (Ts, rest) ↔
      bits = encodeFramedList treeBits Ts ++ rest := by
  constructor
  · intro h
    cases hu : readUnaryFrame bits with
    | none => simp [readFramedList, hu] at h
    | some pair =>
        rcases pair with ⟨q, tail⟩
        have hm : readMany (readTargetTree N m) q tail = some (Ts, rest) := by
          simpa [readFramedList, hu] using h
        have hlen := readMany_length_exact (readTargetTree N m) q tail Ts rest hm
        have htail := manyPrefix_sound treeBits (readTargetTree N m)
          (fun bs T rs hp => (targetTreePrefix_iff N m bs T rs).mp hp) q tail Ts rest hm
        rw [readUnaryFrame_decomposition bits q tail hu, htail]
        simp only [encodeFramedList, hlen, List.append_assoc]
  · intro h
    rw [h]
    exact readFramedList_encode treeBits (readTargetTree N m) readTargetTree_encode Ts rest

/-- Global raw-to-typed converse for the ORIGINAL forest, with both
    directions and arbitrary external suffix. Raw trees are proof-side
    reconstructions, not hidden input promises or machine control values. -/
theorem originalForest_raw_iff (N m : ℕ) (bits rest : List Bool) :
    (∃ Ts : List (BTree (Cell N m)), readFramedList (readTargetTree N m) bits = some (Ts, rest)) ↔
      ∃ Rs : List (BTree (ℕ × ℕ)),
        bits = unaryFrame Rs.length ++ rawForestWord Rs ++ rest ∧
        ∀ R ∈ Rs, rawTreeValid N m R := by
  constructor
  · rintro ⟨Ts, hTs⟩
    refine ⟨Ts.map rawTreeCodes, ?_, ?_⟩
    · have hb := (typedForestPrefix_iff N m bits rest Ts).mp hTs
      simpa only [List.length_map, rawForestWord_map_codes, encodeFramedList, List.append_assoc] using hb
    · exact (rawForestValid_iff_typed N m (Ts.map rawTreeCodes)).mpr ⟨Ts, rfl⟩
  · rintro ⟨Rs, hbits, hvalid⟩
    obtain ⟨Ts, hTs⟩ := (rawForestValid_iff_typed N m Rs).mp hvalid
    refine ⟨Ts, (typedForestPrefix_iff N m bits rest Ts).mpr ?_⟩
    rw [← hTs] at hbits
    simpa only [List.length_map, rawForestWord_map_codes, encodeFramedList, List.append_assoc] using hbits

/-- Physical count + raw forest parser + all finite cell ranges suffices
    for the original typed forest, with EXACT resulting row count. -/
theorem rawForest_to_original (N m q : ℕ) (bits tail rest mask : List Bool)
    (Rs : List (BTree (ℕ × ℕ)))
    (hcount : readUnaryFrame bits = some (q, tail))
    (hraw : rawForestMaskParse tail.length q tail = some (rest, mask))
    (hrows : Rs.length = q) (hword : tail = rawForestWord Rs ++ rest)
    (hvalid : ∀ R ∈ Rs, rawTreeValid N m R) :
    ∃ Ts : List (BTree (Cell N m)), Ts.length = q ∧
      Ts.map rawTreeCodes = Rs ∧ readFramedList (readTargetTree N m) bits = some (Ts, rest) := by
  obtain ⟨Ts, hTs⟩ := (rawForestValid_iff_typed N m Rs).mp hvalid
  have hlen : Ts.length = q := by
    have h := congrArg List.length hTs
    simpa only [List.length_map, hrows] using h
  refine ⟨Ts, hlen, hTs, (typedForestPrefix_iff N m bits rest Ts).mpr ?_⟩
  rw [readUnaryFrame_decomposition bits q tail hcount, hword, ← hTs]
  simp only [rawForestWord_map_codes, encodeFramedList, hlen, List.append_assoc]

/-- A local Boolean observation on a LEGAL node suffix. Internal nodes
pass the cell-range test; genuine leaves run the exact original decoder.
Outside a legal mask, this predicate is not a node-validity oracle. -/
def legalSuffixCellCheck (N m : ℕ) : List Bool → Bool
  | [] => false
  | false :: _ => true
  | true :: bits => (readCellBits N m bits).isSome

def rawNodeRangeValid (N m : ℕ) : BTree (ℕ × ℕ) → Prop
  | .leaf c => rawCellValid N m c
  | .node _ _ => True

theorem legalSuffixCellCheck_view (N m : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool) :
    legalSuffixCellCheck N m (rawCellTreeBits R ++ rest) = true ↔ rawNodeRangeValid N m R := by
  cases R with
  | node l r => simp [rawCellTreeBits, legalSuffixCellCheck, rawNodeRangeValid]
  | leaf c =>
      have he : (readCellBits N m ((unaryFrame c.1 ++ unaryFrame c.2) ++ rest)).isSome =
          (decodeRawCell N m c).isSome := by
        cases hb : decodeBlock m c.1 <;> cases ht : decodeTerminal N m c.2 <;>
          simp [readCellBits, List.append_assoc, readUnaryFrame_encode, decodeRawCell, hb, ht]
      change (readCellBits N m ((unaryFrame c.1 ++ unaryFrame c.2) ++ rest)).isSome = true ↔ _
      rw [he]
      exact decodeRawCell_isSome N m c

theorem rawTreeValid_node (N m : ℕ) (l r : BTree (ℕ × ℕ)) :
    rawTreeValid N m (.node l r) ↔ rawTreeValid N m l ∧ rawTreeValid N m r := by
  simp only [rawTreeValid, scanLeaves, List.mem_append, or_imp, forall_and]

theorem viewCellCheck_iff (N m : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool) :
    (rawNodeViews R rest).all (fun v => legalSuffixCellCheck N m (rawViewSuffix v)) = true ↔
      rawTreeValid N m R := by
  induction R generalizing rest with
  | leaf c =>
      simp only [rawNodeViews, List.all_cons, List.all_nil, Bool.and_true, rawViewSuffix]
      rw [legalSuffixCellCheck_view]
      simp [rawNodeRangeValid, rawTreeValid, scanLeaves]
  | node l r ihl ihr =>
      simp only [rawNodeViews, List.all_cons, List.all_append, Bool.and_eq_true, rawViewSuffix]
      rw [legalSuffixCellCheck_view]
      change (True ∧
        ((rawNodeViews l (rawCellTreeBits r ++ rest)).all
          (fun v => legalSuffixCellCheck N m (rawViewSuffix v)) = true ∧
         (rawNodeViews r rest).all (fun v => legalSuffixCellCheck N m (rawViewSuffix v)) = true)) ↔ _
      rw [ihl, ihr, rawTreeValid_node]
      simp

def forestMaskCellCheck (N m : ℕ) (bits mask : List Bool) : Bool :=
  (rawMarkedSuffixes bits mask).all (legalSuffixCellCheck N m)

theorem forestMaskCellCheck_iff (N m : ℕ) (Rs : List (BTree (ℕ × ℕ))) (rest : List Bool) :
    forestMaskCellCheck N m (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) = true ↔
      ∀ R ∈ Rs, rawTreeValid N m R := by
  induction Rs with
  | nil => simp [forestMaskCellCheck, rawForestWord, rawForestNodeMask, rawMarkedSuffixes]
  | cons R Rs ih =>
      have hsplit : rawMarkedSuffixes (rawForestWord (R :: Rs) ++ rest) (rawForestNodeMask (R :: Rs)) =
          (rawNodeViews R (rawForestWord Rs ++ rest)).map rawViewSuffix ++
            rawMarkedSuffixes (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) := by
        simpa only [rawForestWord, rawForestNodeMask, List.flatMap_cons, List.append_assoc] using
          rawMarkedSuffixes_tree R (rawForestWord Rs ++ rest) (rawForestNodeMask Rs)
      unfold forestMaskCellCheck
      rw [hsplit, List.all_append, Bool.and_eq_true, List.all_map]
      change ((rawNodeViews R (rawForestWord Rs ++ rest)).all
        (fun v => legalSuffixCellCheck N m (rawViewSuffix v)) = true ∧
        forestMaskCellCheck N m (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) = true) ↔ _
      rw [viewCellCheck_iff, ih]
      constructor
      · rintro ⟨hR, hRs⟩ U hU
        rcases List.mem_cons.mp hU with rfl | hU
        · exact hR
        · exact hRs U hU
      · intro h
        exact ⟨h R (by simp), fun U hU => h U (by simp [hU])⟩

/-- Decisive global converse from only the count/parser observations and
the Boolean all-legal-node cell-range scan. No raw-tree witness, source
instance, tree shape, row-origin promise or inferred cell correspondence
is assumed from the caller. All reconstructed trees are obtained here. -/
theorem observedForest_to_original (N m q : ℕ) (bits tail rest mask : List Bool)
    (hcount : readUnaryFrame bits = some (q, tail))
    (hparse : rawForestMaskParse tail.length q tail = some (rest, mask))
    (hcheck : forestMaskCellCheck N m tail mask = true) :
    ∃ Ts : List (BTree (Cell N m)), Ts.length = q ∧
      readFramedList (readTargetTree N m) bits = some (Ts, rest) := by
  obtain ⟨Rs, hrows, hword, hmask⟩ := (rawForestMaskParse_all_words tail rest mask q).mp hparse
  have hv : ∀ R ∈ Rs, rawTreeValid N m R := by
    apply (forestMaskCellCheck_iff N m Rs rest).mp
    simpa only [← hword, ← hmask] using hcheck
  obtain ⟨Ts, hlen, hcodes, htyped⟩ := rawForest_to_original N m q bits tail rest mask Rs
    hcount hparse hrows hword hv
  exact ⟨Ts, hlen, htyped⟩

theorem originalForest_to_observed (N m : ℕ) (bits rest : List Bool) (Ts : List (BTree (Cell N m)))
    (h : readFramedList (readTargetTree N m) bits = some (Ts, rest)) :
    ∃ tail mask, readUnaryFrame bits = some (Ts.length, tail) ∧
      rawForestMaskParse tail.length Ts.length tail = some (rest, mask) ∧
      forestMaskCellCheck N m tail mask = true := by
  have hb := (typedForestPrefix_iff N m bits rest Ts).mp h
  let Rs := Ts.map rawTreeCodes
  let tail := rawForestWord Rs ++ rest
  let mask := rawForestNodeMask Rs
  have hbits : bits = unaryFrame Ts.length ++ tail := by
    simpa only [encodeFramedList, tail, Rs, rawForestWord_map_codes, List.append_assoc] using hb
  have hlen : Rs.length = Ts.length := by simp [Rs]
  refine ⟨tail, mask, ?_, ?_, ?_⟩
  · rw [hbits, readUnaryFrame_encode]
  · apply (rawForestMaskParse_all_words tail rest mask Ts.length).mpr
    exact ⟨Rs, hlen, rfl, rfl⟩
  · apply (forestMaskCellCheck_iff N m Rs rest).mpr
    exact (rawForestValid_iff_typed N m Rs).mpr ⟨Ts, rfl⟩

/- The controller can now establish the ORIGINAL typed forest from its
actual count/mask observations plus the exact local-query all-scan, and
the reverse implication is also present. The later sections provide the
emitted finite cursor/body/cleanup and its operational proof terms. Complete
bounded-pair controller, VerifierMachineWitness and EncodedSourceHardness
are still OPEN. No semantic Boolean loop is claimed to execute for free.
-/

/-! ## Actual ONE-count forest syntax phase of this same controller -/

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

/-- The count is already a PHYSICAL unary pending word. Unlike the
singleton entry, `.read` does not prepend another pending-tree token. -/
def forestForwardRoutine (p : TreeMaskPorts K) : Routine (fun _ : K => Bool) (F × Bool) :=
  RoutineComposition.seq (treeMaskCallerRoutine p .read) (frameReverseRoutine p.reverse p.output)

theorem forestForward_executes (p : TreeMaskPorts K) (base : K → List Bool)
    (frame : F) (flag : Bool) (bits : List Bool) (q : ℕ) :
    ∃ n ≤ 4 * bits.length + q + 4,
      (forestForwardRoutine p).Executes
        (treeMaskCallerStore p (Function.update base p.output []) frame flag bits
          (List.replicate q true) [])
        (treeMaskForwardResult p base frame (rawForestMaskParse bits.length q bits)) n := by
  obtain ⟨n, hn, hparse⟩ := treeMaskCaller_forest_executes p
    (Function.update base p.output []) frame flag bits [] q
  cases hp : rawForestMaskParse bits.length q bits with
  | none =>
      have hreverse := frameReverse_executes p.reverse p.output p.hro
        (Function.update (Function.update base p.source []) p.pending []) frame false [] []
      have hparse' : (treeMaskCallerRoutine p .read).Executes
          (treeMaskCallerStore p (Function.update base p.output []) frame flag bits
            (List.replicate q true) [])
          (frameCallerStore p.reverse p.output
            (Function.update (Function.update base p.source []) p.pending []) frame false [] []) n := by
        simpa only [hp, treeMaskCallerResult, List.append_nil, treeMask_reverse_rotate] using hparse
      have hjoin := RoutineComposition.seq_executes (treeMaskCallerRoutine p .read)
        (frameReverseRoutine p.reverse p.output) hparse' hreverse
      rw [← treeMask_reverse_rotate p base frame false [] [] []] at hjoin
      refine ⟨n + 1, by simp only [List.length_nil] at hn; omega, ?_⟩
      simpa only [forestForwardRoutine, treeMaskForwardResult, hp, List.length_nil,
        List.reverse_nil, List.nil_append] using hjoin
  | some result =>
      rcases result with ⟨rest, mask⟩
      have hlen := rawForestMaskParse_consumption bits rest mask q hp
      have hreverse := frameReverse_executes p.reverse p.output p.hro
        (Function.update (Function.update base p.source rest) p.pending []) frame true mask.reverse []
      have hparse' : (treeMaskCallerRoutine p .read).Executes
          (treeMaskCallerStore p (Function.update base p.output []) frame flag bits
            (List.replicate q true) [])
          (frameCallerStore p.reverse p.output
            (Function.update (Function.update base p.source rest) p.pending [])
            frame true mask.reverse []) n := by
        simpa only [hp, treeMaskCallerResult, List.append_nil, treeMask_reverse_rotate] using hparse
      have hjoin := RoutineComposition.seq_executes (treeMaskCallerRoutine p .read)
        (frameReverseRoutine p.reverse p.output) hparse' hreverse
      simp only [List.reverse_reverse, List.append_nil] at hjoin
      rw [← treeMask_reverse_rotate p base frame true rest [] mask] at hjoin
      refine ⟨n + (mask.length + 1), by simp only [List.length_nil] at hn; omega, ?_⟩
      simpa only [forestForwardRoutine, treeMaskForwardResult, hp, List.length_reverse] using hjoin

inductive ForestSyntaxPort where
  | source | count | tail | pending | reverse | mask | temp
  deriving DecidableEq, Fintype

abbrev ForestSyntaxPorts (K : Type) := ForestSyntaxPort ↪ K

@[simp] theorem forestSyntaxPorts_eq (p : ForestSyntaxPorts K) (a b : ForestSyntaxPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def forestSyntaxMaskPorts (p : ForestSyntaxPorts K) : TreeMaskPorts K where
  source := p .source
  pending := p .pending
  reverse := p .reverse
  output := p .mask
  hsp := by simp
  hsr := by simp
  hso := by simp
  hpr := by simp
  hpo := by simp
  hro := by simp

def forestSyntaxStartOp : Op K Bool (CountdownState F) := .load (fun s => (s.1, true))

def forestSyntaxAfterCount (p : ForestSyntaxPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  guardedUnaryFieldEval (p .source) (p .count) (forestSyntaxStartOp.apply s)

def forestSyntaxPrepareRoutine (p : ForestSyntaxPorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine (p .source) (p .temp) (p .tail))
    (wordDuplicateRoutine (p .count) (p .temp) (p .pending))

def forestSyntaxPrepared (p : ForestSyntaxPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  wordDuplicateEval (p .count) (p .pending) (wordDuplicateEval (p .source) (p .tail) s)

theorem forestSyntaxPrepare_executes (p : ForestSyntaxPorts K) (s : CountdownStore K F)
    (ht : s.stk (p .temp) = []) :
    (forestSyntaxPrepareRoutine p).Executes s (forestSyntaxPrepared p s)
      (3 * (s.stk (p .source)).length + 3 * (s.stk (p .count)).length + 6) := by
  have h1 := wordDuplicate_executes (p .source) (p .temp) (p .tail)
    (by simp) (by simp) (by simp) s ht
  have ht' : (wordDuplicateEval (p .source) (p .tail) s).stk (p .temp) = [] := by
    simp [wordDuplicateEval, ht]
  have h2 := wordDuplicate_executes (p .count) (p .temp) (p .pending)
    (by simp) (by simp) (by simp) (wordDuplicateEval (p .source) (p .tail) s) ht'
  have hjoin := RoutineComposition.seq_executes _ _ h1 h2
  simpa [forestSyntaxPrepareRoutine, forestSyntaxPrepared, wordDuplicateEval,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hjoin

def forestSyntaxAfterMask (p : ForestSyntaxPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  treeMaskForwardResult (forestSyntaxMaskPorts p) s.stk s.state.1
    (rawForestMaskParse (s.stk (p .source)).length (s.stk (p .pending)).length (s.stk (p .source)))

theorem forestSyntaxMask_executes (p : ForestSyntaxPorts K) (s : CountdownStore K F)
    (hu : IsUnaryWord (s.stk (p .pending)))
    (hr : s.stk (p .reverse) = []) (hm : s.stk (p .mask) = []) :
    ∃ n ≤ 4 * (s.stk (p .source)).length + (s.stk (p .pending)).length + 4,
      (forestForwardRoutine (forestSyntaxMaskPorts p)).Executes s (forestSyntaxAfterMask p s) n := by
  obtain ⟨n, hn, he⟩ := forestForward_executes (forestSyntaxMaskPorts p) s.stk s.state.1 s.state.2
    (s.stk (p .source)) (s.stk (p .pending)).length
  have hentry : treeMaskCallerStore (forestSyntaxMaskPorts p)
      (Function.update s.stk (p .mask) []) s.state.1 s.state.2 (s.stk (p .source))
      (List.replicate (s.stk (p .pending)).length true) [] = s := by
    apply countdownStore_ext
    · rfl
    · funext k
      by_cases hs : k = p .source <;> by_cases hp : k = p .pending <;>
        by_cases hr' : k = p .reverse <;> by_cases hm' : k = p .mask <;>
        simp_all [treeMaskCallerStore, forestSyntaxMaskPorts, frameCallerStore, IsUnaryWord]
  rw [hentry] at he
  exact ⟨n, hn, he⟩

def forestSyntaxSuccessRoutine (p : ForestSyntaxPorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (forestSyntaxPrepareRoutine p) (forestForwardRoutine (forestSyntaxMaskPorts p))

def forestSyntaxSuccessEval (p : ForestSyntaxPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  forestSyntaxAfterMask p (forestSyntaxPrepared p s)

def forestSyntaxRoutine (p : ForestSyntaxPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine forestSyntaxStartOp)
    (RoutineComposition.seq (guardedUnaryFieldRoutine (p .source) (p .count))
      (RoutineControl.branch Prod.snd (forestSyntaxSuccessRoutine p) (Atom.routine cleanupNoop)))

def forestSyntaxEval (p : ForestSyntaxPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  let u := forestSyntaxAfterCount p s
  if u.state.2 then forestSyntaxSuccessEval p u else u

/-- One unary tree count, then the SAME raw pending parser. The saved
tail is a paid faithful copy, not a theorem-side resurrection of input.
The count is also preserved for the later m+1 test. No typed-tree or
constructor-image promise is required for this operational theorem. -/
theorem forestSyntax_executes (p : ForestSyntaxPorts K) (L : ℕ) (s : CountdownStore K F)
    (hL : (s.stk (p .source)).length ≤ L)
    (hfresh : ∀ j : ForestSyntaxPort, j ≠ .source → s.stk (p j) = []) :
    ∃ n ≤ 13 * L + 16, (forestSyntaxRoutine p).Executes s (forestSyntaxEval p s) n := by
  let s0 := forestSyntaxStartOp.apply s
  let u := forestSyntaxAfterCount p s
  have hc0 : s0.stk (p .count) = [] := hfresh .count (by decide)
  have hL0 : (s0.stk (p .source)).length ≤ L := hL
  obtain ⟨a, ha, hcount⟩ := guardedUnaryField_executes (p .source) (p .count) (by simp) s0 hc0 L hL0
  have hLu : (u.stk (p .source)).length ≤ L :=
    (guardedUnaryField_source_bound (p .source) (p .count) (by simp) s0).trans hL0
  have hCu : (u.stk (p .count)).length ≤ L :=
    (guardedUnaryField_output_bound (p .source) (p .count) s0 hc0).trans hL0
  have hUu : IsUnaryWord (u.stk (p .count)) :=
    guardedUnaryField_output_unary (p .source) (p .count) s0 hc0
  have hclean (j : ForestSyntaxPort) (hjs : j ≠ .source) (hjc : j ≠ .count) :
      u.stk (p j) = [] := by
    exact (guardedUnaryField_extra (p .source) (p .count) (p j)
      (by simpa using hjs) (by simpa using hjc) s0).trans (hfresh j hjs)
  have hstart := Atom.executes (forestSyntaxStartOp (K := K) (F := F)) s
  cases hg : u.state.2 with
  | false =>
      have hskip := RoutineControl.branch_false Prod.snd (forestSyntaxSuccessRoutine p)
        (Atom.routine cleanupNoop) hg (Atom.executes cleanupNoop u)
      have he := RoutineComposition.seq_executes _ _ hstart
        (RoutineComposition.seq_executes _ _ hcount hskip)
      refine ⟨1 + (a + 2), by omega, ?_⟩
      simpa [forestSyntaxRoutine, forestSyntaxEval, u, s0, hg, cleanupNoop, Op.apply] using he
  | true =>
      let v := forestSyntaxPrepared p u
      have hprep := forestSyntaxPrepare_executes p u (hclean .temp (by decide) (by decide))
      have hvs : v.stk (p .source) = u.stk (p .source) := by simp [v, forestSyntaxPrepared, wordDuplicateEval]
      have hvp : v.stk (p .pending) = u.stk (p .count) := by
        simp [v, forestSyntaxPrepared, wordDuplicateEval, hclean .pending (by decide) (by decide)]
      have hvr : v.stk (p .reverse) = [] := by
        simp [v, forestSyntaxPrepared, wordDuplicateEval, hclean .reverse (by decide) (by decide)]
      have hvm : v.stk (p .mask) = [] := by
        simp [v, forestSyntaxPrepared, wordDuplicateEval, hclean .mask (by decide) (by decide)]
      obtain ⟨b, hb, hmask⟩ := forestSyntaxMask_executes p v (by rw [hvp]; exact hUu) hvr hvm
      have hsuccess := RoutineComposition.seq_executes _ _ hprep hmask
      have hbranch := RoutineControl.branch_true Prod.snd (forestSyntaxSuccessRoutine p)
        (Atom.routine cleanupNoop) hg hsuccess
      have he := RoutineComposition.seq_executes _ _ hstart
        (RoutineComposition.seq_executes _ _ hcount hbranch)
      refine ⟨1 + (a + ((3 * (u.stk (p .source)).length +
        3 * (u.stk (p .count)).length + 6 + b) + 1)), ?_, ?_⟩
      · rw [hvs, hvp] at hb
        omega
      · simpa only [forestSyntaxRoutine, forestSyntaxEval, hg, ↓reduceIte,
          forestSyntaxSuccessRoutine, forestSyntaxSuccessEval, forestSyntaxAfterCount, u, v, s0] using he

/-- This is a mathematical observation of the phase's public ports,
not an extra machine instruction. -/
def forestSyntaxObservation (p : ForestSyntaxPorts K) (s : CountdownStore K F) :
    Option (ℕ × List Bool × List Bool × List Bool) :=
  if s.state.2 then some ((s.stk (p .count)).length, s.stk (p .tail),
    s.stk (p .source), s.stk (p .mask)) else none

def originalForestSyntaxRead (bits : List Bool) : Option (ℕ × List Bool × List Bool × List Bool) :=
  (readUnaryFrame bits).bind (fun qt =>
    (rawForestMaskParse qt.2.length qt.1 qt.2).map (fun rm => (qt.1, qt.2, rm.1, rm.2)))

theorem forestSyntax_observation (p : ForestSyntaxPorts K) (s : CountdownStore K F)
    (hfresh : ∀ j : ForestSyntaxPort, j ≠ .source → s.stk (p j) = []) :
    forestSyntaxObservation p (forestSyntaxEval p s) = originalForestSyntaxRead (s.stk (p .source)) := by
  have ht := hfresh .tail (by decide)
  have hp := hfresh .pending (by decide)
  cases hc : readUnaryFrame (s.stk (p .source)) with
  | none =>
      simp [forestSyntaxObservation, forestSyntaxEval, forestSyntaxAfterCount,
        guardedUnaryFieldEval, forestSyntaxStartOp, Op.apply, unaryCallerResult,
        frameCallerStore, originalForestSyntaxRead, hc]
  | some qt =>
      rcases qt with ⟨q, tail⟩
      cases hm : rawForestMaskParse tail.length q tail with
      | none =>
          simp [forestSyntaxObservation, forestSyntaxEval, forestSyntaxAfterCount,
            guardedUnaryFieldEval, forestSyntaxStartOp, Op.apply, unaryCallerResult,
            frameCallerStore, originalForestSyntaxRead, hc, forestSyntaxSuccessEval,
            forestSyntaxPrepared, wordDuplicateEval, forestSyntaxAfterMask,
            treeMaskForwardResult, treeMaskCallerStore, forestSyntaxMaskPorts, ht, hp, hm]
      | some rm =>
          rcases rm with ⟨rest, mask⟩
          simp [forestSyntaxObservation, forestSyntaxEval, forestSyntaxAfterCount,
            guardedUnaryFieldEval, forestSyntaxStartOp, Op.apply, unaryCallerResult,
            frameCallerStore, originalForestSyntaxRead, hc, forestSyntaxSuccessEval,
            forestSyntaxPrepared, wordDuplicateEval, forestSyntaxAfterMask,
            treeMaskForwardResult, treeMaskCallerStore, forestSyntaxMaskPorts, ht, hp, hm]

theorem originalForestSyntaxRead_success (bits : List Bool) (q : ℕ) (tail rest mask : List Bool) :
    originalForestSyntaxRead bits = some (q, tail, rest, mask) ↔
      readUnaryFrame bits = some (q, tail) ∧
      rawForestMaskParse tail.length q tail = some (rest, mask) := by
  constructor
  · intro h
    cases hc : readUnaryFrame bits with
    | none => simp [originalForestSyntaxRead, hc] at h
    | some qt =>
        rcases qt with ⟨q', tail'⟩
        cases hp : rawForestMaskParse tail'.length q' tail' with
        | none => simp [originalForestSyntaxRead, hc, hp] at h
        | some rm =>
            rcases rm with ⟨rest', mask'⟩
            have he : (q', tail', rest', mask') = (q, tail, rest, mask) :=
              Option.some.inj (by simpa only [originalForestSyntaxRead, hc, hp,
                Option.bind_some, Option.map_some] using h)
            have he' : q' = q ∧ tail' = tail ∧ rest' = rest ∧ mask' = mask := by
              simpa only [Prod.mk.injEq] using he
            rcases he' with ⟨rfl, rfl, rfl, rfl⟩
            exact ⟨hc, hp⟩
  · rintro ⟨hc, hp⟩
    simp [originalForestSyntaxRead, hc, hp]

/-- Global bridge from the ACTUAL emitted syntax phase. Only the range
scan remains a Boolean premise here; the raw trees are reconstructed,
not promised. This premise must be discharged by the paid cursor below
before it can contribute to the full machine witness. -/
theorem forestSyntax_typed_success (p : ForestSyntaxPorts K) (N m : ℕ) (s : CountdownStore K F)
    (hfresh : ∀ j : ForestSyntaxPort, j ≠ .source → s.stk (p j) = [])
    (hflag : (forestSyntaxEval p s).state.2 = true)
    (hcheck : forestMaskCellCheck N m ((forestSyntaxEval p s).stk (p .tail))
      ((forestSyntaxEval p s).stk (p .mask)) = true) :
    ∃ Ts : List (BTree (Cell N m)), Ts.length = ((forestSyntaxEval p s).stk (p .count)).length ∧
      readFramedList (readTargetTree N m) (s.stk (p .source)) =
        some (Ts, (forestSyntaxEval p s).stk (p .source)) := by
  have ho := forestSyntax_observation p s hfresh
  have hp : originalForestSyntaxRead (s.stk (p .source)) =
      some (((forestSyntaxEval p s).stk (p .count)).length,
        (forestSyntaxEval p s).stk (p .tail), (forestSyntaxEval p s).stk (p .source),
        (forestSyntaxEval p s).stk (p .mask)) := by
    simpa only [forestSyntaxObservation, hflag, ↓reduceIte] using ho.symm
  obtain ⟨hcount, hparse⟩ := (originalForestSyntaxRead_success _ _ _ _ _).mp hp
  exact observedForest_to_original N m _ _ _ _ _ hcount hparse hcheck

/- Still to discharge in this SAME controller:
  (1) paid mask cursor + local-range bodies, discharging hcheck above;
  (2) exact reverse success/rejection observation of the combined typed phase;
  (3) bounded original headers/certificate and every guard/clade/score scan;
  (4) exact one-bit clean halt and one global polynomial.
No whole verifier witness is claimed by the syntax-phase time theorem.
-/

/-! ## Paid cursor body and its owned-query cleanup -/

inductive RangeCursorPort where
  | originalWord | originalMask | word | mask | counter
  | source | block | kind | rows | types | temp | residue | subtrahend
  deriving DecidableEq, Fintype

abbrev RangeCursorPorts (K : Type) := RangeCursorPort ↪ K

@[simp] theorem rangeCursorPorts_eq (p : RangeCursorPorts K) (a b : RangeCursorPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def rangeTypedPorts (p : RangeCursorPorts K) : TypedCellPorts K where
  toFun := fun
    | .source => p .source
    | .block => p .block
    | .kind => p .kind
    | .rows => p .rows
    | .types => p .types
    | .temp => p .temp
    | .residue => p .residue
    | .subtrahend => p .subtrahend
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def rangeQueryOwned (p : RangeCursorPorts K) : List K := [p .source, p .block, p .kind]

def rangeLeafPrepared (p : RangeCursorPorts K) (s : CountdownStore K F) :=
  wordDuplicateEval (p .word) (p .source) s

def rangeLeafParsed (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  typedLeafCellEval (rangeTypedPorts p) m A (rangeLeafPrepared p s)

def rangeLeafEval (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  clearManyEval (rangeQueryOwned p) (rangeLeafParsed p m A s)

def rangeLeafRoutine (p : RangeCursorPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine (p .word) (p .temp) (p .source))
    (RoutineComposition.seq (typedLeafCellRoutine (rangeTypedPorts p))
      (clearManyRoutine (rangeQueryOwned p)))

def RangeQueryInv (p : RangeCursorPorts K) (m A L : ℕ) (s : CountdownStore K F) : Prop :=
  (s.stk (p .word)).length ≤ L ∧
  s.stk (p .rows) = List.replicate m true ∧
  s.stk (p .types) = List.replicate A true ∧
  s.stk (p .source) = [] ∧ s.stk (p .block) = [] ∧ s.stk (p .kind) = [] ∧
  s.stk (p .temp) = [] ∧ s.stk (p .residue) = [] ∧ s.stk (p .subtrahend) = []

theorem rangeLeaf_executes (p : RangeCursorPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : RangeQueryInv p m A L s) :
    ∃ n ≤ 18 * L + 4 * m + 4 * A + 36,
      (rangeLeafRoutine p).Executes s (rangeLeafEval p m A s) n := by
  rcases hs with ⟨hL, hm, hA, hsource, hb, hk, ht, hr, hd⟩
  let u := rangeLeafPrepared p s
  let v := rangeLeafParsed p m A s
  have huSource : u.stk (p .source) = s.stk (p .word) := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, hsource]
  have huExtra (j : RangeCursorPort) (hj : j ≠ .source) : u.stk (p j) = s.stk (p j) := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, hj]
  have huL : (u.stk (p .source)).length ≤ L := by rw [huSource]; exact hL
  have hbu := (huExtra .block (by decide)).trans hb
  have hku := (huExtra .kind (by decide)).trans hk
  have h1 := wordDuplicate_executes (p .word) (p .temp) (p .source)
    (by simp) (by simp) (by simp) s ht
  obtain ⟨a, ha, h2⟩ := typedLeafCell_executes (rangeTypedPorts p) m A L u huL
    ((huExtra .rows (by decide)).trans hm) ((huExtra .types (by decide)).trans hA)
    hbu hku ((huExtra .temp (by decide)).trans ht)
    ((huExtra .residue (by decide)).trans hr) ((huExtra .subtrahend (by decide)).trans hd)
  have hbds := rawLeafCell_bounds (typedRawCellPorts (rangeTypedPorts p)) L u huL hbu hku
  have hv : v.stk = (rawLeafCellEval (typedRawCellPorts (rangeTypedPorts p)) u).stk :=
    typedLeafCell_stacks (rangeTypedPorts p) m A u
  have hmass : cleanupMass (rangeQueryOwned p) v ≤ 3 * L := by
    have hsum := Nat.add_le_add (Nat.add_le_add hbds.1 hbds.2.1) hbds.2.2
    simp only [cleanupMass, rangeQueryOwned, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hv]
    simp only [typedRawCellPorts, rangeTypedPorts] at hsum
    omega
  obtain ⟨b, hbtime, h3⟩ := clearMany_executes (rangeQueryOwned p) v
  have hjoin := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)
  refine ⟨3 * (s.stk (p .word)).length + 3 + (a + b), ?_, hjoin⟩
  simp only [rangeQueryOwned, List.length_cons, List.length_nil] at hbtime
  omega

theorem rangeLeaf_result (p : RangeCursorPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : RangeQueryInv p m A L s) :
    rangeLeafEval p m A s = cellCompareFlagStore
      (filterRawLeafCell m A (readRawLeafCell (s.stk (p .word)))).isSome s := by
  rcases hs with ⟨hL, hm, hA, hsource, hb, hk, ht, hr, hd⟩
  let u := rangeLeafPrepared p s
  let v := rangeLeafParsed p m A s
  have huSource : u.stk (p .source) = s.stk (p .word) := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, hsource]
  have hobs := typedLeafCell_observation (rangeTypedPorts p) m A u
  have hflag : v.state.2 = (filterRawLeafCell m A (readRawLeafCell (s.stk (p .word)))).isSome := by
    have h := congrArg Option.isSome hobs
    rw [huSource] at h
    have hsome : (rawLeafCellObservation (typedRawCellPorts (rangeTypedPorts p)) v).isSome =
        v.state.2 := by
      cases hf : v.state.2 <;> simp [rawLeafCellObservation, hf]
    rw [hsome] at h
    exact h
  have hframe : v.state.1 = s.state.1 := typedLeafCell_frame (rangeTypedPorts p) m A u
  apply countdownStore_ext
  · rw [rangeLeafEval, clearMany_state]
    exact Prod.ext hframe hflag
  · funext j
    by_cases hj : j ∈ rangeQueryOwned p
    · rw [rangeLeafEval, clearMany_member _ _ hj]
      have hz : s.stk j = [] := by
        simp only [rangeQueryOwned, List.mem_cons, List.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> assumption
      exact hz.symm
    · have hjs : j ≠ p .source := by intro h; apply hj; simp [rangeQueryOwned, h]
      have hjb : j ≠ p .block := by intro h; apply hj; simp [rangeQueryOwned, h]
      have hjk : j ≠ p .kind := by intro h; apply hj; simp [rangeQueryOwned, h]
      rw [rangeLeafEval, clearMany_outside _ _ hj, typedLeafCell_stacks,
        rawLeafCell_extra (typedRawCellPorts (rangeTypedPorts p)) j hjs hjb hjk]
      simp [rangeLeafPrepared, wordDuplicateEval, cellCompareFlagStore, hjs]

/-- The first cached Boolean is used ONLY between this peek and its
branch. The enclosing countdown refreshes its own cached guard later. -/
def rangeLocalPeekOp (p : RangeCursorPorts K) : Op K Bool (CountdownState F) :=
  .peek (p .word) (fun st h => ((st.1.1, h == some true), h.isSome))

def rawRangeCheck (m A : ℕ) : List Bool → Bool
  | [] => false
  | false :: _ => true
  | true :: bits => (filterRawLeafCell m A (readRawLeafCell (true :: bits))).isSome

def rangeLocalRoutine (p : RangeCursorPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (rangeLocalPeekOp p))
    (RoutineControl.branch (fun st => st.1.2) (rangeLeafRoutine p) (Atom.routine cleanupNoop))

def rangeLocalResult (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨((s.state.1.1, (s.stk (p .word)).head? == some true), rawRangeCheck m A (s.stk (p .word))), s.stk⟩

theorem rawRangeCheck_original (N m : ℕ) (bits : List Bool) :
    rawRangeCheck m (N + m * N + 3) bits = legalSuffixCellCheck N m bits := by
  cases bits with
  | nil => rfl
  | cons b bs =>
      cases b with
      | false => rfl
      | true =>
          have h := congrArg Option.isSome (readOriginalLeafCell_filtered N m (true :: bs))
          cases hp : readCellBits N m bs <;>
            simpa [rawRangeCheck, legalSuffixCellCheck, readOriginalLeafCell, hp] using h.symm

theorem rangeLocal_executes (p : RangeCursorPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : RangeQueryInv p m A L s) :
    ∃ n ≤ 18 * L + 4 * m + 4 * A + 38,
      (rangeLocalRoutine p).Executes s (rangeLocalResult p m A s) n := by
  let u := (rangeLocalPeekOp p).apply s
  have hu : RangeQueryInv p m A L u := hs
  have hpeek := Atom.executes (rangeLocalPeekOp p) s
  cases hw : s.stk (p .word) with
  | nil =>
      have hg : u.state.1.2 = false := by simp [u, rangeLocalPeekOp, Op.apply, hw]
      have hb := RoutineControl.branch_false (fun st : CountdownState F => st.1.2)
        (rangeLeafRoutine p) (Atom.routine cleanupNoop) hg (Atom.executes cleanupNoop u)
      have he := RoutineComposition.seq_executes _ _ hpeek hb
      refine ⟨3, by omega, ?_⟩
      simpa [rangeLocalRoutine, rangeLocalResult, rawRangeCheck, u, rangeLocalPeekOp,
        cleanupNoop, Op.apply, hw] using he
  | cons b bs =>
      cases b with
      | false =>
          have hg : u.state.1.2 = false := by simp [u, rangeLocalPeekOp, Op.apply, hw]
          have hb := RoutineControl.branch_false (fun st : CountdownState F => st.1.2)
            (rangeLeafRoutine p) (Atom.routine cleanupNoop) hg (Atom.executes cleanupNoop u)
          have he := RoutineComposition.seq_executes _ _ hpeek hb
          refine ⟨3, by omega, ?_⟩
          simpa [rangeLocalRoutine, rangeLocalResult, rawRangeCheck, u, rangeLocalPeekOp,
            cleanupNoop, Op.apply, hw] using he
      | true =>
          have hg : u.state.1.2 = true := by simp [u, rangeLocalPeekOp, Op.apply, hw]
          obtain ⟨n, hn, hrun⟩ := rangeLeaf_executes p m A L u hu
          rw [rangeLeaf_result p m A L u hu] at hrun
          have hb := RoutineControl.branch_true (fun st : CountdownState F => st.1.2)
            (rangeLeafRoutine p) (Atom.routine cleanupNoop) hg hrun
          have he := RoutineComposition.seq_executes _ _ hpeek hb
          refine ⟨1 + (n + 1), by omega, ?_⟩
          simpa [rangeLocalRoutine, rangeLocalResult, rawRangeCheck, u, rangeLocalPeekOp,
            cellCompareFlagStore, Op.apply, hw] using he

def rangeSelectMaskOp (p : RangeCursorPorts K) : Op K Bool (CountdownState F) :=
  .peek (p .mask) (fun st h => ((st.1.1, h.getD false), st.2))

def rangePopWordOp (p : RangeCursorPorts K) : Op K Bool (CountdownState F) :=
  .pop (p .word) (fun st _ => st)

def rangePopMaskOp (p : RangeCursorPorts K) : Op K Bool (CountdownState F) :=
  .pop (p .mask) (fun st _ => st)

def rangeBodySelected (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  let u := (rangeSelectMaskOp p).apply s
  if u.state.1.2 then rangeLocalResult p m A u else u

def rangeBodyEval (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  (rangePopMaskOp p).apply ((rangePopWordOp p).apply (rangeBodySelected p m A s))

def rangeBodyRoutine (p : RangeCursorPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (rangeSelectMaskOp p))
    (RoutineComposition.seq
      (RoutineControl.branch (fun st => st.1.2) (rangeLocalRoutine p) (Atom.routine cleanupNoop))
      (RoutineComposition.seq (Atom.routine (rangePopWordOp p)) (Atom.routine (rangePopMaskOp p))))

theorem rangeBody_stacks (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (rangeBodyEval p m A s).stk =
      Function.update (Function.update s.stk (p .word) (s.stk (p .word)).tail)
        (p .mask) (s.stk (p .mask)).tail := by
  by_cases hm : (s.stk (p .mask)).head?.getD false = true <;>
    simp [rangeBodyEval, rangeBodySelected, rangeSelectMaskOp, rangePopWordOp,
      rangePopMaskOp, Op.apply, rangeLocalResult, hm]

theorem rangeBody_frame (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (rangeBodyEval p m A s).state.1.1 = s.state.1.1 := by
  by_cases hm : (s.stk (p .mask)).head?.getD false = true <;>
    simp [rangeBodyEval, rangeBodySelected, rangeSelectMaskOp, rangePopWordOp,
      rangePopMaskOp, Op.apply, rangeLocalResult, hm]

theorem rangeBody_flag (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (rangeBodyEval p m A s).state.2 =
      if (s.stk (p .mask)).head?.getD false then rawRangeCheck m A (s.stk (p .word)) else s.state.2 := by
  by_cases hm : (s.stk (p .mask)).head?.getD false = true <;>
    simp [rangeBodyEval, rangeBodySelected, rangeSelectMaskOp, rangePopWordOp,
      rangePopMaskOp, Op.apply, rangeLocalResult, hm]

theorem rangeBody_extra (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F)
    (j : K) (hjw : j ≠ p .word) (hjm : j ≠ p .mask) :
    (rangeBodyEval p m A s).stk j = s.stk j := by
  rw [rangeBody_stacks]
  simp [hjw, hjm]

theorem rangeBody_inv (p : RangeCursorPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : RangeQueryInv p m A L s) : RangeQueryInv p m A L (rangeBodyEval p m A s) := by
  have htail : (s.stk (p .word)).tail.length ≤ (s.stk (p .word)).length := by
    cases s.stk (p .word) <;> simp
  unfold RangeQueryInv at hs ⊢
  rw [rangeBody_stacks]
  simpa using And.intro (htail.trans hs.1) hs.2

theorem rangeBody_executes (p : RangeCursorPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : RangeQueryInv p m A L s) :
    ∃ n ≤ 18 * L + 4 * m + 4 * A + 42,
      (rangeBodyRoutine p).Executes s (rangeBodyEval p m A s) n := by
  let u := (rangeSelectMaskOp p).apply s
  let v := rangeBodySelected p m A s
  have hu : RangeQueryInv p m A L u := hs
  have hpeek := Atom.executes (rangeSelectMaskOp p) s
  have hpop1 := Atom.executes (rangePopWordOp p) v
  have hpop2 := Atom.executes (rangePopMaskOp p) ((rangePopWordOp p).apply v)
  have hpops := RoutineComposition.seq_executes _ _ hpop1 hpop2
  cases hg : u.state.1.2 with
  | false =>
      have hb := RoutineControl.branch_false (fun st : CountdownState F => st.1.2)
        (rangeLocalRoutine p) (Atom.routine cleanupNoop) hg (Atom.executes cleanupNoop u)
      have hv : v = u := by simp [v, rangeBodySelected, hg, u]
      rw [hv] at hpops
      have he := RoutineComposition.seq_executes _ _ hpeek
        (RoutineComposition.seq_executes _ _ hb hpops)
      refine ⟨5, by omega, ?_⟩
      simpa [rangeBodyRoutine, rangeBodyEval, rangeBodySelected, hg, u,
        cleanupNoop, Op.apply] using he
  | true =>
      obtain ⟨n, hn, hlocal⟩ := rangeLocal_executes p m A L u hu
      have hb := RoutineControl.branch_true (fun st : CountdownState F => st.1.2)
        (rangeLocalRoutine p) (Atom.routine cleanupNoop) hg hlocal
      have hv : v = rangeLocalResult p m A u := by simp [v, rangeBodySelected, hg, u]
      rw [hv] at hpops
      have he := RoutineComposition.seq_executes _ _ hpeek
        (RoutineComposition.seq_executes _ _ hb hpops)
      refine ⟨1 + ((n + 1) + (1 + 1)), by omega, ?_⟩
      simpa only [rangeBodyRoutine, rangeBodyEval, rangeBodySelected, hg, ↓reduceIte, u] using he

/-- Counter copies need not be unary: the existing physical countdown
uses only their length. The independent mask word retains each bit for
selection. Its head is never guessed from a parseable source suffix. -/
def rangeCountdownContract (p : RangeCursorPorts K) (m A L : ℕ) :
    CountdownContract (p .counter) (rangeBodyRoutine p) (rangeBodyEval p m A)
      (RangeQueryInv p m A L) (18 * L + 4 * m + 4 * A + 42) where
  peek_closed s hs := hs
  pop_closed s hs hg := by
    simpa [RangeQueryInv, countdownPop, countdownPopOp, Op.apply] using hs
  body_closed s hs := rangeBody_inv p m A L s hs
  reset_closed s hs := hs
  counter_preserved s hs := rangeBody_extra p m A s (p .counter) (by simp) (by simp)
  body_executes s hs := rangeBody_executes p m A L s hs

def rangeCountdownRoutine (p : RangeCursorPorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  countdownRoutine (p .counter) (rangeBodyRoutine p)

def rangeCountdownEval (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  countdownEval (p .counter) (rangeBodyEval p m A) s

theorem rangeCountdown_executes (p : RangeCursorPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : RangeQueryInv p m A L s) :
    ∃ n ≤ (s.stk (p .counter)).length * (18 * L + 4 * m + 4 * A + 45) + 3,
      (rangeCountdownRoutine p).Executes s (rangeCountdownEval p m A s) n ∧
      RangeQueryInv p m A L (rangeCountdownEval p m A s) ∧
      (rangeCountdownEval p m A s).state.1.2 = false ∧
      ((rangeCountdownEval p m A s).state.2 = true →
        (rangeCountdownEval p m A s).stk (p .counter) = []) := by
  simpa only [rangeCountdownRoutine, rangeCountdownEval, Nat.add_assoc] using
    countdownRoutine_executes (p .counter) (rangeBodyRoutine p) (rangeBodyEval p m A)
      (RangeQueryInv p m A L) (18 * L + 4 * m + 4 * A + 42)
      (rangeCountdownContract p m A L) s hs

/- The all-word OPERATIONAL cursor is now emitted and its body is fully
instantiated, including local typed query copies and cleanup. Its logical
all-mask observation, paid initialization/final cursor cleanup and joining
to forestSyntax_typed_success remain to be composed below. The final
VerifierMachineWitness and EncodedSourceHardness are still OPEN. -/

theorem rangeCountdownLoop_flag (p : RangeCursorPorts K) (m A fuel : ℕ) :
    ∀ s : CountdownStore K F,
      (s.stk (p .counter)).length = (s.stk (p .mask)).length →
      (s.stk (p .mask)).length ≤ (s.stk (p .word)).length →
      (s.stk (p .counter)).length ≤ fuel →
      s.state.1.2 = (s.stk (p .counter)).head?.isSome →
      (countdownLoopEval (p .counter) (rangeBodyEval p m A) fuel s).state.2 =
        s.state.2 && (rawMarkedSuffixes (s.stk (p .word)) (s.stk (p .mask))).all (rawRangeCheck m A) := by
  induction fuel with
  | zero =>
      intro s hsame hfit hlen hpeek
      have hm : s.stk (p .mask) = [] := List.eq_nil_of_length_eq_zero (by omega)
      cases hw : s.stk (p .word) <;>
        simp [countdownLoopEval, rawMarkedSuffixes, hm, hw]
  | succ fuel ih =>
      intro s hsame hfit hlen hpeek
      cases hf : s.state.2 with
      | false => simp [countdownLoopEval, countdownGuard, hf]
      | true =>
          cases hm : s.stk (p .mask) with
          | nil =>
              have hc : s.stk (p .counter) = [] := List.eq_nil_of_length_eq_zero (by simpa [hm] using hsame)
              cases hw : s.stk (p .word) <;>
                simp [countdownLoopEval, countdownGuard, hpeek, hc, hm, hw, rawMarkedSuffixes, hf]
          | cons mark mask =>
              cases hw : s.stk (p .word) with
              | nil => simp [hm, hw] at hfit
              | cons b bits =>
                  have hc : (s.stk (p .counter)).head?.isSome = true := by
                    cases hcs : s.stk (p .counter) with
                    | nil => simp [hcs, hm] at hsame
                    | cons c cs => rfl
                  have hg : countdownGuard s.state = true := by simp [countdownGuard, hpeek, hc, hf]
                  let u := countdownPeek (p .counter) (rangeBodyEval p m A (countdownPop (p .counter) s))
                  have huw : u.stk (p .word) = bits := by
                    change (rangeBodyEval p m A (countdownPop (p .counter) s)).stk (p .word) = bits
                    rw [rangeBody_stacks]
                    simp [countdownPop, countdownPopOp, Op.apply, hw]
                  have hum : u.stk (p .mask) = mask := by
                    change (rangeBodyEval p m A (countdownPop (p .counter) s)).stk (p .mask) = mask
                    rw [rangeBody_stacks]
                    simp [countdownPop, countdownPopOp, Op.apply, hm]
                  have huc : u.stk (p .counter) = (s.stk (p .counter)).tail := by
                    change (rangeBodyEval p m A (countdownPop (p .counter) s)).stk (p .counter) = _
                    rw [rangeBody_extra p m A _ (p .counter) (by simp) (by simp)]
                    exact countdownPop_counter (p .counter) s
                  have huf : u.state.2 = if mark then rawRangeCheck m A (b :: bits) else true := by
                    change (rangeBodyEval p m A (countdownPop (p .counter) s)).state.2 = _
                    rw [rangeBody_flag]
                    simp [countdownPop, countdownPopOp, Op.apply, hm, hw, hf]
                  have husame : (u.stk (p .counter)).length = (u.stk (p .mask)).length := by
                    rw [huc, hum]
                    cases hcs : s.stk (p .counter) with
                    | nil => simp [hcs, hm] at hsame
                    | cons c cs => simpa [hcs, hm] using hsame
                  have hufit : (u.stk (p .mask)).length ≤ (u.stk (p .word)).length := by
                    rw [hum, huw]
                    simpa [hm, hw] using hfit
                  have hulen : (u.stk (p .counter)).length ≤ fuel := by
                    rw [huc]
                    cases hcs : s.stk (p .counter) with
                    | nil => simp
                    | cons c cs => simpa [hcs] using hlen
                  have hi := ih u husame hufit hulen (countdownPeek_control (p .counter) _)
                  simp only [countdownLoopEval, hg, ↓reduceIte]
                  rw [hi, huf, huw, hum]
                  cases mark <;> simp [hm, hw, hf, rawMarkedSuffixes]

theorem rangeCountdown_flag (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F)
    (hsame : (s.stk (p .counter)).length = (s.stk (p .mask)).length)
    (hfit : (s.stk (p .mask)).length ≤ (s.stk (p .word)).length) :
    (rangeCountdownEval p m A s).state.2 =
      s.state.2 && (rawMarkedSuffixes (s.stk (p .word)) (s.stk (p .mask))).all (rawRangeCheck m A) := by
  exact rangeCountdownLoop_flag p m A (s.stk (p .counter)).length
    (countdownPeek (p .counter) s) hsame hfit (le_refl _) (countdownPeek_control (p .counter) s)

/-- This identifies the paid all-mask scan with the exact grammar range
predicate. The mask/source length relation is derived from parsing in
the full controller, not imposed on arbitrary input words. -/
theorem rangeCountdown_original_flag (p : RangeCursorPorts K) (N m : ℕ) (s : CountdownStore K F)
    (hsame : (s.stk (p .counter)).length = (s.stk (p .mask)).length)
    (hfit : (s.stk (p .mask)).length ≤ (s.stk (p .word)).length) :
    (rangeCountdownEval p m (N + m * N + 3) s).state.2 =
      s.state.2 && forestMaskCellCheck N m (s.stk (p .word)) (s.stk (p .mask)) := by
  rw [rangeCountdown_flag p m (N + m * N + 3) s hsame hfit]
  have hf : rawRangeCheck m (N + m * N + 3) = legalSuffixCellCheck N m :=
    funext (rawRangeCheck_original N m)
  rw [hf]
  rfl

def rangeCursorOwned (p : RangeCursorPorts K) : List K := [p .word, p .mask, p .counter]

def rangeAllWork (p : RangeCursorPorts K) : List K :=
  [p .word, p .mask, p .counter, p .source, p .block, p .kind, p .temp, p .residue, p .subtrahend]

def RangeAllEntry (p : RangeCursorPorts K) (m A L : ℕ) (s : CountdownStore K F) : Prop :=
  (s.stk (p .originalWord)).length ≤ L ∧
  (s.stk (p .originalMask)).length ≤ (s.stk (p .originalWord)).length ∧
  s.stk (p .rows) = List.replicate m true ∧ s.stk (p .types) = List.replicate A true ∧
  ∀ j ∈ rangeAllWork p, s.stk j = []

def rangeAllPrepareRoutine (p : RangeCursorPorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine (p .originalWord) (p .temp) (p .word))
    (RoutineComposition.seq (wordDuplicateRoutine (p .originalMask) (p .temp) (p .mask))
      (RoutineComposition.seq (wordDuplicateRoutine (p .mask) (p .temp) (p .counter))
        (Atom.routine forestSyntaxStartOp)))

def rangeAllPrepared (p : RangeCursorPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  forestSyntaxStartOp.apply (wordDuplicateEval (p .mask) (p .counter)
    (wordDuplicateEval (p .originalMask) (p .mask)
      (wordDuplicateEval (p .originalWord) (p .word) s)))

theorem rangeAllPrepared_state (p : RangeCursorPorts K) (s : CountdownStore K F) :
    (rangeAllPrepared p s).state = (s.state.1, true) := rfl

theorem rangeAllPrepared_stacks (p : RangeCursorPorts K) (s : CountdownStore K F)
    (hw : s.stk (p .word) = []) (hm : s.stk (p .mask) = []) (hc : s.stk (p .counter) = []) :
    (rangeAllPrepared p s).stk =
      Function.update (Function.update (Function.update s.stk (p .word) (s.stk (p .originalWord)))
        (p .mask) (s.stk (p .originalMask))) (p .counter) (s.stk (p .originalMask)) := by
  funext j
  by_cases hjc : j = p .counter <;> by_cases hjm : j = p .mask <;> by_cases hjw : j = p .word <;>
    simp_all [rangeAllPrepared, forestSyntaxStartOp, Op.apply, wordDuplicateEval]

theorem rangeAllPrepare_executes (p : RangeCursorPorts K) (s : CountdownStore K F)
    (ht : s.stk (p .temp) = []) (hm : s.stk (p .mask) = []) :
    (rangeAllPrepareRoutine p).Executes s (rangeAllPrepared p s)
      (3 * (s.stk (p .originalWord)).length + 6 * (s.stk (p .originalMask)).length + 10) := by
  let u := wordDuplicateEval (p .originalWord) (p .word) s
  let v := wordDuplicateEval (p .originalMask) (p .mask) u
  let w := wordDuplicateEval (p .mask) (p .counter) v
  have h1 := wordDuplicate_executes (p .originalWord) (p .temp) (p .word)
    (by simp) (by simp) (by simp) s ht
  have htu : u.stk (p .temp) = [] := by simp [u, wordDuplicateEval, ht]
  have h2 := wordDuplicate_executes (p .originalMask) (p .temp) (p .mask)
    (by simp) (by simp) (by simp) u htu
  have htv : v.stk (p .temp) = [] := by simp [v, u, wordDuplicateEval, ht]
  have h3 := wordDuplicate_executes (p .mask) (p .temp) (p .counter)
    (by simp) (by simp) (by simp) v htv
  have h4 := Atom.executes (forestSyntaxStartOp (K := K) (F := F)) w
  have he := RoutineComposition.seq_executes _ _ h1
    (RoutineComposition.seq_executes _ _ h2 (RoutineComposition.seq_executes _ _ h3 h4))
  convert he using 1 <;> simp [rangeAllPrepareRoutine, rangeAllPrepared, u, v, w,
    wordDuplicateEval, hm] <;> omega

theorem rangeBody_lengths (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) (j : K) :
    ((rangeBodyEval p m A s).stk j).length ≤ (s.stk j).length := by
  rw [rangeBody_stacks]
  by_cases hjm : j = p .mask
  · subst j
    simp only [Function.update_same]
    cases s.stk (p .mask) <;> simp
  · by_cases hjw : j = p .word
    · subst j
      simp only [Function.update_of_ne hjm, Function.update_same]
      cases s.stk (p .word) <;> simp
    · simp [hjm, hjw]

theorem rangeCountdownLoop_lengths (p : RangeCursorPorts K) (m A fuel : ℕ) :
    ∀ (s : CountdownStore K F) (j : K),
      ((countdownLoopEval (p .counter) (rangeBodyEval p m A) fuel s).stk j).length ≤ (s.stk j).length := by
  induction fuel with
  | zero => intro s j; exact le_refl _
  | succ fuel ih =>
      intro s j
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          have hpop : ((countdownPop (p .counter) s).stk j).length ≤ (s.stk j).length := by
            by_cases hj : j = p .counter
            · subst j
              rw [countdownPop_counter]
              cases s.stk (p .counter) <;> simp
            · simp [countdownPop, countdownPopOp, Op.apply, hj]
          have hbody := rangeBody_lengths p m A (countdownPop (p .counter) s) j
          have hi := ih (countdownPeek (p .counter) (rangeBodyEval p m A (countdownPop (p .counter) s))) j
          simpa only [countdownLoopEval, hg, ↓reduceIte] using hi.trans (hbody.trans hpop)

theorem rangeCountdown_lengths (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) (j : K) :
    ((rangeCountdownEval p m A s).stk j).length ≤ (s.stk j).length :=
  rangeCountdownLoop_lengths p m A (s.stk (p .counter)).length (countdownPeek (p .counter) s) j

theorem rangeCountdown_extra (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F)
    (j : K) (hjw : j ≠ p .word) (hjm : j ≠ p .mask) (hjc : j ≠ p .counter) :
    (rangeCountdownEval p m A s).stk j = s.stk j := by
  exact countdownLoop_preserves (p .counter) (rangeBodyEval p m A) (fun t => t.stk j)
    (fun _ => rfl)
    (by intro t; simp [countdownPop, countdownPopOp, Op.apply, hjc])
    (fun t => rangeBody_extra p m A t j hjw hjm)
    (s.stk (p .counter)).length (countdownPeek (p .counter) s)

theorem rangeCountdown_frame (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (rangeCountdownEval p m A s).state.1.1 = s.state.1.1 := by
  exact countdownLoop_preserves (p .counter) (rangeBodyEval p m A) (fun t => t.state.1.1)
    (fun _ => rfl) (fun _ => rfl) (rangeBody_frame p m A)
    (s.stk (p .counter)).length (countdownPeek (p .counter) s)

def rangeAllEval (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  clearManyEval (rangeCursorOwned p) (rangeCountdownEval p m A (rangeAllPrepared p s))

def rangeAllRoutine (p : RangeCursorPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (rangeAllPrepareRoutine p)
    (RoutineComposition.seq (rangeCountdownRoutine p) (clearManyRoutine (rangeCursorOwned p)))

def rangeAllResult (p : RangeCursorPorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨((s.state.1.1, false),
    (rawMarkedSuffixes (s.stk (p .originalWord)) (s.stk (p .originalMask))).all (rawRangeCheck m A)), s.stk⟩

/-- The COMPLETE paid all-range cursor: three restoring copies, the
instantiated physical countdown, per-query cleanup, and final cursor
cleanup on BOTH success and early rejection. No input grammar promise
is used, only bounded physical words and empty owned ports. -/
theorem rangeAll_executes (p : RangeCursorPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : RangeAllEntry p m A L s) :
    ∃ n ≤ L * (18 * L + 4 * m + 4 * A + 45) + 12 * L + 17,
      (rangeAllRoutine p).Executes s (rangeAllResult p m A s) n := by
  rcases hs with ⟨hL, hfit, hm, hA, hwork⟩
  have hf (j : RangeCursorPort) (hj : p j ∈ rangeAllWork p) : s.stk (p j) = [] := hwork _ hj
  have hw0 := hf .word (by simp [rangeAllWork])
  have hm0 := hf .mask (by simp [rangeAllWork])
  have hc0 := hf .counter (by simp [rangeAllWork])
  let u := rangeAllPrepared p s
  let v := rangeCountdownEval p m A u
  have hustk := rangeAllPrepared_stacks p s hw0 hm0 hc0
  have huw : u.stk (p .word) = s.stk (p .originalWord) := by simp [u, hustk]
  have hum : u.stk (p .mask) = s.stk (p .originalMask) := by simp [u, hustk]
  have huc : u.stk (p .counter) = s.stk (p .originalMask) := by simp [u, hustk]
  have hux (j : K) (hjw : j ≠ p .word) (hjm : j ≠ p .mask) (hjc : j ≠ p .counter) :
      u.stk j = s.stk j := by simp [u, hustk, hjw, hjm, hjc]
  have hu : RangeQueryInv p m A L u := by
    unfold RangeQueryInv
    rw [huw]
    refine ⟨hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hux _ (by simp) (by simp) (by simp)).trans hm
    · exact (hux _ (by simp) (by simp) (by simp)).trans hA
    all_goals
      rw [hux _ (by simp) (by simp) (by simp)]
      apply hwork
      simp [rangeAllWork]
  have hprep := rangeAllPrepare_executes p s (hf .temp (by simp [rangeAllWork])) hm0
  obtain ⟨a, ha, hrun, hvinv, hvguard, hvexhaust⟩ := rangeCountdown_executes p m A L u hu
  obtain ⟨b, hb, hclear⟩ := clearMany_executes (rangeCursorOwned p) v
  have hvw := rangeCountdown_lengths p m A u (p .word)
  have hvm := rangeCountdown_lengths p m A u (p .mask)
  have hvc := rangeCountdown_lengths p m A u (p .counter)
  rw [huw] at hvw
  rw [hum] at hvm
  rw [huc] at hvc
  have hmass : cleanupMass (rangeCursorOwned p) v ≤ 3 * L := by
    simp only [cleanupMass, rangeCursorOwned, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega
  have hresult : rangeAllEval p m A s = rangeAllResult p m A s := by
    apply countdownStore_ext
    · rw [rangeAllEval, clearMany_state]
      apply Prod.ext
      · exact Prod.ext (rangeCountdown_frame p m A u) hvguard
      · have hflag := rangeCountdown_flag p m A u (by rw [huc, hum]) (by rw [hum, huw]; exact hfit)
        simpa only [rangeAllPrepared_state, Bool.true_and, huw, hum] using hflag
    · funext j
      by_cases hj : j ∈ rangeCursorOwned p
      · rw [rangeAllEval, clearMany_member _ _ hj]
        have hj' : j ∈ rangeAllWork p := by
          simp only [rangeCursorOwned, List.mem_cons, List.mem_singleton] at hj
          rcases hj with rfl | rfl | rfl <;> simp [rangeAllWork]
        exact (hwork _ hj').symm
      · have hjw : j ≠ p .word := by intro h; apply hj; simp [rangeCursorOwned, h]
        have hjm : j ≠ p .mask := by intro h; apply hj; simp [rangeCursorOwned, h]
        have hjc : j ≠ p .counter := by intro h; apply hj; simp [rangeCursorOwned, h]
        rw [rangeAllEval, clearMany_outside _ _ hj, rangeCountdown_extra p m A u j hjw hjm hjc]
        exact hux j hjw hjm hjc
  have he := RoutineComposition.seq_executes _ _ hprep (RoutineComposition.seq_executes _ _ hrun hclear)
  rw [hresult] at he
  refine ⟨(3 * (s.stk (p .originalWord)).length + 6 * (s.stk (p .originalMask)).length + 10) + (a + b), ?_, he⟩
  rw [huc] at ha
  simp only [rangeCursorOwned, List.length_cons, List.length_nil] at hb
  have hM : (s.stk (p .originalMask)).length ≤ L := hfit.trans hL
  have hmul := Nat.mul_le_mul_right (18 * L + 4 * m + 4 * A + 45) hM
  omega

theorem forestSyntax_extra (p : ForestSyntaxPorts K) (s : CountdownStore K F) (j : K)
    (hjs : j ≠ p .source) (hjc : j ≠ p .count) (hjt : j ≠ p .tail)
    (hjp : j ≠ p .pending) (hjr : j ≠ p .reverse) (hjm : j ≠ p .mask) :
    (forestSyntaxEval p s).stk j = s.stk j := by
  let u := forestSyntaxAfterCount p s
  have hu : u.stk j = s.stk j :=
    guardedUnaryField_extra (p .source) (p .count) j hjs hjc (forestSyntaxStartOp.apply s)
  change (if u.state.2 then forestSyntaxSuccessEval p u else u).stk j = s.stk j
  cases hf : u.state.2 with
  | false => simpa only [forestSyntaxEval, hf, Bool.false_eq_true, ↓reduceIte] using hu
  | true =>
      let v := forestSyntaxPrepared p u
      have hv : v.stk j = u.stk j := by simp [v, forestSyntaxPrepared, wordDuplicateEval, hjp, hjt]
      have hx := treeMaskForward_preserves (forestSyntaxMaskPorts p) j hjs hjp hjr hjm
        v.stk v.state.1
        (rawForestMaskParse (v.stk (p .source)).length (v.stk (p .pending)).length (v.stk (p .source)))
      exact hx.2.2.2.trans (hv.trans hu)

theorem forestSyntax_frame (p : ForestSyntaxPorts K) (s : CountdownStore K F) :
    (forestSyntaxEval p s).state.1 = s.state.1 := by
  let u := forestSyntaxAfterCount p s
  have hu : u.state.1 = s.state.1 :=
    guardedUnaryField_frame (p .source) (p .count) (forestSyntaxStartOp.apply s)
  change (if u.state.2 then forestSyntaxSuccessEval p u else u).state.1 = s.state.1
  cases hf : u.state.2 with
  | false => simpa only [forestSyntaxEval, hf, Bool.false_eq_true, ↓reduceIte] using hu
  | true =>
      let v := forestSyntaxPrepared p u
      have hv : v.state.1 = u.state.1 := rfl
      have hx := treeMaskForward_preserves (forestSyntaxMaskPorts p) (p .count)
        (by simp [forestSyntaxMaskPorts]) (by simp [forestSyntaxMaskPorts])
        (by simp [forestSyntaxMaskPorts]) (by simp [forestSyntaxMaskPorts])
        v.stk v.state.1
        (rawForestMaskParse (v.stk (p .source)).length (v.stk (p .pending)).length (v.stk (p .source)))
      exact hx.1.trans (hv.trans hu)

theorem forestSyntax_success_bounds (p : ForestSyntaxPorts K) (L : ℕ) (s : CountdownStore K F)
    (hL : (s.stk (p .source)).length ≤ L)
    (hfresh : ∀ j : ForestSyntaxPort, j ≠ .source → s.stk (p j) = [])
    (hflag : (forestSyntaxEval p s).state.2 = true) :
    ((forestSyntaxEval p s).stk (p .tail)).length ≤ L ∧
      ((forestSyntaxEval p s).stk (p .mask)).length ≤ ((forestSyntaxEval p s).stk (p .tail)).length := by
  have ho := forestSyntax_observation p s hfresh
  have hp : originalForestSyntaxRead (s.stk (p .source)) =
      some (((forestSyntaxEval p s).stk (p .count)).length,
        (forestSyntaxEval p s).stk (p .tail), (forestSyntaxEval p s).stk (p .source),
        (forestSyntaxEval p s).stk (p .mask)) := by
    simpa only [forestSyntaxObservation, hflag, ↓reduceIte] using ho.symm
  obtain ⟨hc, hm⟩ := (originalForestSyntaxRead_success _ _ _ _ _).mp hp
  have hcount := readUnaryFrame_consumption _ _ _ hc
  have hmask := rawForestMaskParse_consumption _ _ _ _ hm
  exact ⟨by omega, by omega⟩

def originalTypedSyntaxRead (N m : ℕ) (bits : List Bool) : Option (ℕ × List Bool) :=
  (originalForestSyntaxRead bits).bind (fun data =>
    if forestMaskCellCheck N m data.2.1 data.2.2.2 then some (data.1, data.2.2.1) else none)

/-- Exact global typed grammar, BOTH directions, with arbitrary external
suffix. This is not a constructor-image promise or merely typed-to-raw
completeness. It quantifies over every original Boolean word. -/
theorem originalTypedSyntaxRead_success (N m : ℕ) (bits rest : List Bool) (q : ℕ) :
    originalTypedSyntaxRead N m bits = some (q, rest) ↔
      ∃ Ts : List (BTree (Cell N m)), Ts.length = q ∧
        readFramedList (readTargetTree N m) bits = some (Ts, rest) := by
  constructor
  · intro h
    cases hp : originalForestSyntaxRead bits with
    | none => simp [originalTypedSyntaxRead, hp] at h
    | some data =>
        rcases data with ⟨q', tail, rest', mask⟩
        cases hc : forestMaskCellCheck N m tail mask with
        | false => simp [originalTypedSyntaxRead, hp, hc] at h
        | true =>
            have he : (q', rest') = (q, rest) :=
              Option.some.inj (by simpa [originalTypedSyntaxRead, hp, hc] using h)
            have hq : q' = q := congrArg Prod.fst he
            have hr : rest' = rest := congrArg Prod.snd he
            subst q'
            subst rest'
            obtain ⟨hcount, hparse⟩ := (originalForestSyntaxRead_success _ _ _ _ _).mp hp
            exact observedForest_to_original N m q bits tail rest mask hcount hparse hc
  · rintro ⟨Ts, hlen, hp⟩
    obtain ⟨tail, mask, hcount, hparse, hcheck⟩ := originalForest_to_observed N m bits rest Ts hp
    have hraw := (originalForestSyntaxRead_success bits Ts.length tail rest mask).mpr ⟨hcount, hparse⟩
    simp [originalTypedSyntaxRead, hraw, hcheck, hlen]

inductive GrammarPort where
  | source | count | tail | pending | reverse | nodeMask | temp
  | word | mask | counter | cellSource | block | kind | rows | types | residue | subtrahend
  deriving DecidableEq, Fintype

abbrev GrammarPorts (K : Type) := GrammarPort ↪ K

@[simp] theorem grammarPorts_eq (p : GrammarPorts K) (a b : GrammarPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def grammarSyntaxPorts (p : GrammarPorts K) : ForestSyntaxPorts K where
  toFun := fun
    | .source => p .source
    | .count => p .count
    | .tail => p .tail
    | .pending => p .pending
    | .reverse => p .reverse
    | .mask => p .nodeMask
    | .temp => p .temp
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def grammarRangePorts (p : GrammarPorts K) : RangeCursorPorts K where
  toFun := fun
    | .originalWord => p .tail
    | .originalMask => p .nodeMask
    | .word => p .word
    | .mask => p .mask
    | .counter => p .counter
    | .source => p .cellSource
    | .block => p .block
    | .kind => p .kind
    | .rows => p .rows
    | .types => p .types
    | .temp => p .temp
    | .residue => p .residue
    | .subtrahend => p .subtrahend
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def GrammarEntry (p : GrammarPorts K) (N m L : ℕ) (s : CountdownStore K F) : Prop :=
  (s.stk (p .source)).length ≤ L ∧
  s.stk (p .rows) = List.replicate m true ∧
  s.stk (p .types) = List.replicate (N + m * N + 3) true ∧
  ∀ j : GrammarPort, j ≠ .source → j ≠ .rows → j ≠ .types → s.stk (p j) = []

def originalForestGrammarRoutine (p : GrammarPorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (forestSyntaxRoutine (grammarSyntaxPorts p))
    (RoutineComposition.seq
      (RoutineControl.branch Prod.snd (rangeAllRoutine (grammarRangePorts p)) (Atom.routine cleanupNoop))
      (Atom.routine countdownResetOp))

def originalForestGrammarEval (p : GrammarPorts K) (N m : ℕ) (s : CountdownStore K F) :=
  let u := forestSyntaxEval (grammarSyntaxPorts p) s
  countdownReset (if u.state.2 then rangeAllResult (grammarRangePorts p) m (N + m * N + 3) u else u)

theorem grammarEntry_syntax (p : GrammarPorts K) (N m L : ℕ) (s : CountdownStore K F)
    (hs : GrammarEntry p N m L s) :
    ∀ j : ForestSyntaxPort, j ≠ .source → s.stk (grammarSyntaxPorts p j) = [] := by
  intro j hj
  cases j <;> simp_all [grammarSyntaxPorts, GrammarEntry]

theorem grammarEntry_range_after_syntax (p : GrammarPorts K) (N m L : ℕ) (s : CountdownStore K F)
    (hs : GrammarEntry p N m L s)
    (hflag : (forestSyntaxEval (grammarSyntaxPorts p) s).state.2 = true) :
    RangeAllEntry (grammarRangePorts p) m (N + m * N + 3) L
      (forestSyntaxEval (grammarSyntaxPorts p) s) := by
  let u := forestSyntaxEval (grammarSyntaxPorts p) s
  have hsyntax := grammarEntry_syntax p N m L s hs
  have hbds := forestSyntax_success_bounds (grammarSyntaxPorts p) L s hs.1 hsyntax hflag
  have hx (j : GrammarPort) (hjs : j ≠ .source) (hjc : j ≠ .count) (hjt : j ≠ .tail)
      (hjp : j ≠ .pending) (hjr : j ≠ .reverse) (hjm : j ≠ .nodeMask) : u.stk (p j) = s.stk (p j) := by
    exact forestSyntax_extra (grammarSyntaxPorts p) s (p j)
      (by simpa [grammarSyntaxPorts] using hjs) (by simpa [grammarSyntaxPorts] using hjc)
      (by simpa [grammarSyntaxPorts] using hjt) (by simpa [grammarSyntaxPorts] using hjp)
      (by simpa [grammarSyntaxPorts] using hjr) (by simpa [grammarSyntaxPorts] using hjm)
  refine ⟨hbds.1, hbds.2, ?_, ?_, ?_⟩
  · exact (hx .rows (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs.2.1
  · exact (hx .types (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs.2.2.1
  · intro j hj
    simp only [rangeAllWork, List.mem_cons, List.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [hx _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hs.2.2.2 _ (by decide) (by decide) (by decide)

/-- One ORIGINAL framed forest and every finite leaf range, with both
malformed/count-too-large rejection and PAID all-node validation. This
is a composed grammar PHASE, not the complete target verifier. Physical
m and A are already established header operands; no valid tree, row
origin or canonical constructor shape is assumed. -/
theorem originalForestGrammar_executes (p : GrammarPorts K) (N m L : ℕ) (s : CountdownStore K F)
    (hs : GrammarEntry p N m L s) :
    ∃ n ≤ L * (18 * L + 4 * m + 4 * (N + m * N + 3) + 45) + 25 * L + 35,
      (originalForestGrammarRoutine p).Executes s (originalForestGrammarEval p N m s) n := by
  let u := forestSyntaxEval (grammarSyntaxPorts p) s
  obtain ⟨a, ha, hsyntax⟩ := forestSyntax_executes (grammarSyntaxPorts p) L s hs.1
    (grammarEntry_syntax p N m L s hs)
  cases hf : u.state.2 with
  | false =>
      have hbranch := RoutineControl.branch_false Prod.snd (rangeAllRoutine (grammarRangePorts p))
        (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop u)
      have hreset := Atom.executes (countdownResetOp (K := K) (F := F)) u
      have he := RoutineComposition.seq_executes _ _ hsyntax
        (RoutineComposition.seq_executes _ _ hbranch hreset)
      refine ⟨a + (2 + 1), by omega, ?_⟩
      simpa [originalForestGrammarRoutine, originalForestGrammarEval, hf, u,
        cleanupNoop, Op.apply, countdownReset] using he
  | true =>
      have hentry := grammarEntry_range_after_syntax p N m L s hs hf
      obtain ⟨b, hb, hrange⟩ := rangeAll_executes (grammarRangePorts p) m (N + m * N + 3) L u hentry
      have hbranch := RoutineControl.branch_true Prod.snd (rangeAllRoutine (grammarRangePorts p))
        (Atom.routine cleanupNoop) hf hrange
      have hreset := Atom.executes (countdownResetOp (K := K) (F := F))
        (rangeAllResult (grammarRangePorts p) m (N + m * N + 3) u)
      have he := RoutineComposition.seq_executes _ _ hsyntax
        (RoutineComposition.seq_executes _ _ hbranch hreset)
      refine ⟨a + ((b + 1) + 1), by omega, ?_⟩
      simpa only [originalForestGrammarRoutine, originalForestGrammarEval, hf,
        ↓reduceIte, u, countdownReset] using he

def originalForestGrammarObservation (p : GrammarPorts K) (s : CountdownStore K F) :
    Option (ℕ × List Bool) :=
  if s.state.2 then some ((s.stk (p .count)).length, s.stk (p .source)) else none

theorem originalForestGrammar_observation (p : GrammarPorts K) (N m : ℕ) (s : CountdownStore K F)
    (hfresh : ∀ j : ForestSyntaxPort, j ≠ .source → s.stk (grammarSyntaxPorts p j) = []) :
    originalForestGrammarObservation p (originalForestGrammarEval p N m s) =
      originalTypedSyntaxRead N m (s.stk (p .source)) := by
  let u := forestSyntaxEval (grammarSyntaxPorts p) s
  have ho : originalForestSyntaxRead (s.stk (p .source)) =
      if u.state.2 then some ((u.stk (p .count)).length,
        u.stk (p .tail), u.stk (p .source), u.stk (p .nodeMask)) else none := by
    simpa only [forestSyntaxObservation, grammarSyntaxPorts] using
      (forestSyntax_observation (grammarSyntaxPorts p) s hfresh).symm
  have hfun : rawRangeCheck m (N + m * N + 3) = legalSuffixCellCheck N m :=
    funext (rawRangeCheck_original N m)
  have hcheck : (rawMarkedSuffixes (u.stk (p .tail)) (u.stk (p .nodeMask))).all
      (rawRangeCheck m (N + m * N + 3)) =
      forestMaskCellCheck N m (u.stk (p .tail)) (u.stk (p .nodeMask)) := by
    rw [hfun]
    rfl
  unfold originalTypedSyntaxRead
  rw [ho]
  cases hf : u.state.2 <;>
    simp [originalForestGrammarObservation, originalForestGrammarEval, rangeAllResult,
      grammarRangePorts, countdownReset, countdownResetOp, Op.apply, hf, hcheck, u]

/-- FULL grammar-phase acceptance equivalence. On a successful path q
is the actual number of parsed original trees and rest the actual
remaining bytes; on any malformed or out-of-range path the observation
is none. No tree or source witness is supplied to the machine. -/
theorem originalForestGrammar_accepts_iff (p : GrammarPorts K) (N m L : ℕ)
    (s : CountdownStore K F) (hs : GrammarEntry p N m L s) (q : ℕ) (rest : List Bool) :
    originalForestGrammarObservation p (originalForestGrammarEval p N m s) = some (q, rest) ↔
      ∃ Ts : List (BTree (Cell N m)), Ts.length = q ∧
        readFramedList (readTargetTree N m) (s.stk (p .source)) = some (Ts, rest) := by
  rw [originalForestGrammar_observation p N m s (grammarEntry_syntax p N m L s hs)]
  exact originalTypedSyntaxRead_success N m (s.stk (p .source)) rest q

/- CURRENT WHOLE-CONTRACT STATUS, 23 October 2026:
The original one-count forest grammar, global finite-cell converse, and
PAID range cursor are now composed as one actual grammar phase in this
file, with an all-word observation theorem and a component time bound.
This removes the previous Boolean hcheck premise from THAT PHASE only.

The FULL bounded-pair verifier is NOT emitted here. Still required:
  * original pair split and bounded N/m/budget/A preparation;
  * target count=m+1, whole-target and whole-certificate consumption;
  * cell uniqueness, every-row markers/mixedness and global type coverage;
  * certificate uniqueness and two-way CELL-set equality;
  * every fixed clade, including internal composite-child clades;
  * actual per-internal-node distinct-TYPE objective, including root;
  * budget comparison, one answer bit, every owned port empty, finite
    control reset, and ONE polynomial for all accepted/rejected words.
VerifierMachineWitness therefore remains OPEN. EncodedSourceHardness
is a separate independent OPEN premise. All source is UNELABORATED;
no machine execution, compiler/kernel check or verified certificate.
-/

/-! ## The ORIGINAL unframed, whole single-tree certificate path -/

def wholeInputOp (source : K) : Op K Bool (CountdownState F) :=
  .peek source (fun st h => (st.1, st.2 && !h.isSome))

theorem wholeInput_true_iff (source : K) (s : CountdownStore K F) :
    ((wholeInputOp source).apply s).state.2 = true ↔ s.state.2 = true ∧ s.stk source = [] := by
  cases hw : s.stk source <;> cases hf : s.state.2 <;>
    simp [wholeInputOp, Op.apply, hw, hf]

def certificatePushOp (p : GrammarPorts K) (bit : Bool) : Op K Bool (CountdownState F) :=
  .push (p .source) (fun _ => bit)

/-- This TWO-INSTRUCTION internal adapter prepends U(1) to the current
certificate word. It does not change the external certificate encoding.
The equivalence to the original unframed parser is proved below. -/
def certificatePrefixRoutine (p : GrammarPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (certificatePushOp p false)) (Atom.routine (certificatePushOp p true))

def certificatePrefixEval (p : GrammarPorts K) (s : CountdownStore K F) :=
  (certificatePushOp p true).apply ((certificatePushOp p false).apply s)

theorem certificatePrefix_source (p : GrammarPorts K) (s : CountdownStore K F) :
    (certificatePrefixEval p s).stk (p .source) = unaryFrame 1 ++ s.stk (p .source) := by
  simp [certificatePrefixEval, certificatePushOp, Op.apply, unaryFrame]

theorem certificatePrefix_executes (p : GrammarPorts K) (s : CountdownStore K F) :
    (certificatePrefixRoutine p).Executes s (certificatePrefixEval p s) 2 :=
  RoutineComposition.seq_executes _ _ (Atom.executes (certificatePushOp p false) s)
    (Atom.executes (certificatePushOp p true) ((certificatePushOp p false).apply s))

theorem certificatePrefix_entry (p : GrammarPorts K) (N m L : ℕ) (s : CountdownStore K F)
    (hs : GrammarEntry p N m L s) : GrammarEntry p N m (L + 2) (certificatePrefixEval p s) := by
  rcases hs with ⟨hL, hm, hA, hwork⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [certificatePrefix_source]
    simp only [List.length_append, unaryFrame, List.length_replicate, List.length_singleton]
    omega
  · simpa [certificatePrefixEval, certificatePushOp, Op.apply] using hm
  · simpa [certificatePrefixEval, certificatePushOp, Op.apply] using hA
  · intro j hjs hjm hjA
    simpa [certificatePrefixEval, certificatePushOp, Op.apply, hjs] using hwork j hjs hjm hjA

def originalCertificateGrammarRoutine (p : GrammarPorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (certificatePrefixRoutine p)
    (RoutineComposition.seq (originalForestGrammarRoutine p) (Atom.routine (wholeInputOp (p .source))))

def originalCertificateGrammarEval (p : GrammarPorts K) (N m : ℕ) (s : CountdownStore K F) :=
  (wholeInputOp (p .source)).apply (originalForestGrammarEval p N m (certificatePrefixEval p s))

theorem originalCertificateGrammar_executes (p : GrammarPorts K) (N m L : ℕ)
    (s : CountdownStore K F) (hs : GrammarEntry p N m L s) :
    ∃ n ≤ (L + 2) * (18 * (L + 2) + 4 * m + 4 * (N + m * N + 3) + 45) + 25 * (L + 2) + 38,
      (originalCertificateGrammarRoutine p).Executes s (originalCertificateGrammarEval p N m s) n := by
  have hp := certificatePrefix_executes p s
  obtain ⟨n, hn, hg⟩ := originalForestGrammar_executes p N m (L + 2) (certificatePrefixEval p s)
    (certificatePrefix_entry p N m L s hs)
  have hw := Atom.executes (wholeInputOp (p .source))
    (originalForestGrammarEval p N m (certificatePrefixEval p s))
  have he := RoutineComposition.seq_executes _ _ hp (RoutineComposition.seq_executes _ _ hg hw)
  exact ⟨2 + (n + 1), by omega, he⟩

theorem oneFramedForest_read (N m : ℕ) (bits : List Bool) :
    readFramedList (readTargetTree N m) (unaryFrame 1 ++ bits) =
      (readTargetTree N m bits).map (fun p => ([p.1], p.2)) := by
  simp only [readFramedList, readUnaryFrame_encode, readMany]
  cases hp : readTargetTree N m bits with
  | none => rfl
  | some pair => rcases pair with ⟨T, rest⟩; rfl

theorem parseBitTree_asTarget (N m : ℕ) (bits : List Bool) :
    parseBitTree N m bits = (readTargetTree N m bits).bind
      (fun p => if p.2.isEmpty then some p.1 else none) := by
  unfold parseBitTree readTargetTree
  cases hp : parseBitPrefix N m bits.length bits with
  | none => rfl
  | some pair =>
      rcases pair with ⟨T, rest⟩
      cases rest <;> rfl

theorem oneFramedForest_whole_iff (N m : ℕ) (bits : List Bool) :
    (∃ Ts : List (BTree (Cell N m)),
      readFramedList (readTargetTree N m) (unaryFrame 1 ++ bits) = some (Ts, [])) ↔
      ∃ T : BTree (Cell N m), parseBitTree N m bits = some T := by
  rw [oneFramedForest_read]
  simp only [parseBitTree_asTarget]
  cases hp : readTargetTree N m bits with
  | none => simp
  | some pair =>
      rcases pair with ⟨T, rest⟩
      cases rest <;> simp

/-- Exact ORIGINAL certificate acceptance, for EVERY unframed Boolean
word. Extra trailing trees/bytes reject. The internal two-bit adapter
does not impose or require a new certificate format from the caller. -/
theorem originalCertificateGrammar_accepts_iff (p : GrammarPorts K) (N m L : ℕ)
    (s : CountdownStore K F) (hs : GrammarEntry p N m L s) :
    (originalCertificateGrammarEval p N m s).state.2 = true ↔
      ∃ T : BTree (Cell N m), parseBitTree N m (s.stk (p .source)) = some T := by
  let u := certificatePrefixEval p s
  let v := originalForestGrammarEval p N m u
  have hu := certificatePrefix_entry p N m L s hs
  change ((wholeInputOp (p .source)).apply v).state.2 = true ↔ _
  rw [wholeInput_true_iff]
  constructor
  · rintro ⟨hflag, hrest⟩
    have ho : originalForestGrammarObservation p v = some ((v.stk (p .count)).length, []) := by
      simp [originalForestGrammarObservation, hflag, hrest]
    obtain ⟨Ts, hlen, hparse⟩ :=
      (originalForestGrammar_accepts_iff p N m (L + 2) u hu (v.stk (p .count)).length []).mp ho
    apply (oneFramedForest_whole_iff N m (s.stk (p .source))).mp
    exact ⟨Ts, by simpa only [u, certificatePrefix_source] using hparse⟩
  · intro htree
    obtain ⟨Ts, hparse⟩ := (oneFramedForest_whole_iff N m (s.stk (p .source))).mpr htree
    have hparse' : readFramedList (readTargetTree N m) (u.stk (p .source)) = some (Ts, []) := by
      simpa only [u, certificatePrefix_source] using hparse
    have ho := (originalForestGrammar_accepts_iff p N m (L + 2) u hu Ts.length []).mpr ⟨Ts, rfl, hparse'⟩
    cases hflag : v.state.2 with
    | false => simp [originalForestGrammarObservation, hflag, v] at ho
    | true =>
        have he : ((v.stk (p .count)).length, v.stk (p .source)) = (Ts.length, []) :=
          Option.some.inj (by simpa only [originalForestGrammarObservation, hflag, ↓reduceIte] using ho)
        exact ⟨hflag, congrArg Prod.snd he⟩

/- The original certificate grammar is now joined to the SAME paid
forest/range phase. This is still grammar validity, NOT certificate cell
uniqueness, set equality, refinement, objective acceptance or the final
clean verifier halt. The remaining whole-contract clauses above retain
their full force. New source after the 00:32 public snapshot is local and
UNELABORATED until separately preserved and checked. -/

/-! ## Original target forest count and whole-word guards -/

theorem forestSyntax_count (p : ForestSyntaxPorts K) (s : CountdownStore K F) :
    (forestSyntaxEval p s).stk (p .count) = (forestSyntaxAfterCount p s).stk (p .count) := by
  let u := forestSyntaxAfterCount p s
  change (if u.state.2 then forestSyntaxSuccessEval p u else u).stk (p .count) = u.stk (p .count)
  cases hf : u.state.2 with
  | false => simp [hf]
  | true =>
      let v := forestSyntaxPrepared p u
      have hx := treeMaskForward_preserves (forestSyntaxMaskPorts p) (p .count)
        (by simp [forestSyntaxMaskPorts]) (by simp [forestSyntaxMaskPorts])
        (by simp [forestSyntaxMaskPorts]) (by simp [forestSyntaxMaskPorts])
        v.stk v.state.1
        (rawForestMaskParse (v.stk (p .source)).length (v.stk (p .pending)).length (v.stk (p .source)))
      have hv : v.stk (p .count) = u.stk (p .count) := by
        simp [v, forestSyntaxPrepared, wordDuplicateEval]
      simpa only [hf, ↓reduceIte] using hx.2.2.2.trans hv

theorem originalForestGrammar_stacks (p : GrammarPorts K) (N m : ℕ) (s : CountdownStore K F) :
    (originalForestGrammarEval p N m s).stk = (forestSyntaxEval (grammarSyntaxPorts p) s).stk := by
  unfold originalForestGrammarEval
  split <;> rfl

theorem originalForestGrammar_extra (p : GrammarPorts K) (N m : ℕ) (s : CountdownStore K F) (j : GrammarPort)
    (hjs : j ≠ .source) (hjc : j ≠ .count) (hjt : j ≠ .tail)
    (hjp : j ≠ .pending) (hjr : j ≠ .reverse) (hjm : j ≠ .nodeMask) :
    (originalForestGrammarEval p N m s).stk (p j) = s.stk (p j) := by
  rw [originalForestGrammar_stacks]
  exact forestSyntax_extra (grammarSyntaxPorts p) s (p j)
    (by simpa [grammarSyntaxPorts] using hjs) (by simpa [grammarSyntaxPorts] using hjc)
    (by simpa [grammarSyntaxPorts] using hjt) (by simpa [grammarSyntaxPorts] using hjp)
    (by simpa [grammarSyntaxPorts] using hjr) (by simpa [grammarSyntaxPorts] using hjm)

theorem originalForestGrammar_count_bounded (p : GrammarPorts K) (N m L : ℕ)
    (s : CountdownStore K F) (hs : GrammarEntry p N m L s) :
    IsUnaryWord ((originalForestGrammarEval p N m s).stk (p .count)) ∧
      ((originalForestGrammarEval p N m s).stk (p .count)).length ≤ L := by
  rw [originalForestGrammar_stacks]
  change IsUnaryWord ((forestSyntaxEval (grammarSyntaxPorts p) s).stk (grammarSyntaxPorts p .count)) ∧ _
  rw [forestSyntax_count]
  have hc : s.stk (p .count) = [] := hs.2.2.2 .count (by decide) (by decide) (by decide)
  have hu := guardedUnaryField_output_unary (p .source) (p .count) (forestSyntaxStartOp.apply s) hc
  have hb := guardedUnaryField_output_bound (p .source) (p .count) (forestSyntaxStartOp.apply s) hc
  exact ⟨hu, hb.trans hs.1⟩

def targetCountComparePorts (p : GrammarPorts K) : CellComparePorts K where
  toFun := fun
    | .left => p .cellSource
    | .right => p .count
    | .temp => p .temp
    | .residue => p .residue
    | .subtrahend => p .subtrahend
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def targetCountPushOp (p : GrammarPorts K) : Op K Bool (CountdownState F) :=
  .push (p .cellSource) (fun _ => true)

def targetCountExpected (p : GrammarPorts K) (s : CountdownStore K F) :=
  (targetCountPushOp p).apply (wordDuplicateEval (p .rows) (p .cellSource) s)

def targetForestEndRoutine (p : GrammarPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine (p .rows) (p .temp) (p .cellSource))
    (RoutineComposition.seq (Atom.routine (targetCountPushOp p))
      (RoutineComposition.seq (guardedCellCompareRoutine (targetCountComparePorts p) .eq)
        (RoutineComposition.seq (clearStackRoutine (p .cellSource)) (Atom.routine (wholeInputOp (p .source))))))

def targetForestEndEval (p : GrammarPorts K) (m q : ℕ) (s : CountdownStore K F) :=
  (wholeInputOp (p .source)).apply (clearStackEval (p .cellSource)
    (guardedCellCompareEval .eq (m + 1) q (targetCountExpected p s)))

theorem targetForestEnd_result (p : GrammarPorts K) (m q : ℕ) (s : CountdownStore K F)
    (hc : s.stk (p .cellSource) = []) :
    targetForestEndEval p m q s = cellCompareFlagStore
      ((s.state.2 && decide (q = m + 1)) && !(s.stk (p .source)).head?.isSome) s := by
  apply countdownStore_ext
  · cases hf : s.state.2 <;>
      simp [targetForestEndEval, targetCountExpected, targetCountPushOp, wholeInputOp,
        guardedCellCompareEval, cellCompareFlagStore, cellCompareAnswer, clearStackEval,
        wordDuplicateEval, Op.apply, hf]
  · funext j
    by_cases hj : j = p .cellSource <;> cases hf : s.state.2 <;>
      simp_all [targetForestEndEval, targetCountExpected, targetCountPushOp, wholeInputOp,
        guardedCellCompareEval, cellCompareFlagStore, clearStackEval, wordDuplicateEval, Op.apply]

theorem targetForestEnd_executes (p : GrammarPorts K) (m q : ℕ) (s : CountdownStore K F)
    (hm : s.stk (p .rows) = List.replicate m true)
    (hq : s.stk (p .count) = List.replicate q true)
    (hc : s.stk (p .cellSource) = []) (ht : s.stk (p .temp) = [])
    (hr : s.stk (p .residue) = []) (hd : s.stk (p .subtrahend) = []) :
    ∃ n ≤ 8 * m + 4 * q + 21,
      (targetForestEndRoutine p).Executes s (targetForestEndEval p m q s) n := by
  let u := wordDuplicateEval (p .rows) (p .cellSource) s
  let v := targetCountExpected p s
  let w := guardedCellCompareEval .eq (m + 1) q v
  have h1 := wordDuplicate_executes (p .rows) (p .temp) (p .cellSource)
    (by simp) (by simp) (by simp) s ht
  rw [hm, List.length_replicate] at h1
  have h2 := Atom.executes (targetCountPushOp p) u
  have hvleft : v.stk (p .cellSource) = List.replicate (m + 1) true := by
    simp [v, targetCountExpected, targetCountPushOp, wordDuplicateEval, Op.apply, hm, hc, List.replicate_succ]
  have hvq : v.stk (p .count) = List.replicate q true := by
    simp [v, targetCountExpected, targetCountPushOp, wordDuplicateEval, Op.apply, hq]
  have hvx (j : GrammarPort) (hj : j ≠ .cellSource) : v.stk (p j) = s.stk (p j) := by
    simp [v, targetCountExpected, targetCountPushOp, wordDuplicateEval, Op.apply, hj]
  obtain ⟨a, ha, h3⟩ := guardedCellCompare_executes (targetCountComparePorts p) .eq (m + 1) q v
    hvleft hvq ((hvx .residue (by decide)).trans hr) ((hvx .subtrahend (by decide)).trans hd)
    ((hvx .temp (by decide)).trans ht)
  have h4 := clearStack_executes (p .cellSource) w
  have hwlen : (w.stk (p .cellSource)).length = m + 1 := by
    rw [guardedCellCompare_stacks, hvleft, List.length_replicate]
  rw [hwlen] at h4
  have h5 := Atom.executes (wholeInputOp (p .source)) (clearStackEval (p .cellSource) w)
  have he := RoutineComposition.seq_executes _ _ h1
    (RoutineComposition.seq_executes _ _ h2 (RoutineComposition.seq_executes _ _ h3
      (RoutineComposition.seq_executes _ _ h4 h5)))
  exact ⟨(3 * m + 3) + (1 + (a + ((m + 1 + 1) + 1))), by omega, he⟩

theorem targetForestEnd_accepts_iff (p : GrammarPorts K) (m : ℕ) (s : CountdownStore K F)
    (hc : s.stk (p .cellSource) = []) :
    (targetForestEndEval p m (s.stk (p .count)).length s).state.2 = true ↔
      originalForestGrammarObservation p s = some (m + 1, []) := by
  rw [targetForestEnd_result p m _ s hc]
  cases hf : s.state.2 <;> cases hw : s.stk (p .source) <;>
    simp [cellCompareFlagStore, originalForestGrammarObservation, hf, hw]

def originalTargetForestRoutine (p : GrammarPorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (originalForestGrammarRoutine p) (targetForestEndRoutine p)

def originalTargetForestEval (p : GrammarPorts K) (N m : ℕ) (s : CountdownStore K F) :=
  let u := originalForestGrammarEval p N m s
  targetForestEndEval p m (u.stk (p .count)).length u

theorem originalTargetForest_executes (p : GrammarPorts K) (N m L : ℕ)
    (s : CountdownStore K F) (hs : GrammarEntry p N m L s) :
    ∃ n ≤ L * (18 * L + 4 * m + 4 * (N + m * N + 3) + 45) + 29 * L + 8 * m + 56,
      (originalTargetForestRoutine p).Executes s (originalTargetForestEval p N m s) n := by
  let u := originalForestGrammarEval p N m s
  have hbds := originalForestGrammar_count_bounded p N m L s hs
  have hq : u.stk (p .count) = List.replicate (u.stk (p .count)).length true := hbds.1
  have hum : u.stk (p .rows) = List.replicate m true :=
    (originalForestGrammar_extra p N m s .rows (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.2.1
  have huwork (j : GrammarPort) (hjs : j ≠ .source) (hjc : j ≠ .count) (hjt : j ≠ .tail)
      (hjp : j ≠ .pending) (hjr : j ≠ .reverse) (hjm : j ≠ .nodeMask)
      (hjrows : j ≠ .rows) (hjtypes : j ≠ .types) : u.stk (p j) = [] :=
    (originalForestGrammar_extra p N m s j hjs hjc hjt hjp hjr hjm).trans
      (hs.2.2.2 j hjs hjrows hjtypes)
  obtain ⟨a, ha, hgrammar⟩ := originalForestGrammar_executes p N m L s hs
  obtain ⟨b, hb, hend⟩ := targetForestEnd_executes p m (u.stk (p .count)).length u hum hq
    (huwork .cellSource (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (huwork .temp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (huwork .residue (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (huwork .subtrahend (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  exact ⟨a + b, by omega, RoutineComposition.seq_executes _ _ hgrammar hend⟩

/-- Precisely the ORIGINAL target FOREST requirements: m+1 typed trees
and no trailing bytes. This does NOT assert N>0, m>=2, uniqueness,
markers, mixedness, coverage, certificate refinement or objective. -/
theorem originalTargetForest_accepts_iff (p : GrammarPorts K) (N m L : ℕ)
    (s : CountdownStore K F) (hs : GrammarEntry p N m L s) :
    (originalTargetForestEval p N m s).state.2 = true ↔
      ∃ Ts : List (BTree (Cell N m)), Ts.length = m + 1 ∧
        readFramedList (readTargetTree N m) (s.stk (p .source)) = some (Ts, []) := by
  let u := originalForestGrammarEval p N m s
  have hc : u.stk (p .cellSource) = [] :=
    (originalForestGrammar_extra p N m s .cellSource (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      (hs.2.2.2 .cellSource (by decide) (by decide) (by decide))
  change (targetForestEndEval p m (u.stk (p .count)).length u).state.2 = true ↔ _
  rw [targetForestEnd_accepts_iff p m u hc]
  exact originalForestGrammar_accepts_iff p N m L s hs (m + 1) []

/-! ## The same controller: exact CELL matching, not type matching

The local result below is a SEARCH-CONTINUATION flag: false means that
this candidate matched, so a search may stop. It is not a global failure.
The later existential join must negate it before using it as membership.
Both coordinates are physically compared. A nonleaf/malformed suffix is
not a match. Only genuine-node masks may be used for the tree semantics.
-/

inductive MatchCursorPort where
  | cursor (port : RangeCursorPort)
  | wantedBlock | wantedKind
  deriving DecidableEq, Fintype

abbrev MatchCursorPorts (K : Type) := MatchCursorPort ↪ K

@[simp] theorem matchCursorPorts_eq (p : MatchCursorPorts K) (a b : MatchCursorPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def matchRangePorts (p : MatchCursorPorts K) : RangeCursorPorts K where
  toFun := fun j => p (.cursor j)
  inj' := by intro a b h; simpa using p.injective h

def matchComparePorts (p : MatchCursorPorts K) (kind : Bool) : CellComparePorts K where
  toFun := fun
    | .left => if kind then p .wantedKind else p .wantedBlock
    | .right => if kind then p (.cursor .kind) else p (.cursor .block)
    | .temp => p (.cursor .temp)
    | .residue => p (.cursor .residue)
    | .subtrahend => p (.cursor .subtrahend)
  inj' := by intro a b h; cases kind <;> cases a <;> cases b <;> simp_all

def rawCellMatch (m A B T : ℕ) (bits : List Bool) : Bool :=
  match filterRawLeafCell m A (readRawLeafCell bits) with
  | none => false
  | some (c, _) => decide (c.1 = B) && decide (c.2 = T)

def searchFlipOp : Op K Bool (CountdownState F) :=
  .load (fun st => (st.1, !st.2))

def matchLeafCompared (p : MatchCursorPorts K) (m A B T : ℕ) (s : CountdownStore K F) :=
  let v := rangeLeafParsed (matchRangePorts p) m A s
  guardedCellCompareEval .eq T (v.stk (p (.cursor .kind))).length
    (guardedCellCompareEval .eq B (v.stk (p (.cursor .block))).length v)

def matchLeafEval (p : MatchCursorPorts K) (m A B T : ℕ) (s : CountdownStore K F) :=
  searchFlipOp.apply (clearManyEval (rangeQueryOwned (matchRangePorts p))
    (matchLeafCompared p m A B T s))

def matchLeafRoutine (p : MatchCursorPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  let r := matchRangePorts p
  RoutineComposition.seq (wordDuplicateRoutine (r .word) (r .temp) (r .source))
    (RoutineComposition.seq (typedLeafCellRoutine (rangeTypedPorts r))
      (RoutineComposition.seq (guardedCellCompareRoutine (matchComparePorts p false) .eq)
        (RoutineComposition.seq (guardedCellCompareRoutine (matchComparePorts p true) .eq)
          (RoutineComposition.seq (clearManyRoutine (rangeQueryOwned r))
            (Atom.routine searchFlipOp)))))

def MatchQueryInv (p : MatchCursorPorts K) (m A B T L : ℕ) (s : CountdownStore K F) : Prop :=
  RangeQueryInv (matchRangePorts p) m A L s ∧
  s.stk (p .wantedBlock) = List.replicate B true ∧
  s.stk (p .wantedKind) = List.replicate T true

theorem matchLeafCompared_stacks (p : MatchCursorPorts K) (m A B T : ℕ)
    (s : CountdownStore K F) :
    (matchLeafCompared p m A B T s).stk = (rangeLeafParsed (matchRangePorts p) m A s).stk := by
  unfold matchLeafCompared
  rw [guardedCellCompare_stacks, guardedCellCompare_stacks]

theorem matchLeafCompared_flag (p : MatchCursorPorts K) (m A B T : ℕ)
    (s : CountdownStore K F) (hz : s.stk (p (.cursor .source)) = []) :
    (matchLeafCompared p m A B T s).state.2 = rawCellMatch m A B T (s.stk (p (.cursor .word))) := by
  let r := matchRangePorts p
  let u := rangeLeafPrepared r s
  let v := rangeLeafParsed r m A s
  have hu : u.stk (r .source) = s.stk (r .word) := by
    simp [u, r, rangeLeafPrepared, wordDuplicateEval, matchRangePorts, hz]
  have ho := typedLeafCell_observation (rangeTypedPorts r) m A u
  rw [hu] at ho
  unfold rawCellMatch
  rw [← ho]
  change (guardedCellCompareEval .eq T (v.stk (r .kind)).length
    (guardedCellCompareEval .eq B (v.stk (r .block)).length v)).state.2 = _
  rw [guardedCellCompare_flag, guardedCellCompare_flag]
  cases hf : v.state.2 <;>
    simp [rawLeafCellObservation, typedRawCellPorts, rangeTypedPorts,
      cellCompareAnswer, hf, r, matchRangePorts, Bool.and_assoc]

theorem matchLeaf_result (p : MatchCursorPorts K) (m A B T L : ℕ) (s : CountdownStore K F)
    (hs : MatchQueryInv p m A B T L s) :
    matchLeafEval p m A B T s = cellCompareFlagStore
      (!rawCellMatch m A B T (s.stk (p (.cursor .word)))) s := by
  let r := matchRangePorts p
  have hrestore := rangeLeaf_result r m A L s hs.1
  have hstack : (clearManyEval (rangeQueryOwned r) (matchLeafCompared p m A B T s)).stk =
      (rangeLeafEval r m A s).stk := by
    change (clearManyEval (rangeQueryOwned r) (matchLeafCompared p m A B T s)).stk =
      (clearManyEval (rangeQueryOwned r) (rangeLeafParsed r m A s)).stk
    simp only [rangeQueryOwned, clearManyEval, clearStackEval, matchLeafCompared_stacks]
  have hframe : (matchLeafCompared p m A B T s).state.1 = s.state.1 := by
    unfold matchLeafCompared
    rw [guardedCellCompare_frame, guardedCellCompare_frame]
    exact typedLeafCell_frame (rangeTypedPorts r) m A (rangeLeafPrepared r s)
  apply countdownStore_ext
  · change ((clearManyEval (rangeQueryOwned r) (matchLeafCompared p m A B T s)).state.1,
      !(clearManyEval (rangeQueryOwned r) (matchLeafCompared p m A B T s)).state.2) = _
    rw [clearMany_state, hframe, matchLeafCompared_flag p m A B T s hs.1.2.2.2.1]
    rfl
  · change (clearManyEval (rangeQueryOwned r) (matchLeafCompared p m A B T s)).stk = s.stk
    rw [hstack, hrestore]
    rfl

theorem matchLeaf_executes (p : MatchCursorPorts K) (m A B T L : ℕ) (s : CountdownStore K F)
    (hs : MatchQueryInv p m A B T L s) :
    ∃ n ≤ 26 * L + 4 * m + 4 * A + 4 * B + 4 * T + 57,
      (matchLeafRoutine p).Executes s
        (cellCompareFlagStore (!rawCellMatch m A B T (s.stk (p (.cursor .word)))) s) n := by
  rcases hs with ⟨hquery, hB, hT⟩
  rcases hquery with ⟨hL, hm, hA, hsource, hb, hk, ht, hr, hd⟩
  let r := matchRangePorts p
  let u := rangeLeafPrepared r s
  let v := rangeLeafParsed r m A s
  let w := guardedCellCompareEval .eq B (v.stk (r .block)).length v
  let z := matchLeafCompared p m A B T s
  have huSource : u.stk (r .source) = s.stk (r .word) := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, hsource]
  have huExtra (j : K) (hj : j ≠ r .source) : u.stk j = s.stk j := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, hj]
  have huL : (u.stk (r .source)).length ≤ L := by rw [huSource]; exact hL
  have hbu := (huExtra (r .block) (by simp)).trans hb
  have hku := (huExtra (r .kind) (by simp)).trans hk
  have h1 := wordDuplicate_executes (r .word) (r .temp) (r .source)
    (by simp) (by simp) (by simp) s ht
  obtain ⟨a, ha, h2⟩ := typedLeafCell_executes (rangeTypedPorts r) m A L u huL
    ((huExtra _ (by simp)).trans hm) ((huExtra _ (by simp)).trans hA)
    hbu hku ((huExtra _ (by simp)).trans ht)
    ((huExtra _ (by simp)).trans hr) ((huExtra _ (by simp)).trans hd)
  have hbds := rawLeafCell_bounds (typedRawCellPorts (rangeTypedPorts r)) L u huL hbu hku
  have hunary := rawLeafCell_unary (typedRawCellPorts (rangeTypedPorts r)) u hbu hku
  have hvstk : v.stk = (rawLeafCellEval (typedRawCellPorts (rangeTypedPorts r)) u).stk :=
    typedLeafCell_stacks (rangeTypedPorts r) m A u
  have hvx (j : K) (hjs : j ≠ r .source) (hjb : j ≠ r .block) (hjk : j ≠ r .kind) :
      v.stk j = s.stk j := by
    rw [hvstk, rawLeafCell_extra (typedRawCellPorts (rangeTypedPorts r)) j hjs hjb hjk]
    exact huExtra j hjs
  have hvb : v.stk (r .block) = List.replicate (v.stk (r .block)).length true := by
    simpa only [hvstk, typedRawCellPorts, rangeTypedPorts] using hunary.1
  have hvk : v.stk (r .kind) = List.replicate (v.stk (r .kind)).length true := by
    simpa only [hvstk, typedRawCellPorts, rangeTypedPorts] using hunary.2
  have hvB : v.stk (p .wantedBlock) = List.replicate B true :=
    (hvx _ (by simp [r, matchRangePorts]) (by simp [r, matchRangePorts])
      (by simp [r, matchRangePorts])).trans hB
  have hvT : v.stk (p .wantedKind) = List.replicate T true :=
    (hvx _ (by simp [r, matchRangePorts]) (by simp [r, matchRangePorts])
      (by simp [r, matchRangePorts])).trans hT
  have hvt := (hvx (r .temp) (by simp) (by simp) (by simp)).trans ht
  have hvr := (hvx (r .residue) (by simp) (by simp) (by simp)).trans hr
  have hvd := (hvx (r .subtrahend) (by simp) (by simp) (by simp)).trans hd
  obtain ⟨b, hbt, h3⟩ := guardedCellCompare_executes (matchComparePorts p false) .eq
    B (v.stk (r .block)).length v
    (by simpa [matchComparePorts] using hvB) (by simpa [matchComparePorts, r, matchRangePorts] using hvb)
    (by simpa [matchComparePorts, r, matchRangePorts] using hvr)
    (by simpa [matchComparePorts, r, matchRangePorts] using hvd)
    (by simpa [matchComparePorts, r, matchRangePorts] using hvt)
  have hwstk : w.stk = v.stk := guardedCellCompare_stacks .eq B _ v
  obtain ⟨c, hc, h4⟩ := guardedCellCompare_executes (matchComparePorts p true) .eq
    T (v.stk (r .kind)).length w
    (by simpa [matchComparePorts, hwstk] using hvT)
    (by simpa [matchComparePorts, hwstk, r, matchRangePorts] using hvk)
    (by simpa [matchComparePorts, hwstk, r, matchRangePorts] using hvr)
    (by simpa [matchComparePorts, hwstk, r, matchRangePorts] using hvd)
    (by simpa [matchComparePorts, hwstk, r, matchRangePorts] using hvt)
  obtain ⟨d, hdtime, h5⟩ := clearMany_executes (rangeQueryOwned r) z
  have h6 := Atom.executes (searchFlipOp (K := K) (F := F)) (clearManyEval (rangeQueryOwned r) z)
  have hmass : cleanupMass (rangeQueryOwned r) z ≤ 3 * L := by
    have hsum := Nat.add_le_add (Nat.add_le_add hbds.1 hbds.2.1) hbds.2.2
    simp only [cleanupMass, rangeQueryOwned, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, z, matchLeafCompared_stacks, hvstk]
    simp only [typedRawCellPorts, rangeTypedPorts] at hsum
    omega
  have hbL : (v.stk (r .block)).length ≤ L := by
    simpa only [hvstk, typedRawCellPorts, rangeTypedPorts] using hbds.2.1
  have hkL : (v.stk (r .kind)).length ≤ L := by
    simpa only [hvstk, typedRawCellPorts, rangeTypedPorts] using hbds.2.2
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ h4
      (RoutineComposition.seq_executes _ _ h5 h6))))
  change (matchLeafRoutine p).Executes s (matchLeafEval p m A B T s) _ at he
  rw [matchLeaf_result p m A B T L s ⟨⟨hL, hm, hA, hsource, hb, hk, ht, hr, hd⟩, hB, hT⟩] at he
  refine ⟨3 * (s.stk (r .word)).length + 3 + (a + (b + (c + (d + 1)))), ?_, he⟩
  simp only [rangeQueryOwned, List.length_cons, List.length_nil] at hdtime
  omega

/-! ## One paid mask-loop schema, with actual query implementations

The contract below is a composition interface, not a machine existence
assumption. Its cell-match instance is supplied below. No final verifier
may leave a query contract or a complete nested scan as an external axiom.
-/

def maskedBodyEval (p : RangeCursorPorts K) (q : List Bool → Bool) (s : CountdownStore K F) :
    CountdownStore K F :=
  let selected := (s.stk (p .mask)).head?.getD false
  ⟨((s.state.1.1, selected), if selected then q (s.stk (p .word)) else s.state.2),
    Function.update (Function.update s.stk (p .word) (s.stk (p .word)).tail)
      (p .mask) (s.stk (p .mask)).tail⟩

def maskedBodyRoutine (p : RangeCursorPorts K)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (rangeSelectMaskOp p))
    (RoutineComposition.seq
      (RoutineControl.branch (fun st => st.1.2) query (Atom.routine cleanupNoop))
      (RoutineComposition.seq (Atom.routine (rangePopWordOp p)) (Atom.routine (rangePopMaskOp p))))

structure MaskedQueryContract (p : RangeCursorPorts K)
    (query : Routine (fun _ : K => Bool) (CountdownState F))
    (q : List Bool → Bool) (I : (K → List Bool) → Prop) (M : ℕ) : Prop where
  positive : 1 ≤ M
  query_executes : ∀ s, I s.stk → s.state.1.2 = true → ∃ n ≤ M,
    query.Executes s (cellCompareFlagStore (q (s.stk (p .word))) s) n
  cursor_closed : ∀ stk, I stk →
    I (Function.update (Function.update stk (p .word) (stk (p .word)).tail)
      (p .mask) (stk (p .mask)).tail)
  counter_closed : ∀ stk, I stk → I (Function.update stk (p .counter) (stk (p .counter)).tail)

theorem maskedBody_executes (p : RangeCursorPorts K)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) (q : List Bool → Bool)
    (I : (K → List Bool) → Prop) (M : ℕ) (h : MaskedQueryContract p query q I M)
    (s : CountdownStore K F) (hs : I s.stk) :
    ∃ n ≤ M + 4, (maskedBodyRoutine p query).Executes s (maskedBodyEval p q s) n := by
  let u := (rangeSelectMaskOp p).apply s
  have hpeek := Atom.executes (rangeSelectMaskOp p) s
  cases hg : u.state.1.2 with
  | false =>
      have hbranch := RoutineControl.branch_false (fun st : CountdownState F => st.1.2)
        query (Atom.routine cleanupNoop) hg (Atom.executes cleanupNoop u)
      have hp1 := Atom.executes (rangePopWordOp p) u
      have hp2 := Atom.executes (rangePopMaskOp p) ((rangePopWordOp p).apply u)
      have he := RoutineComposition.seq_executes _ _ hpeek
        (RoutineComposition.seq_executes _ _ hbranch (RoutineComposition.seq_executes _ _ hp1 hp2))
      have hM : 1 ≤ M := h.positive
      refine ⟨5, by omega, ?_⟩
      simpa [maskedBodyRoutine, maskedBodyEval, u, rangeSelectMaskOp,
        rangePopWordOp, rangePopMaskOp, cleanupNoop, Op.apply, hg] using he
  | true =>
      obtain ⟨n, hn, hquery⟩ := h.query_executes u hs hg
      have hbranch := RoutineControl.branch_true (fun st : CountdownState F => st.1.2)
        query (Atom.routine cleanupNoop) hg hquery
      let v := cellCompareFlagStore (q (u.stk (p .word))) u
      have hp1 := Atom.executes (rangePopWordOp p) v
      have hp2 := Atom.executes (rangePopMaskOp p) ((rangePopWordOp p).apply v)
      have he := RoutineComposition.seq_executes _ _ hpeek
        (RoutineComposition.seq_executes _ _ hbranch (RoutineComposition.seq_executes _ _ hp1 hp2))
      refine ⟨1 + ((n + 1) + (1 + 1)), by omega, ?_⟩
      simpa [maskedBodyRoutine, maskedBodyEval, u, v, rangeSelectMaskOp,
        rangePopWordOp, rangePopMaskOp, cellCompareFlagStore, Op.apply, hg] using he

theorem maskedBody_extra (p : RangeCursorPorts K) (q : List Bool → Bool)
    (s : CountdownStore K F) (j : K) (hjw : j ≠ p .word) (hjm : j ≠ p .mask) :
    (maskedBodyEval p q s).stk j = s.stk j := by simp [maskedBodyEval, hjw, hjm]

def maskedCountdownContract (p : RangeCursorPorts K)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) (q : List Bool → Bool)
    (I : (K → List Bool) → Prop) (M : ℕ) (h : MaskedQueryContract p query q I M) :
    CountdownContract (p .counter) (maskedBodyRoutine p query) (maskedBodyEval p q)
      (fun s => I s.stk) (M + 4) where
  peek_closed s hs := hs
  pop_closed s hs hg := h.counter_closed s.stk hs
  body_closed s hs := h.cursor_closed s.stk hs
  reset_closed s hs := hs
  counter_preserved s hs := maskedBody_extra p q s (p .counter) (by simp) (by simp)
  body_executes s hs := maskedBody_executes p query q I M h s hs

def maskedCountdownRoutine (p : RangeCursorPorts K)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) :=
  countdownRoutine (p .counter) (maskedBodyRoutine p query)

def maskedCountdownEval (p : RangeCursorPorts K) (q : List Bool → Bool) (s : CountdownStore K F) :=
  countdownEval (p .counter) (maskedBodyEval p q) s

theorem maskedCountdown_executes (p : RangeCursorPorts K)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) (q : List Bool → Bool)
    (I : (K → List Bool) → Prop) (M : ℕ) (h : MaskedQueryContract p query q I M)
    (s : CountdownStore K F) (hs : I s.stk) :
    ∃ n ≤ (s.stk (p .counter)).length * (M + 7) + 3,
      (maskedCountdownRoutine p query).Executes s (maskedCountdownEval p q s) n ∧
      I (maskedCountdownEval p q s).stk ∧
      (maskedCountdownEval p q s).state.1.2 = false ∧
      ((maskedCountdownEval p q s).state.2 = true →
        (maskedCountdownEval p q s).stk (p .counter) = []) := by
  simpa only [maskedCountdownRoutine, maskedCountdownEval, Nat.add_assoc] using
    countdownRoutine_executes (p .counter) (maskedBodyRoutine p query) (maskedBodyEval p q)
      (fun s => I s.stk) (M + 4) (maskedCountdownContract p query q I M h) s hs

theorem maskedCountdownLoop_flag (p : RangeCursorPorts K) (q : List Bool → Bool) (fuel : ℕ) :
    ∀ s : CountdownStore K F,
      (s.stk (p .counter)).length = (s.stk (p .mask)).length →
      (s.stk (p .mask)).length ≤ (s.stk (p .word)).length →
      (s.stk (p .counter)).length ≤ fuel →
      s.state.1.2 = (s.stk (p .counter)).head?.isSome →
      (countdownLoopEval (p .counter) (maskedBodyEval p q) fuel s).state.2 =
        s.state.2 && (rawMarkedSuffixes (s.stk (p .word)) (s.stk (p .mask))).all q := by
  induction fuel with
  | zero =>
      intro s hsame hfit hlen hpeek
      have hm : s.stk (p .mask) = [] := List.eq_nil_of_length_eq_zero (by omega)
      cases hw : s.stk (p .word) <;> simp [countdownLoopEval, rawMarkedSuffixes, hm, hw]
  | succ fuel ih =>
      intro s hsame hfit hlen hpeek
      cases hf : s.state.2 with
      | false => simp [countdownLoopEval, countdownGuard, hf]
      | true =>
          cases hm : s.stk (p .mask) with
          | nil =>
              have hc : s.stk (p .counter) = [] :=
                List.eq_nil_of_length_eq_zero (by simpa [hm] using hsame)
              cases hw : s.stk (p .word) <;>
                simp [countdownLoopEval, countdownGuard, hpeek, hc, hm, hw, rawMarkedSuffixes, hf]
          | cons mark mask =>
              cases hw : s.stk (p .word) with
              | nil => simp [hm, hw] at hfit
              | cons bit bits =>
                  have hc : (s.stk (p .counter)).head?.isSome = true := by
                    cases hcs : s.stk (p .counter) with
                    | nil => simp [hcs, hm] at hsame
                    | cons c cs => rfl
                  have hg : countdownGuard s.state = true := by simp [countdownGuard, hpeek, hc, hf]
                  let u := countdownPeek (p .counter) (maskedBodyEval p q (countdownPop (p .counter) s))
                  have huw : u.stk (p .word) = bits := by
                    simp [u, countdownPeek, maskedBodyEval, countdownPop, countdownPopOp, Op.apply, hw]
                  have hum : u.stk (p .mask) = mask := by
                    simp [u, countdownPeek, maskedBodyEval, countdownPop, countdownPopOp, Op.apply, hm]
                  have huc : u.stk (p .counter) = (s.stk (p .counter)).tail := by
                    change (maskedBodyEval p q (countdownPop (p .counter) s)).stk (p .counter) = _
                    rw [maskedBody_extra p q _ (p .counter) (by simp) (by simp)]
                    exact countdownPop_counter (p .counter) s
                  have huf : u.state.2 = if mark then q (bit :: bits) else true := by
                    simp [u, countdownPeek, maskedBodyEval, countdownPop, countdownPopOp,
                      countdownPeekOp, Op.apply, hm, hw, hf]
                  have husame : (u.stk (p .counter)).length = (u.stk (p .mask)).length := by
                    rw [huc, hum]
                    cases hcs : s.stk (p .counter) with
                    | nil => simp [hcs, hm] at hsame
                    | cons c cs => simpa [hcs, hm] using hsame
                  have hufit : (u.stk (p .mask)).length ≤ (u.stk (p .word)).length := by
                    rw [hum, huw]; simpa [hm, hw] using hfit
                  have hulen : (u.stk (p .counter)).length ≤ fuel := by
                    rw [huc]
                    cases hcs : s.stk (p .counter) with
                    | nil => simp
                    | cons c cs => simpa [hcs] using hlen
                  have hi := ih u husame hufit hulen (countdownPeek_control (p .counter) _)
                  simp only [countdownLoopEval, hg, ↓reduceIte]
                  rw [hi, huf, huw, hum]
                  cases mark <;> simp [hm, hw, hf, rawMarkedSuffixes]

theorem maskedCountdown_flag (p : RangeCursorPorts K) (q : List Bool → Bool) (s : CountdownStore K F)
    (hsame : (s.stk (p .counter)).length = (s.stk (p .mask)).length)
    (hfit : (s.stk (p .mask)).length ≤ (s.stk (p .word)).length) :
    (maskedCountdownEval p q s).state.2 =
      s.state.2 && (rawMarkedSuffixes (s.stk (p .word)) (s.stk (p .mask))).all q :=
  maskedCountdownLoop_flag p q (s.stk (p .counter)).length
    (countdownPeek (p .counter) s) hsame hfit (le_refl _) (countdownPeek_control (p .counter) s)

theorem maskedBody_lengths (p : RangeCursorPorts K) (q : List Bool → Bool)
    (s : CountdownStore K F) (j : K) :
    ((maskedBodyEval p q s).stk j).length ≤ (s.stk j).length := by
  by_cases hjm : j = p .mask
  · subst j; simp only [maskedBodyEval, Function.update_same]
    cases s.stk (p .mask) <;> simp
  · by_cases hjw : j = p .word
    · subst j; simp only [maskedBodyEval, Function.update_of_ne hjm, Function.update_same]
      cases s.stk (p .word) <;> simp
    · simp [maskedBodyEval, hjm, hjw]

theorem maskedCountdownLoop_lengths (p : RangeCursorPorts K) (q : List Bool → Bool) (fuel : ℕ) :
    ∀ (s : CountdownStore K F) (j : K),
      ((countdownLoopEval (p .counter) (maskedBodyEval p q) fuel s).stk j).length ≤ (s.stk j).length := by
  induction fuel with
  | zero => intro s j; exact le_refl _
  | succ fuel ih =>
      intro s j
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          have hpop : ((countdownPop (p .counter) s).stk j).length ≤ (s.stk j).length := by
            by_cases hj : j = p .counter
            · subst j; rw [countdownPop_counter]; cases s.stk (p .counter) <;> simp
            · simp [countdownPop, countdownPopOp, Op.apply, hj]
          have hb := maskedBody_lengths p q (countdownPop (p .counter) s) j
          have hi := ih (countdownPeek (p .counter) (maskedBodyEval p q (countdownPop (p .counter) s))) j
          simpa only [countdownLoopEval, hg, ↓reduceIte] using hi.trans (hb.trans hpop)

theorem maskedCountdown_extra (p : RangeCursorPorts K) (q : List Bool → Bool)
    (s : CountdownStore K F) (j : K) (hjw : j ≠ p .word) (hjm : j ≠ p .mask) (hjc : j ≠ p .counter) :
    (maskedCountdownEval p q s).stk j = s.stk j :=
  countdownLoop_preserves (p .counter) (maskedBodyEval p q) (fun t => t.stk j)
    (fun _ => rfl) (by intro t; simp [countdownPop, countdownPopOp, Op.apply, hjc])
    (fun t => maskedBody_extra p q t j hjw hjm)
    (s.stk (p .counter)).length (countdownPeek (p .counter) s)

theorem maskedCountdown_frame (p : RangeCursorPorts K) (q : List Bool → Bool) (s : CountdownStore K F) :
    (maskedCountdownEval p q s).state.1.1 = s.state.1.1 :=
  countdownLoop_preserves (p .counter) (maskedBodyEval p q) (fun t => t.state.1.1)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (s.stk (p .counter)).length (countdownPeek (p .counter) s)

def maskedAllRoutine (p : RangeCursorPorts K)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) :=
  RoutineComposition.seq (rangeAllPrepareRoutine p)
    (RoutineComposition.seq (maskedCountdownRoutine p query) (clearManyRoutine (rangeCursorOwned p)))

def maskedAllEval (p : RangeCursorPorts K) (q : List Bool → Bool) (s : CountdownStore K F) :=
  clearManyEval (rangeCursorOwned p) (maskedCountdownEval p q (rangeAllPrepared p s))

def maskedAllResult (p : RangeCursorPorts K) (q : List Bool → Bool) (s : CountdownStore K F) :
    CountdownStore K F :=
  ⟨((s.state.1.1, false),
    (rawMarkedSuffixes (s.stk (p .originalWord)) (s.stk (p .originalMask))).all q), s.stk⟩

theorem maskedAll_executes (p : RangeCursorPorts K)
    (query : Routine (fun _ : K => Bool) (CountdownState F)) (q : List Bool → Bool)
    (I : (K → List Bool) → Prop) (M L : ℕ) (h : MaskedQueryContract p query q I M)
    (s : CountdownStore K F)
    (hL : (s.stk (p .originalWord)).length ≤ L)
    (hfit : (s.stk (p .originalMask)).length ≤ (s.stk (p .originalWord)).length)
    (hw0 : s.stk (p .word) = []) (hm0 : s.stk (p .mask) = [])
    (hc0 : s.stk (p .counter) = []) (ht0 : s.stk (p .temp) = [])
    (hi : I (rangeAllPrepared p s).stk) :
    ∃ n ≤ L * (M + 7) + 12 * L + 17,
      (maskedAllRoutine p query).Executes s (maskedAllResult p q s) n := by
  let u := rangeAllPrepared p s
  let v := maskedCountdownEval p q u
  have hustk := rangeAllPrepared_stacks p s hw0 hm0 hc0
  have huw : u.stk (p .word) = s.stk (p .originalWord) := by simp [u, hustk]
  have hum : u.stk (p .mask) = s.stk (p .originalMask) := by simp [u, hustk]
  have huc : u.stk (p .counter) = s.stk (p .originalMask) := by simp [u, hustk]
  have hux (j : K) (hjw : j ≠ p .word) (hjm : j ≠ p .mask) (hjc : j ≠ p .counter) :
      u.stk j = s.stk j := by simp [u, hustk, hjw, hjm, hjc]
  have hprep := rangeAllPrepare_executes p s ht0 hm0
  obtain ⟨a, ha, hrun, hvinv, hvguard, hvexhaust⟩ := maskedCountdown_executes p query q I M h u hi
  obtain ⟨b, hb, hclear⟩ := clearMany_executes (rangeCursorOwned p) v
  have hvlen (j : K) : (v.stk j).length ≤ (u.stk j).length :=
    maskedCountdownLoop_lengths p q (u.stk (p .counter)).length (countdownPeek (p .counter) u) j
  have hvw := hvlen (p .word)
  have hvm := hvlen (p .mask)
  have hvc := hvlen (p .counter)
  rw [huw] at hvw
  rw [hum] at hvm
  rw [huc] at hvc
  have hmass : cleanupMass (rangeCursorOwned p) v ≤ 3 * L := by
    simp only [cleanupMass, rangeCursorOwned, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hresult : maskedAllEval p q s = maskedAllResult p q s := by
    apply countdownStore_ext
    · rw [maskedAllEval, clearMany_state]
      apply Prod.ext
      · exact Prod.ext (maskedCountdown_frame p q u) hvguard
      · have hf := maskedCountdown_flag p q u (by rw [huc, hum]) (by rw [hum, huw]; exact hfit)
        simpa only [rangeAllPrepared_state, Bool.true_and, huw, hum] using hf
    · funext j
      by_cases hj : j ∈ rangeCursorOwned p
      · rw [maskedAllEval, clearMany_member _ _ hj]
        simp only [rangeCursorOwned, List.mem_cons, List.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl
        · exact hw0.symm
        · exact hm0.symm
        · exact hc0.symm
      · have hjw : j ≠ p .word := by intro he; apply hj; simp [rangeCursorOwned, he]
        have hjm : j ≠ p .mask := by intro he; apply hj; simp [rangeCursorOwned, he]
        have hjc : j ≠ p .counter := by intro he; apply hj; simp [rangeCursorOwned, he]
        rw [maskedAllEval, clearMany_outside _ _ hj, maskedCountdown_extra p q u j hjw hjm hjc]
        exact hux j hjw hjm hjc
  have he := RoutineComposition.seq_executes _ _ hprep (RoutineComposition.seq_executes _ _ hrun hclear)
  rw [hresult] at he
  refine ⟨(3 * (s.stk (p .originalWord)).length + 6 * (s.stk (p .originalMask)).length + 10) + (a + b), ?_, he⟩
  rw [huc] at ha
  simp only [rangeCursorOwned, List.length_cons, List.length_nil] at hb
  have hmul := Nat.mul_le_mul_right (M + 7) (hfit.trans hL)
  omega

def MatchStackInv (p : MatchCursorPorts K) (m A B T L : ℕ) (stk : K → List Bool) : Prop :=
  ((stk (p (.cursor .word))).length ≤ L ∧
    stk (p (.cursor .rows)) = List.replicate m true ∧
    stk (p (.cursor .types)) = List.replicate A true ∧
    stk (p (.cursor .source)) = [] ∧ stk (p (.cursor .block)) = [] ∧
    stk (p (.cursor .kind)) = [] ∧ stk (p (.cursor .temp)) = [] ∧
    stk (p (.cursor .residue)) = [] ∧ stk (p (.cursor .subtrahend)) = []) ∧
  stk (p .wantedBlock) = List.replicate B true ∧ stk (p .wantedKind) = List.replicate T true

def matchMaskedContract (p : MatchCursorPorts K) (m A B T L : ℕ) :
    MaskedQueryContract (matchRangePorts p) (matchLeafRoutine p)
      (fun bits => !rawCellMatch m A B T bits) (MatchStackInv p m A B T L)
      (26 * L + 4 * m + 4 * A + 4 * B + 4 * T + 57) where
  positive := by omega
  query_executes s hs hselected := matchLeaf_executes p m A B T L s hs
  cursor_closed stk hs := by
    have ht : (stk (p (.cursor .word))).tail.length ≤ (stk (p (.cursor .word))).length := by
      cases stk (p (.cursor .word)) <;> simp
    unfold MatchStackInv at hs ⊢
    simpa [matchRangePorts] using And.intro (And.intro (ht.trans hs.1.1) hs.1.2) hs.2
  counter_closed stk hs := by
    simpa [MatchStackInv, matchRangePorts] using hs

def MatchAllEntry (p : MatchCursorPorts K) (m A B T L : ℕ) (s : CountdownStore K F) : Prop :=
  RangeAllEntry (matchRangePorts p) m A L s ∧
  s.stk (p .wantedBlock) = List.replicate B true ∧ s.stk (p .wantedKind) = List.replicate T true

theorem matchAll_prepared_inv (p : MatchCursorPorts K) (m A B T L : ℕ)
    (s : CountdownStore K F) (hs : MatchAllEntry p m A B T L s) :
    MatchStackInv p m A B T L (rangeAllPrepared (matchRangePorts p) s).stk := by
  rcases hs with ⟨⟨hL, hfit, hm, hA, hwork⟩, hB, hT⟩
  let r := matchRangePorts p
  have hf (j : RangeCursorPort) (hj : r j ∈ rangeAllWork r) : s.stk (r j) = [] := hwork _ hj
  have hustk := rangeAllPrepared_stacks r s (hf .word (by simp [rangeAllWork]))
    (hf .mask (by simp [rangeAllWork])) (hf .counter (by simp [rangeAllWork]))
  rw [hustk]
  unfold MatchStackInv
  have hsource := hf .source (by simp [rangeAllWork])
  have hblock := hf .block (by simp [rangeAllWork])
  have hkind := hf .kind (by simp [rangeAllWork])
  have htemp := hf .temp (by simp [rangeAllWork])
  have hresidue := hf .residue (by simp [rangeAllWork])
  have hsub := hf .subtrahend (by simp [rangeAllWork])
  simpa [r, matchRangePorts] using
    And.intro (And.intro hL ⟨hm, hA, hsource, hblock, hkind, htemp, hresidue, hsub⟩) ⟨hB, hT⟩

theorem all_not_flip_eq_any {X : Type} (xs : List X) (q : X → Bool) :
    !(xs.all (fun x => !q x)) = xs.any q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.all_cons, List.any_cons]
      cases hq : q x <;> simp [hq, ih]

def cellMembershipRoutine (p : MatchCursorPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (maskedAllRoutine (matchRangePorts p) (matchLeafRoutine p))
    (Atom.routine searchFlipOp)

def cellMembershipResult (p : MatchCursorPorts K) (m A B T : ℕ) (s : CountdownStore K F) :
    CountdownStore K F :=
  ⟨((s.state.1.1, false),
    (rawMarkedSuffixes (s.stk (p (.cursor .originalWord)))
      (s.stk (p (.cursor .originalMask)))).any (rawCellMatch m A B T)), s.stk⟩

/-- Fully instantiated membership search: real typed queries and TWO
physical comparisons, all cursor/query copying and cleanup paid. This
returns a local membership Boolean; it does NOT absorb an earlier global
rejection. The enclosing verifier must branch/store that global flag. -/
theorem cellMembership_executes (p : MatchCursorPorts K) (m A B T L : ℕ)
    (s : CountdownStore K F) (hs : MatchAllEntry p m A B T L s) :
    ∃ n ≤ L * (26 * L + 4 * m + 4 * A + 4 * B + 4 * T + 64) + 12 * L + 18,
      (cellMembershipRoutine p).Executes s (cellMembershipResult p m A B T s) n := by
  let r := matchRangePorts p
  let q := fun bits => !rawCellMatch m A B T bits
  have hf (j : RangeCursorPort) (hj : r j ∈ rangeAllWork r) : s.stk (r j) = [] := hs.1.2.2.2.2 _ hj
  obtain ⟨n, hn, he⟩ := maskedAll_executes r (matchLeafRoutine p) q (MatchStackInv p m A B T L)
    (26 * L + 4 * m + 4 * A + 4 * B + 4 * T + 57) L (matchMaskedContract p m A B T L) s
    hs.1.1 hs.1.2.1 (hf .word (by simp [rangeAllWork])) (hf .mask (by simp [rangeAllWork]))
    (hf .counter (by simp [rangeAllWork])) (hf .temp (by simp [rangeAllWork]))
    (matchAll_prepared_inv p m A B T L s hs)
  have hflip := Atom.executes (searchFlipOp (K := K) (F := F)) (maskedAllResult r q s)
  have hresult : searchFlipOp.apply (maskedAllResult r q s) = cellMembershipResult p m A B T s := by
    apply countdownStore_ext
    · simp [maskedAllResult, cellMembershipResult, searchFlipOp, Op.apply,
        r, q, matchRangePorts, all_not_flip_eq_any]
    · rfl
  rw [hresult] at hflip
  exact ⟨n + 1, by omega, RoutineComposition.seq_executes _ _ he hflip⟩

def rawCellCodeMatch (m A B T : ℕ) (c : ℕ × ℕ) : Bool :=
  decide (c.1 ≤ m ∧ c.2 < A) && (decide (c.1 = B) && decide (c.2 = T))

theorem rawCellMatch_leaf (m A B T : ℕ) (c : ℕ × ℕ) (rest : List Bool) :
    rawCellMatch m A B T (rawCellTreeBits (.leaf c) ++ rest) = rawCellCodeMatch m A B T c := by
  by_cases hv : c.1 ≤ m ∧ c.2 < A <;>
    simp [rawCellMatch, rawCellCodeMatch, rawCellTreeBits, readRawLeafCell,
      filterRawLeafCell, List.append_assoc, readUnaryFrame_encode, hv]

theorem rawCellMatch_node (m A B T : ℕ) (l r : BTree (ℕ × ℕ)) (rest : List Bool) :
    rawCellMatch m A B T (rawCellTreeBits (.node l r) ++ rest) = false := rfl

theorem rawCellMatch_views (m A B T : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool) :
    ((rawNodeViews R rest).map rawViewSuffix).any (rawCellMatch m A B T) =
      (scanLeaves R).any (rawCellCodeMatch m A B T) := by
  induction R generalizing rest with
  | leaf c =>
      simpa only [rawNodeViews, rawViewSuffix, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, Bool.or_false, scanLeaves] using rawCellMatch_leaf m A B T c rest
  | node l r ihl ihr =>
      simp only [rawNodeViews, List.map_cons, List.map_append, List.any_cons,
        List.any_append, rawViewSuffix, rawCellMatch_node, Bool.false_or, scanLeaves, ihl, ihr]

/-- This semantic identity covers ALL raw trees, even out-of-range cells;
the range filter is explicit. No typed-tree or constructor assumption is
needed to identify what the emitted search actually returns. -/
theorem rawCellMembership_forest (m A B T : ℕ) (Rs : List (BTree (ℕ × ℕ)))
    (rest : List Bool) :
    (rawMarkedSuffixes (rawForestWord Rs ++ rest) (rawForestNodeMask Rs)).any
      (rawCellMatch m A B T) =
      (Rs.flatMap scanLeaves).any (rawCellCodeMatch m A B T) := by
  induction Rs with
  | nil => simp [rawForestWord, rawForestNodeMask, rawMarkedSuffixes]
  | cons R Rs ih =>
      simp only [rawForestWord, rawForestNodeMask, List.flatMap_cons, List.append_assoc]
      rw [rawMarkedSuffixes_tree, List.any_append, rawCellMatch_views]
      rw [ih, List.any_append]

theorem rawCellMembership_forest_valid (N m B T : ℕ) (Rs : List (BTree (ℕ × ℕ)))
    (rest : List Bool) (hv : ∀ R ∈ Rs, rawTreeValid N m R) :
    (rawMarkedSuffixes (rawForestWord Rs ++ rest) (rawForestNodeMask Rs)).any
      (rawCellMatch m (N + m * N + 3) B T) = true ↔
      (B, T) ∈ Rs.flatMap scanLeaves := by
  rw [rawCellMembership_forest, List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hmatch⟩
    have he : (c.1 ≤ m ∧ c.2 < N + m * N + 3) ∧ c.1 = B ∧ c.2 = T := by
      simpa only [rawCellCodeMatch, Bool.and_eq_true, decide_eq_true_eq] using hmatch
    have heq : c = (B, T) := Prod.ext he.2.1 he.2.2
    simpa only [heq] using hc
  · intro hc
    obtain ⟨R, hR, hleaf⟩ := List.mem_flatMap.mp hc
    have hvalid := hv R hR (B, T) hleaf
    refine ⟨(B, T), hc, ?_⟩
    simp [rawCellCodeMatch, rawCellValid] at hvalid ⊢
    exact hvalid

/-- The forest witness here is RECONSTRUCTED from the parser and range
observations, not supplied as a validity promise. These observations are
exactly the ones provided by the grammar phase above. The final bounded
pair controller still has to place both phases in its common inventory. -/
theorem cellMembership_observed_forest (p : MatchCursorPorts K) (N m q B T : ℕ)
    (s : CountdownStore K F) (rest : List Bool)
    (hparse : rawForestMaskParse (s.stk (p (.cursor .originalWord))).length q
      (s.stk (p (.cursor .originalWord))) = some (rest, s.stk (p (.cursor .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.cursor .originalWord)))
      (s.stk (p (.cursor .originalMask))) = true) :
    ∃ Rs : List (BTree (ℕ × ℕ)), Rs.length = q ∧
      s.stk (p (.cursor .originalWord)) = rawForestWord Rs ++ rest ∧
      s.stk (p (.cursor .originalMask)) = rawForestNodeMask Rs ∧
      (∀ R ∈ Rs, rawTreeValid N m R) ∧
      ((cellMembershipResult p m (N + m * N + 3) B T s).state.2 = true ↔
        (B, T) ∈ Rs.flatMap scanLeaves) := by
  obtain ⟨Rs, hq, hword, hmask⟩ :=
    (rawForestMaskParse_all_words (s.stk (p (.cursor .originalWord))) rest
      (s.stk (p (.cursor .originalMask))) q).mp hparse
  have hv : ∀ R ∈ Rs, rawTreeValid N m R :=
    (forestMaskCellCheck_iff N m Rs rest).mp (by simpa only [← hword, ← hmask] using hcheck)
  refine ⟨Rs, hq, hword, hmask, hv, ?_⟩
  change (rawMarkedSuffixes (s.stk (p (.cursor .originalWord)))
    (s.stk (p (.cursor .originalMask)))).any (rawCellMatch m (N + m * N + 3) B T) = true ↔ _
  rw [hword, hmask]
  exact rawCellMembership_forest_valid N m B T Rs rest hv

/- The actual membership scan is now an instantiated use of the common
paid cursor, not a Boolean oracle. It alone does not implement target or
certificate uniqueness, bidirectional cell sets, the all/exists clade
nest, marker/mixedness/coverage guards, or distinct-type score. Those
remain full-controller composition obligations. The final machine and
encoded-source-hardness premises are still independent and unclosed. -/

end PolytomyReductionModel.WholeVerifierController
