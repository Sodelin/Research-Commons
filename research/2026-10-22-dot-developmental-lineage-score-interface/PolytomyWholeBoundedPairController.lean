/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

WORK IN PROGRESS toward the ONE ORIGINAL bounded-pair verifier controller.
This file supplies its composed original forest grammar/range PHASE,
not the full controller or VerifierMachineWitness. The target forest
has ONE unary count and concatenated self-delimiting binary trees. There
is no length frame per tree and no enclosing-row/block-tag restriction.

The range cursor is emitted, instantiated and cleaned below. The full
headers/guards/clades/score/final cleanup remain to be composed. No
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

end PolytomyReductionModel.WholeVerifierController
