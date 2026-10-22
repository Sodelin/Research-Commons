/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No execution or verification certificate.

Direct bounded range-filter enumeration, left-comb bit emission and fixed
comb-cost arithmetic for the SAME canonical constructor. No generic tree
or clade engine is required merely to serialize its fixed child combs.
The complete actual-D_lambda reduction is retained through byte equality.
-/
import PolytomySaturatedVerifier
import Mathlib.Data.Finset.Sort

namespace PolytomyReductionModel
universe u v

def directBlockCodes {N m : ℕ} (D : MSSCInstance N m) (b : Block m) : List ℕ :=
  (List.range (N + m * N + 3)).filter
    (fun n => decide (n ∈ (blockTypes D b).image (terminalCode N m)))

theorem directBlockCodes_eq {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    directBlockCodes D b = (canonicalTypeList D b).map (terminalCode N m) := by
  classical
  letI := terminalCodeOrder N m
  let e : Terminal N m ↪ ℕ := ⟨terminalCode N m, terminalCode_injective N m⟩
  have hmap : (canonicalTypeList D b).map (terminalCode N m) =
      ((blockTypes D b).map e).sort (· ≤ ·) := by
    exact Finset.map_sort e (blockTypes D b) (· ≤ ·) (· ≤ ·)
      (fun _ _ _ _ => Iff.rfl)
  have hfin : (directBlockCodes D b).toFinset = (blockTypes D b).map e := by
    ext n
    simp only [directBlockCodes, List.mem_toFinset, List.mem_filter,
      List.mem_range, decide_eq_true_eq, Finset.mem_image, Finset.mem_map]
    constructor
    · rintro ⟨hn, s, hs, he⟩
      exact ⟨s, hs, he⟩
    · rintro ⟨s, hs, he⟩
      have hcode : terminalCode N m s = n := he
      exact ⟨hcode ▸ terminalCode_lt N m s, s, hs, hcode⟩
  have hnodup : (directBlockCodes D b).Nodup :=
    List.Nodup.filter _ (List.nodup_range _)
  have hpair : (directBlockCodes D b).Pairwise (· ≤ ·) := by
    have hr : (List.range (N + m * N + 3)).Pairwise (· ≤ ·) := by
      simpa only [Finset.sort_range] using
        (Finset.pairwise_sort (Finset.range (N + m * N + 3)) (· ≤ ·))
    exact List.Pairwise.filter _ hr
  have hsort : ((blockTypes D b).map e).sort (· ≤ ·) = directBlockCodes D b := by
    rw [← hfin]
    exact (List.toFinset_sort (r := (· ≤ ·)) hnodup).mpr hpair
  exact (hmap.trans hsort).symm

theorem directBlockCodes_length {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    (directBlockCodes D b).length = (canonicalBlockCells D b).length := by
  simp only [directBlockCodes_eq, canonicalBlockCells, List.length_map]

theorem directBlockCodes_length_le {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    (directBlockCodes D b).length ≤ N + m * N + 3 := by
  have h := List.length_filter_le
    (fun n => decide (n ∈ (blockTypes D b).image (terminalCode N m)))
    (List.range (N + m * N + 3))
  simpa only [directBlockCodes, List.length_range] using h

theorem treeBits_attach {N m : ℕ} (T : BTree (Cell N m)) (xs : List (Cell N m)) :
    treeBits (attach T xs) =
      List.replicate xs.length false ++ treeBits T ++ xs.flatMap (fun a => treeBits (.leaf a)) := by
  induction xs generalizing T with
  | nil => simp [attach]
  | cons a xs ih =>
      rw [attach, ih]
      simp only [treeBits, List.length_cons, List.flatMap_cons]
      rw [List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append, List.cons_append]

theorem treeBits_combFrom {N m : ℕ} (a : Cell N m) (xs : List (Cell N m)) :
    treeBits (combFrom a xs) =
      List.replicate xs.length false ++ (a :: xs).flatMap (fun c => true :: cellBits c) := by
  simpa only [combFrom, foldl_node_eq_attach, List.flatMap_cons, treeBits,
    List.append_assoc] using treeBits_attach (BTree.leaf a) xs

theorem canonicalBlockCells_nonempty {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    canonicalBlockCells D b ≠ [] := by
  have h : (b, marker0 N m) ∈ canonicalBlockCells D b := by
    simp [canonicalBlockCells, mem_canonicalTypeList, marker0_mem_blockTypes]
  intro he
  simp [he] at h

theorem canonicalBlockTree_bits {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    treeBits (canonicalBlockTree D b) =
      List.replicate ((canonicalBlockCells D b).length - 1) false ++
        (canonicalBlockCells D b).flatMap (fun a => true :: cellBits a) := by
  have hn := canonicalBlockCells_nonempty D b
  cases h : canonicalBlockCells D b with
  | nil => exact (hn h).elim
  | cons a xs =>
      simpa only [canonicalBlockTree, h, List.headD_cons, List.tail_cons,
        List.length_cons, Nat.add_sub_cancel] using treeBits_combFrom a xs

def directBlockBits {N m : ℕ} (D : MSSCInstance N m) (b : Block m) : List Bool :=
  let codes := directBlockCodes D b
  List.replicate (codes.length - 1) false ++
    codes.flatMap (fun n => true :: (unaryFrame (blockCode b) ++ unaryFrame n))

theorem directBlockBits_eq {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    directBlockBits D b = treeBits (canonicalBlockTree D b) := by
  rw [canonicalBlockTree_bits]
  simp only [directBlockBits, directBlockCodes_eq, canonicalBlockCells,
    List.length_map, List.flatMap_map, cellBits]

/-- Cost of appending n fresh terminal types to a current c-leaf comb.
    A simple bounded counter recursion, not a minimization or tree scan. -/
def combTailCost (s c : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (s - (c + 1)) + combTailCost s (c + 1) n

theorem combTailCost_le (s c n : ℕ) : combTailCost s c n ≤ n * s := by
  induction n generalizing c with
  | zero => simp [combTailCost]
  | succ n ih =>
      have ht := ih (c + 1)
      have hs := Nat.sub_le s (c + 1)
      simp only [combTailCost]
      nlinarith

theorem scanTypeCount_eq_leaves_of_nodup {A : Type u} {S : Type v}
    [DecidableEq S] (tip : A → S) (T : BTree A)
    (h : ((leaves T).map tip).Nodup) : scanTypeCount tip T = (leaves T).length := by
  simp only [scanTypeCount, scanLeaves_eq, scanDistinctCount_spec,
    List.toFinset_card_of_nodup h, List.length_map]

theorem scanStarScore_attach_distinct {A : Type u} {S : Type v}
    [DecidableEq S] (s : ℕ) (tip : A → S) (T : BTree A) (xs : List A)
    (h : ((leaves T ++ xs).map tip).Nodup) :
    scanStarScore s tip (attach T xs) =
      scanStarScore s tip T + combTailCost s (leaves T).length xs.length := by
  induction xs generalizing T with
  | nil => simp [attach, combTailCost]
  | cons a xs ih =>
      have hall : ((leaves (.node T (.leaf a)) ++ xs).map tip).Nodup := by
        simpa only [leaves, List.singleton_append, List.append_assoc] using h
      have hhead : ((leaves (.node T (.leaf a))).map tip).Nodup := by
        have hp : (((leaves (.node T (.leaf a))).map tip) ++ xs.map tip).Nodup := by
          simpa only [List.map_append] using hall
        exact (List.nodup_append.mp hp).1
      have hc := scanTypeCount_eq_leaves_of_nodup tip (.node T (.leaf a)) hhead
      rw [attach, ih (.node T (.leaf a)) hall]
      simp only [scanStarScore, hc, leaves, List.length_append, List.length_singleton,
        List.length_cons, combTailCost, Nat.add_zero]
      omega

theorem scanStarScore_combFrom_distinct {A : Type u} {S : Type v}
    [DecidableEq S] (s : ℕ) (tip : A → S) (a : A) (xs : List A)
    (h : ((a :: xs).map tip).Nodup) :
    scanStarScore s tip (combFrom a xs) = combTailCost s 1 xs.length := by
  have hall : ((leaves (.leaf a) ++ xs).map tip).Nodup := h
  simpa only [combFrom, foldl_node_eq_attach, leaves, List.length_singleton,
    scanStarScore, Nat.zero_add] using scanStarScore_attach_distinct s tip (.leaf a) xs hall

theorem scanStarScore_canonical_arithmetic {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    scanStarScore (N + m * N + 3) Prod.snd (canonicalBlockTree D b) =
      combTailCost (N + m * N + 3) 1 ((directBlockCodes D b).length - 1) := by
  have hdist : ((canonicalBlockCells D b).map Prod.snd).Nodup := by
    simpa only [canonicalBlockCells, List.map_map, Function.comp_def, List.map_id] using
      canonicalTypeList_nodup D b
  have hn := canonicalBlockCells_nonempty D b
  rw [directBlockCodes_length]
  cases h : canonicalBlockCells D b with
  | nil => exact (hn h).elim
  | cons a xs =>
      have hax : ((a :: xs).map Prod.snd).Nodup := by simpa only [h] using hdist
      simpa only [canonicalBlockTree, h, List.headD_cons, List.tail_cons,
        List.length_cons, Nat.add_sub_cancel] using
          scanStarScore_combFrom_distinct (N + m * N + 3) Prod.snd a xs hax

def directFixedCost {N m : ℕ} (D : MSSCInstance N m) : ℕ :=
  ((blockIndexList m).map fun b =>
    combTailCost (N + m * N + 3) 1 ((directBlockCodes D b).length - 1)).sum

theorem directFixedCost_eq {N m : ℕ} (D : MSSCInstance N m) :
    directFixedCost D = scanFixedCost (canonicalBlockTree D) := by
  simp only [directFixedCost, scanFixedCost, scanStarScore_canonical_arithmetic]

def directCanonicalBits {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) : List Bool :=
  binaryNatFrame N ++ binaryNatFrame m ++ binaryNatFrame (directFixedCost D + K - N) ++
    unaryFrame (blockIndexList m).length ++
      (blockIndexList m).flatMap (directBlockBits D)

theorem directCanonicalBits_eq {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) :
    directCanonicalBits D K = scanEncodeTarget ⟨N, m, scanCanonicalTarget D K⟩ := by
  simp only [directCanonicalBits, directFixedCost_eq, directBlockBits_eq,
    scanEncodeTarget, scanCanonicalTarget, encodeFramedList, List.length_map,
    List.flatMap_map, Function.comp_def, List.append_assoc]

def directMSSCBits {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) : List Bool :=
  if N = 0 then scanEncodeTarget scanFixedYesTarget
  else if m ≤ 1 then
    (if N ≤ K then scanEncodeTarget scanFixedYesTarget else scanEncodeTarget scanFixedNoTarget)
  else if K < N then scanEncodeTarget scanFixedNoTarget
  else if m * N ≤ K then scanEncodeTarget scanFixedYesTarget
  else directCanonicalBits D K

theorem directMSSCBits_eq {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) :
    directMSSCBits D K = scanEncodeTarget (scanTotalMSSCTarget D K) := by
  by_cases hz : N = 0
  · simp [directMSSCBits, scanTotalMSSCTarget, hz]
  · by_cases hm : m ≤ 1
    · by_cases hNK : N ≤ K <;>
        simp [directMSSCBits, scanTotalMSSCTarget, hz, hm, hNK]
    · by_cases hKN : K < N
      · simp [directMSSCBits, scanTotalMSSCTarget, hz, hm, hKN]
      · by_cases hbig : m * N ≤ K <;>
          simp [directMSSCBits, scanTotalMSSCTarget, hz, hm, hKN, hbig,
            directCanonicalBits_eq]

def directRawSourceBits (R : RawMSSCRecord) : List Bool :=
  if h : scanSourceValid R = true then
    directMSSCBits (scanSourceModel R ((scanSourceValid_spec R).mp h)) R.K
  else scanEncodeTarget scanFixedNoTarget

theorem directRawSourceBits_eq (R : RawMSSCRecord) :
    directRawSourceBits R = scanEncodeTarget (scanTotalRawTarget R) := by
  by_cases h : scanSourceValid R = true <;>
    simp [directRawSourceBits, scanTotalRawTarget, h, directMSSCBits_eq]

def directBoundedConstructor (bits : List Bool) : List Bool :=
  match parseSaturatedSource bits with
  | none => scanEncodeTarget scanFixedNoTarget
  | some R => directRawSourceBits R

/-- Full exact constructor, with original malformed/boundary behavior. -/
theorem directBoundedConstructor_eq (bits : List Bool) :
    directBoundedConstructor bits = scanEncodedConstructor bits := by
  rw [← saturatedEncodedConstructor_eq]
  unfold directBoundedConstructor saturatedEncodedConstructor
  cases h : parseSaturatedSource bits with
  | none => rfl
  | some R => exact directRawSourceBits_eq R

def originalConstructorMachineOfDirect
    (h : Turing.TM2ComputableInPolyTime
      (fun bits : List Bool => bits) (fun bits : List Bool => bits)
      directBoundedConstructor) : ConstructorMachineWitness := by
  have he : directBoundedConstructor = scanEncodedConstructor :=
    funext directBoundedConstructor_eq
  simpa only [he] using h

theorem full_direct_constructor_interface (input : List Bool) (lambda : ℝ) :
    (directBoundedConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (directBoundedConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (directBoundedConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (directBoundedConstructor input).length ∧
          boundedEncodedTarget (directBoundedConstructor input) cert = true) := by
  simpa only [directBoundedConstructor_eq, boundedEncodedTarget_eq] using
    full_explicit_encoded_reduction input lambda

/- Range filtering and unary-cost/bit emission are still ordinary source
algorithms, not actual finite-TM2 programs. Membership in the finite sets
comes from the explicitly supplied, guarded source rows, not an oracle for
an arbitrary D. Whole emitted programs and operational resource proofs,
the independent verifier, encoded upstream hardness and all kernel checks
remain open. The full reduction is not replaced by a comb-only target:
only the original fixed CHILD blocks are serialized as their original combs;
the candidate JOINING refinement remains completely unrestricted.
-/

end PolytomyReductionModel
