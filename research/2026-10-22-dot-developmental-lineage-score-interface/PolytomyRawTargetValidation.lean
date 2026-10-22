/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/certificate.

Independent target-record validation. The guard examines actual supplied
trees and their observed type codes before constructing a function on all
declared blocks or enumerating the declared terminal universe.
-/
import PolytomyMarkedTargetDomain

namespace PolytomyReductionModel
noncomputable section

structure RawTargetRows (N m : ℕ) where
  budget : ℕ
  rows : List (BTree (Cell N m))

def rawTargetLeaves {N m : ℕ} (R : RawTargetRows N m) : List (Cell N m) :=
  R.rows.flatMap leaves

def rawTargetTypes {N m : ℕ} (R : RawTargetRows N m) : Finset (Terminal N m) :=
  ((rawTargetLeaves R).map Prod.snd).toFinset

def rawTargetTypeCodes {N m : ℕ} (R : RawTargetRows N m) : Finset ℕ :=
  ((rawTargetLeaves R).map (fun a => terminalCode N m a.2)).toFinset

def checkTreeMixed {N m : ℕ} : BTree (Cell N m) → Bool
  | .leaf _ => true
  | .node l r => decide (2 ≤ (observed Prod.snd (.node l r)).card) &&
      checkTreeMixed l && checkTreeMixed r

theorem checkTreeMixed_spec {N m : ℕ} (T : BTree (Cell N m)) :
    checkTreeMixed T = true ↔ AllInternalMixed Prod.snd T := by
  induction T with
  | leaf a => simp [checkTreeMixed, AllInternalMixed]
  | node l r ihl ihr => simp [checkTreeMixed, AllInternalMixed, ihl, ihr, and_assoc]

structure RawTargetRowsValid {N m : ℕ} (R : RawTargetRows N m) : Prop where
  positiveN : 0 < N
  degree : 2 ≤ m
  rowCount : R.rows.length = m + 1
  cellsNodup : (rawTargetLeaves R).Nodup
  mixed : ∀ T ∈ R.rows, AllInternalMixed Prod.snd T
  markers : ∀ T ∈ R.rows, markers N m ⊆ observed Prod.snd T
  typeCount : (rawTargetTypeCodes R).card = N + m * N + 3

/-- No Fin N/Fin m/universe enumeration occurs in this guard. Markers has
    exactly two elements, regardless of the declared dimensions. -/
def rawTargetRowsValidBool {N m : ℕ} (R : RawTargetRows N m) : Bool :=
  decide (0 < N) && decide (2 ≤ m) && decide (R.rows.length = m + 1) &&
  decide ((rawTargetLeaves R).Nodup) &&
  R.rows.all checkTreeMixed &&
  R.rows.all (fun T => decide (markers N m ⊆ observed Prod.snd T)) &&
  decide ((rawTargetTypeCodes R).card = N + m * N + 3)

theorem rawTargetRowsValidBool_spec {N m : ℕ} (R : RawTargetRows N m) :
    rawTargetRowsValidBool R = true ↔ RawTargetRowsValid R := by
  simp only [rawTargetRowsValidBool, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, checkTreeMixed_spec]
  constructor
  · intro h
    rcases h with ⟨⟨⟨⟨⟨⟨hN, hm⟩, hl⟩, hn⟩, hmix⟩, hmarks⟩, hc⟩
    exact ⟨hN, hm, hl, hn, hmix, hmarks, hc⟩
  · rintro ⟨hN, hm, hl, hn, hmix, hmarks, hc⟩
    exact ⟨⟨⟨⟨⟨⟨hN, hm⟩, hl⟩, hn⟩, hmix⟩, hmarks⟩, hc⟩

theorem blockCode_le {m : ℕ} (b : Block m) : blockCode b ≤ m := by
  cases b with
  | none => simp [blockCode]
  | some i => have hi := i.isLt; simp only [blockCode]; omega

theorem blockCode_injective (m : ℕ) : Function.Injective (@blockCode m) := by
  intro b c h
  cases b with
  | none => cases c <;> simp_all [blockCode]
  | some i =>
      cases c with
      | none => simp [blockCode] at h
      | some j =>
          have hv : i.val = j.val := by simpa [blockCode] using h
          exact congrArg some (Fin.ext hv)

theorem blockCode_hits_index {m : ℕ} (i : ℕ) (hi : i ≤ m) :
    ∃ b : Block m, blockCode b = i := by
  by_cases h0 : i = 0
  · exact ⟨none, by simp [blockCode, h0]⟩
  · refine ⟨some ⟨i - 1, by omega⟩, ?_⟩
    simp only [blockCode]
    omega

def rawTargetIndex {N m : ℕ} (R : RawTargetRows N m) (h : RawTargetRowsValid R)
    (b : Block m) : Fin R.rows.length :=
  ⟨blockCode b, by have hb := blockCode_le b; rw [h.rowCount]; omega⟩

def rawRowsToTarget {N m : ℕ} (R : RawTargetRows N m) (h : RawTargetRowsValid R) :
    BlockTargetData N m where
  blocks b := R.rows.get (rawTargetIndex R h b)
  budget := R.budget

theorem rawRowsToTarget_mem {N m : ℕ} (R : RawTargetRows N m) (h : RawTargetRowsValid R)
    (b : Block m) : (rawRowsToTarget R h).blocks b ∈ R.rows :=
  List.get_mem _ _

theorem rawRowsToTarget_hits {N m : ℕ} (R : RawTargetRows N m) (h : RawTargetRowsValid R)
    (T : BTree (Cell N m)) (hT : T ∈ R.rows) :
    ∃ b : Block m, (rawRowsToTarget R h).blocks b = T := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hT
  obtain ⟨b, hb⟩ := blockCode_hits_index i.val (by have hlt := i.isLt; rw [h.rowCount] at hlt; omega)
  refine ⟨b, ?_⟩
  have he : rawTargetIndex R h b = i := Fin.ext hb
  simpa only [rawRowsToTarget, he] using hi

theorem rawTargetTypeCodes_image {N m : ℕ} (R : RawTargetRows N m) :
    rawTargetTypeCodes R = (rawTargetTypes R).image (terminalCode N m) := by
  ext n
  simp only [rawTargetTypeCodes, rawTargetTypes, List.mem_toFinset, List.mem_map,
    Finset.mem_image]
  aesop

theorem rawTargetTypes_univ {N m : ℕ} (R : RawTargetRows N m) (h : RawTargetRowsValid R) :
    rawTargetTypes R = Finset.univ := by
  have hc := h.typeCount
  rw [rawTargetTypeCodes_image, Finset.card_image_of_injective _ (terminalCode_injective N m)] at hc
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa only [Finset.card_univ, terminal_card, hc]

theorem rawRowsToTarget_typeUnion {N m : ℕ} (R : RawTargetRows N m)
    (h : RawTargetRowsValid R) :
    (Finset.univ.biUnion fun b => observed Prod.snd ((rawRowsToTarget R h).blocks b)) =
      rawTargetTypes R := by
  ext s
  constructor
  · intro hs
    obtain ⟨b, hb, hbs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨a, ha, he⟩ : ∃ a ∈ leaves ((rawRowsToTarget R h).blocks b), a.2 = s := by
      simpa [observed_eq_leaves_image] using hbs
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨a, List.mem_flatMap.mpr ⟨(rawRowsToTarget R h).blocks b,
      rawRowsToTarget_mem R h b, ha⟩, he⟩
  · intro hs
    obtain ⟨a, ha, he⟩ : ∃ a ∈ rawTargetLeaves R, a.2 = s := by
      simpa [rawTargetTypes] using hs
    obtain ⟨T, hTr, haT⟩ := List.mem_flatMap.mp ha
    obtain ⟨b, hb⟩ := rawRowsToTarget_hits R h T hTr
    apply Finset.mem_biUnion.mpr
    refine ⟨b, Finset.mem_univ b, ?_⟩
    rw [hb, observed_eq_leaves_image]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, haT, he⟩)

theorem rawRowsToTarget_cellUnion {N m : ℕ} (R : RawTargetRows N m)
    (h : RawTargetRowsValid R) :
    (Finset.univ.biUnion fun b => cellSet ((rawRowsToTarget R h).blocks b)) =
      (rawTargetLeaves R).toFinset := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
      ⟨(rawRowsToTarget R h).blocks b, rawRowsToTarget_mem R h b, (mem_cellSet a _).mp hab⟩)
  · intro ha
    obtain ⟨T, hTr, haT⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp ha)
    obtain ⟨b, hb⟩ := rawRowsToTarget_hits R h T hTr
    refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, ?_⟩
    rw [hb]
    exact (mem_cellSet a T).mpr haT

theorem raw_target_refinement_leaf_bound {N m : ℕ} (R : RawTargetRows N m)
    (h : RawTargetRowsValid R) (T : BTree (Cell N m))
    (hT : StandardBlockRefinement (rawRowsToTarget R h).blocks T) :
    (leaves T).length ≤ (rawTargetLeaves R).length := by
  have hc : (leaves T).length = (cellSet T).card := by
    simpa [cellSet, observed_eq_leaves_image] using
      (List.toFinset_card_of_nodup hT.1).symm
  rw [hc, hT.2.1, rawRowsToTarget_cellUnion]
  exact List.toFinset_card_le _

theorem rawRowsToTarget_marked {N m : ℕ} (R : RawTargetRows N m)
    (h : RawTargetRowsValid R) : MarkedTargetDomain (rawRowsToTarget R h) := by
  obtain ⟨hnb, hpair⟩ := List.nodup_flatMap.mp h.cellsNodup
  refine ⟨h.positiveN, h.degree, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact hnb _ (rawRowsToTarget_mem R h b)
  · intro b c hbc
    have hine : rawTargetIndex R h b ≠ rawTargetIndex R h c := by
      intro he
      apply hbc
      apply blockCode_injective m
      exact congrArg Fin.val he
    apply Finset.disjoint_left.mpr
    intro a hab hac
    have hlb := (mem_cellSet a _).mp hab
    have hlc := (mem_cellSet a _).mp hac
    rcases lt_or_gt_of_ne hine with hlt | hgt
    · exact (hpair.rel_get_of_lt hlt) hlb hlc
    · exact (hpair.rel_get_of_lt hgt) hlc hlb
  · intro b
    exact h.mixed _ (rawRowsToTarget_mem R h b)
  · intro b
    exact h.markers _ (rawRowsToTarget_mem R h b)
  · rw [rawRowsToTarget_typeUnion, rawTargetTypes_univ R h]

def decodeRawTargetRows {N m : ℕ} (R : RawTargetRows N m) : Option (BlockTargetData N m) :=
  if h : rawTargetRowsValidBool R = true then
    some (rawRowsToTarget R ((rawTargetRowsValidBool_spec R).mp h))
  else none

theorem decodeRawTargetRows_valid {N m : ℕ} (R : RawTargetRows N m)
    (h : RawTargetRowsValid R) :
    decodeRawTargetRows R = some (rawRowsToTarget R h) := by
  simp [decodeRawTargetRows, (rawTargetRowsValidBool_spec R).mpr h]

theorem decodeRawTargetRows_marked {N m : ℕ} (R : RawTargetRows N m)
    (G : BlockTargetData N m) (hG : decodeRawTargetRows R = some G) : MarkedTargetDomain G := by
  unfold decodeRawTargetRows at hG
  split_ifs at hG with h
  · have he := Option.some.inj hG
    rw [← he]
    exact rawRowsToTarget_marked R ((rawTargetRowsValidBool_spec R).mp h)
  · cases hG

theorem raw_target_dimensions_bounded {N m : ℕ} (R : RawTargetRows N m)
    (h : RawTargetRowsValid R) :
    N + m * N + 3 ≤ (rawTargetLeaves R).length ∧ m < R.rows.length := by
  have hc := List.toFinset_card_le
    ((rawTargetLeaves R).map (fun a => terminalCode N m a.2))
  have hs : (rawTargetTypeCodes R).card ≤ (rawTargetLeaves R).length := by
    simpa [rawTargetTypeCodes] using hc
  rw [h.typeCount] at hs
  exact ⟨hs, by rw [h.rowCount]; omega⟩

def targetToRows {N m : ℕ} (G : BlockTargetData N m) : RawTargetRows N m where
  budget := G.budget
  rows := (blockIndexList m).map G.blocks

theorem blockIndexList_nodup (m : ℕ) : (blockIndexList m).Nodup := by
  have h := (List.nodup_finRange m).map
    (fun a b h => (Option.some.inj h : a = b))
  simpa [blockIndexList] using h

theorem targetToRows_length {N m : ℕ} (G : BlockTargetData N m) :
    (targetToRows G).rows.length = m + 1 := by
  simp [targetToRows, blockIndexList]

theorem targetToRows_get {N m : ℕ} (G : BlockTargetData N m) (b : Block m)
    (hi : blockCode b < (targetToRows G).rows.length) :
    (targetToRows G).rows.get ⟨blockCode b, hi⟩ = G.blocks b := by
  cases b <;> simp [targetToRows, blockIndexList, blockCode, List.get_eq_getElem, List.finRange]

theorem targetToRows_typeUnion {N m : ℕ} (G : BlockTargetData N m) :
    rawTargetTypes (targetToRows G) =
      Finset.univ.biUnion (fun b => observed Prod.snd (G.blocks b)) := by
  ext s
  simp only [rawTargetTypes, rawTargetLeaves, targetToRows, List.mem_toFinset,
    List.mem_map, List.mem_flatMap, Finset.mem_biUnion, Finset.mem_univ,
    true_and, observed_eq_leaves_image]
  constructor
  · rintro ⟨a, ⟨T, ⟨b, hb, rfl⟩, ha⟩, he⟩
    exact ⟨b, a, ha, he⟩
  · rintro ⟨b, a, ha, he⟩
    exact ⟨a, ⟨G.blocks b, ⟨b, mem_blockIndexList b, rfl⟩, ha⟩, he⟩

theorem targetToRows_valid {N m : ℕ} (G : BlockTargetData N m)
    (h : MarkedTargetDomain G) : RawTargetRowsValid (targetToRows G) := by
  refine ⟨h.positiveN, h.degree, targetToRows_length G, ?_, ?_, ?_, ?_⟩
  · change (((blockIndexList m).map G.blocks).flatMap leaves).Nodup
    rw [List.flatMap_map]
    apply List.nodup_flatMap.mpr
    refine ⟨fun b hb => h.blockNodup b, ?_⟩
    exact (blockIndexList_nodup m).imp fun {b c} hbc a hab hac =>
      Finset.disjoint_left.mp (h.blockDisjoint b c hbc)
        ((mem_cellSet a _).mpr hab) ((mem_cellSet a _).mpr hac)
  · intro T hT
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hT
    exact h.blockMixed b
  · intro T hT
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hT
    exact h.blockMarkers b
  · rw [rawTargetTypeCodes_image, Finset.card_image_of_injective _ (terminalCode_injective N m),
      targetToRows_typeUnion, h.typeCoverage, Finset.card_univ, terminal_card]

theorem blockTargetData_eq {N m : ℕ} {G H : BlockTargetData N m}
    (hb : G.blocks = H.blocks) (hk : G.budget = H.budget) : G = H := by
  cases G
  cases H
  cases hb
  cases hk
  rfl

theorem rawRowsToTarget_targetToRows {N m : ℕ} (G : BlockTargetData N m)
    (h : RawTargetRowsValid (targetToRows G)) : rawRowsToTarget (targetToRows G) h = G := by
  apply blockTargetData_eq
  · funext b
    exact targetToRows_get G b _
  · rfl

theorem decodeRawTargetRows_targetToRows {N m : ℕ} (G : BlockTargetData N m)
    (h : MarkedTargetDomain G) : decodeRawTargetRows (targetToRows G) = some G := by
  rw [decodeRawTargetRows_valid _ (targetToRows_valid G h), rawRowsToTarget_targetToRows]

/- The input guard contains only operations on supplied finite trees/lists
and numerical comparisons. The raw forest bit codec, its consumption bounds,
encoder inverse and concrete polynomial machine proof remain separate. -/

end
end PolytomyReductionModel
