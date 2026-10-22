/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/kernel/runtime or complexity certificate.

Canonical tagged-range ordering and an exact full-reduction adapter for any
binary block realization with the required observed sets and mixed vertices.
Each realization uses its OWN fixed cost. No tree-isomorphism shortcut is used.
Sorting is specified by finite arithmetic comparison, not Finset.toList choice.
This does not yet supply an encoded Turing-machine polynomial-time proof.
-/
import PolytomyFrontierInterface

namespace PolytomyReductionModel

section CanonicalEnumeration

def terminalCode (N m : ℕ) : Terminal N m → ℕ
  | .inl x => x.val
  | .inr (.inl z) => N + z.val
  | .inr (.inr k) => N + privateCount N m + k.val

theorem terminalCode_injective (N m : ℕ) :
    Function.Injective (terminalCode N m) := by
  intro a b h
  rcases a with x | (z | k)
  · rcases b with y | (w | j)
    · apply congrArg Sum.inl
      apply Fin.ext
      exact h
    · have hx := x.isLt
      simp only [terminalCode] at h
      omega
    · have hx := x.isLt
      simp only [terminalCode] at h
      omega
  · rcases b with y | (w | j)
    · have hy := y.isLt
      simp only [terminalCode] at h
      omega
    · apply congrArg Sum.inr
      apply congrArg Sum.inl
      apply Fin.ext
      simp only [terminalCode] at h
      omega
    · have hz := z.isLt
      simp only [terminalCode] at h
      omega
  · rcases b with y | (w | j)
    · have hy := y.isLt
      simp only [terminalCode] at h
      omega
    · have hw := w.isLt
      simp only [terminalCode] at h
      omega
    · apply congrArg Sum.inr
      apply congrArg Sum.inr
      apply Fin.ext
      simp only [terminalCode] at h
      omega

def terminalCodeOrder (N m : ℕ) : LinearOrder (Terminal N m) :=
  LinearOrder.lift' (terminalCode N m) (terminalCode_injective N m)

theorem terminalCode_lt (N m : ℕ) (s : Terminal N m) :
    terminalCode N m s < N + m * N + 3 := by
  rcases s with x | (z | k)
  · have hx := x.isLt
    simp only [terminalCode]
    omega
  · have hz := z.isLt
    simp only [terminalCode, privateCount] at hz ⊢
    omega
  · have hk := k.isLt
    simp only [terminalCode, privateCount]
    omega

def canonicalTypeList {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    List (Terminal N m) :=
  letI := terminalCodeOrder N m
  (blockTypes D b).sort (· ≤ ·)

theorem canonicalTypeList_nodup {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    (canonicalTypeList D b).Nodup := by
  letI := terminalCodeOrder N m
  exact Finset.sort_nodup (blockTypes D b) (· ≤ ·)

theorem mem_canonicalTypeList {N m : ℕ} (D : MSSCInstance N m) (b : Block m)
    (s : Terminal N m) : s ∈ canonicalTypeList D b ↔ s ∈ blockTypes D b := by
  letI := terminalCodeOrder N m
  exact Finset.mem_sort (s := blockTypes D b) (· ≤ ·)

theorem canonicalTypeList_length {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    (canonicalTypeList D b).length = (blockTypes D b).card := by
  letI := terminalCodeOrder N m
  exact Finset.length_sort (s := blockTypes D b) (· ≤ ·)

def canonicalBlockCells {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    List (Cell N m) :=
  (canonicalTypeList D b).map (fun s => (b, s))

def canonicalBlockTree {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    BTree (Cell N m) :=
  let xs := canonicalBlockCells D b
  combFrom (xs.headD (b, marker0 N m)) xs.tail

theorem leaves_canonicalBlockTree {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : leaves (canonicalBlockTree D b) = canonicalBlockCells D b := by
  have hm : (b, marker0 N m) ∈ canonicalBlockCells D b := by
    simp [canonicalBlockCells, mem_canonicalTypeList, marker0_mem_blockTypes]
  cases hx : canonicalBlockCells D b with
  | nil => simp [hx] at hm
  | cons a rest =>
      simp [canonicalBlockTree, hx, combFrom, foldl_node_eq_attach,
        leaves_attach, leaves]

theorem observed_canonicalBlockTree {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : observed Prod.snd (canonicalBlockTree D b) = blockTypes D b := by
  rw [observed_eq_leaves_image, leaves_canonicalBlockTree]
  ext s
  simp [canonicalBlockCells, List.map_map, mem_canonicalTypeList]

theorem canonicalBlockTree_mixed {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : AllInternalMixed Prod.snd (canonicalBlockTree D b) := by
  apply allInternalMixed_of_nodup
  rw [leaves_canonicalBlockTree]
  simpa [canonicalBlockCells, List.map_map] using canonicalTypeList_nodup D b

theorem canonicalBlockTree_cells_nodup {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : (leaves (canonicalBlockTree D b)).Nodup := by
  rw [leaves_canonicalBlockTree]
  apply List.Nodup.map
  · intro a c h
    exact congrArg Prod.snd h
  · exact canonicalTypeList_nodup D b

theorem valid_canonical_graft_cells_nodup {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) (ht : ValidJoiningTree t) :
    (leaves (graft (canonicalBlockTree D) t)).Nodup := by
  have hn : (leaves t).Nodup := ht.nodup_iff.mpr Finset.univ.nodup_toList
  rw [leaves_graft_flatMap]
  apply List.nodup_flatMap.mpr
  constructor
  · intro b hb
    exact canonicalBlockTree_cells_nodup D b
  · exact hn.imp fun {b c} hbc x hx hy => by
      rw [leaves_canonicalBlockTree] at hx hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      obtain ⟨z, hz, he⟩ := List.mem_map.mp hy
      exact hbc (congrArg Prod.fst he).symm

theorem canonicalBlockTree_leaf_bound {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : (leaves (canonicalBlockTree D b)).length ≤ N + m * N + 3 := by
  rw [leaves_canonicalBlockTree]
  have h := Finset.card_le_card (Finset.subset_univ (blockTypes D b))
  simpa [canonicalBlockCells, canonicalTypeList_length, terminal_card] using h

theorem valid_canonical_graft_leaf_bound {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) (ht : ValidJoiningTree t) :
    (leaves (graft (canonicalBlockTree D) t)).length ≤
      (m + 1) * (N + m * N + 3) := by
  rw [graft_leaf_count, blockScoreSum_as_list,
    (ht.map (fun b => (leaves (canonicalBlockTree D b)).length)).sum_eq,
    Finset.sum_map_toList]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b hb => canonicalBlockTree_leaf_bound D b)
  simpa using h

theorem valid_canonical_graft_vertex_bound {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) (ht : ValidJoiningTree t) :
    vertexCount (graft (canonicalBlockTree D) t) + 1 ≤
      2 * ((m + 1) * (N + m * N + 3)) := by
  rw [vertexCount_add_one]
  exact Nat.mul_le_mul_left 2 (valid_canonical_graft_leaf_bound D t ht)

end CanonicalEnumeration

noncomputable section RealizationAdapter

def realizedFixedCost {N m : ℕ} (blocks : Block m → BTree (Cell N m)) : ℕ :=
  ∑ b : Block m, starScore Finset.univ Prod.snd (blocks b)

def realizedScore {N m : ℕ} (blocks : Block m → BTree (Cell N m))
    (t : BTree (Block m)) : ℕ :=
  starScore Finset.univ Prod.snd (graft blocks t)

theorem canonicalBlockTree_score_bound {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : starScore Finset.univ Prod.snd (canonicalBlockTree D b) ≤
      (N + m * N + 3) * (N + m * N + 3) := by
  have hs := starScore_bound Finset.univ Prod.snd (canonicalBlockTree D b)
  have hl := canonicalBlockTree_leaf_bound D b
  have hc := leaves_length (canonicalBlockTree D b)
  have hi : internalCount (canonicalBlockTree D b) ≤ N + m * N + 3 := by omega
  simp only [Finset.card_univ, terminal_card] at hs
  exact hs.trans (Nat.mul_le_mul_right _ hi)

theorem canonical_fixedCost_bound {N m : ℕ} (D : MSSCInstance N m) :
    realizedFixedCost (canonicalBlockTree D) ≤
      (m + 1) * ((N + m * N + 3) * (N + m * N + 3)) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b hb => canonicalBlockTree_score_bound D b)
  simpa [realizedFixedCost] using h

theorem realizedScore_decomposition {N m : ℕ} (D : MSSCInstance N m)
    (blocks : Block m → BTree (Cell N m))
    (hobs : ∀ b, observed Prod.snd (blocks b) = blockTypes D b)
    (t : BTree (Block m)) (ht : ValidJoiningTree t) :
    realizedScore blocks t = realizedFixedCost blocks +
      joiningScore Finset.univ (blockTypes D) t := by
  have hsum := (ht.map (fun b => starScore Finset.univ Prod.snd (blocks b))).sum_eq
  rw [Finset.sum_map_toList] at hsum
  simp only [realizedScore, star_graft_score, hobs, blockScoreSum_as_list]
  rw [hsum]
  rfl

/-- Changing fixed block realizations changes only the fixed part of the score.
    Thresholds use the corresponding fixed cost on EACH side. -/
theorem realized_threshold_iff {N m : ℕ} (D : MSSCInstance N m)
    (blocks : Block m → BTree (Cell N m))
    (hobs : ∀ b, observed Prod.snd (blocks b) = blockTypes D b)
    (t : BTree (Block m)) (ht : ValidJoiningTree t) (K : ℕ) (hNK : N ≤ K) :
    realizedScore blocks t ≤ realizedFixedCost blocks + K - N ↔
      fullScore D t ≤ fixedCost D + K - N := by
  rw [realizedScore_decomposition D blocks hobs t ht, fullScore_decomposition D t ht]
  omega

theorem realization_graft_mixed {N m : ℕ} (D : MSSCInstance N m)
    (blocks : Block m → BTree (Cell N m))
    (hobs : ∀ b, observed Prod.snd (blocks b) = blockTypes D b)
    (hmix : ∀ b, AllInternalMixed Prod.snd (blocks b)) (t : BTree (Block m)) :
    AllInternalMixed Prod.snd (graft blocks t) := by
  have hmarks : ∀ q : BTree (Block m),
      markers N m ⊆ observed Prod.snd (graft blocks q) := by
    intro q
    induction q with
    | leaf b => simpa only [graft, hobs] using markers_subset_blockTypes D b
    | node l r ihl ihr => exact ihl.trans Finset.subset_union_left
  induction t with
  | leaf b => exact hmix b
  | node l r ihl ihr =>
      refine ⟨?_, ihl, ihr⟩
      have h := Finset.card_le_card (hmarks (.node l r))
      simpa only [markers_card] using h

def RealizedCartaDecision {N m : ℕ} (blocks : Block m → BTree (Cell N m))
    (lambda : ℝ) (K : ℕ) : Prop :=
  ∃ t : BTree (Block m), ∃ L : StarLabeledTree (Cell N m) (Terminal N m),
    ValidJoiningTree t ∧ eraseStar L = graft blocks t ∧
    StarFeasible Prod.snd L ∧
    cartaStarScore Prod.snd lambda L ≤ (realizedFixedCost blocks + K - N : ℕ)

theorem realizedCartaDecision_iff_refinementDecision {N m : ℕ}
    (D : MSSCInstance N m) (blocks : Block m → BTree (Cell N m))
    (hobs : ∀ b, observed Prod.snd (blocks b) = blockTypes D b)
    (hmix : ∀ b, AllInternalMixed Prod.snd (blocks b))
    (lambda : ℝ) (K : ℕ) (hNK : N ≤ K) :
    RealizedCartaDecision blocks lambda K ↔ RefinementDecision D K := by
  constructor
  · rintro ⟨t, L, ht, he, hf, hc⟩
    have hm : AllInternalMixed Prod.snd (eraseStar L) := by
      rw [he]
      exact realization_graft_mixed D blocks hobs hmix t
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm, he] at hc
    have hn : realizedScore blocks t ≤ realizedFixedCost blocks + K - N := by
      exact_mod_cast hc
    exact ⟨t, ht, (realized_threshold_iff D blocks hobs t ht K hNK).mp hn⟩
  · rintro ⟨t, ht, hc⟩
    let L : StarLabeledTree (Cell N m) (Terminal N m) := canonicalStar (graft blocks t)
    have he : eraseStar L = graft blocks t := canonicalStar_erase _
    have hf : StarFeasible Prod.snd L := canonicalStar_feasible Prod.snd _
    have hm : AllInternalMixed Prod.snd (eraseStar L) := by
      rw [he]
      exact realization_graft_mixed D blocks hobs hmix t
    have hn := (realized_threshold_iff D blocks hobs t ht K hNK).mpr hc
    refine ⟨t, L, ht, he, hf, ?_⟩
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm, he]
    exact_mod_cast hn

/-- The entire actual-D_lambda finite reduction for the canonically ordered
    block realization. No isomorphism to arbitrary-choice combs is assumed. -/
theorem full_canonical_carta_reduction {N m : ℕ} (D : MSSCInstance N m)
    (lambda : ℝ) (K : ℕ) (hN : 0 < N) (hm : 2 ≤ m)
    (hNK : N ≤ K) (hKmN : K ≤ m * N) :
    MSSCDecision D K ↔ RealizedCartaDecision (canonicalBlockTree D) lambda K := by
  rw [realizedCartaDecision_iff_refinementDecision D (canonicalBlockTree D)
    (observed_canonicalBlockTree D) (canonicalBlockTree_mixed D) lambda K hNK]
  exact fullReductionClaim N m D K hN hm hNK hKmN

def RealizedFrontierCartaDecision {N m : ℕ}
    (blocks : Block m → BTree (Cell N m)) (lambda : ℝ) (K : ℕ) : Prop :=
  ∃ L : StarLabeledTree (Cell N m) (Terminal N m),
    (∃ xs : List (Block m), xs.Perm (Finset.univ : Finset (Block m)).toList ∧
      BlockFrontier blocks (eraseStar L) xs) ∧ StarFeasible Prod.snd L ∧
    cartaStarScore Prod.snd lambda L ≤ (realizedFixedCost blocks + K - N : ℕ)

theorem realizedFrontierCartaDecision_iff_refinementDecision {N m : ℕ}
    (D : MSSCInstance N m) (blocks : Block m → BTree (Cell N m))
    (hobs : ∀ b, observed Prod.snd (blocks b) = blockTypes D b)
    (hmix : ∀ b, AllInternalMixed Prod.snd (blocks b))
    (lambda : ℝ) (K : ℕ) (hNK : N ≤ K) :
    RealizedFrontierCartaDecision blocks lambda K ↔ RefinementDecision D K := by
  constructor
  · rintro ⟨L, ⟨xs, hp, hfront⟩, hf, hc⟩
    obtain ⟨t, hl, hi⟩ := BlockFrontier.has_skeleton blocks hfront
    have ht : ValidJoiningTree t := by simpa only [ValidJoiningTree, hl] using hp
    have hm : AllInternalMixed Prod.snd (eraseStar L) :=
      (TreeIso.mixed_iff Prod.snd hi).mpr (realization_graft_mixed D blocks hobs hmix t)
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm,
      TreeIso.starScore_eq Finset.univ Prod.snd hi] at hc
    have hn : realizedScore blocks t ≤ realizedFixedCost blocks + K - N := by
      exact_mod_cast hc
    exact ⟨t, ht, (realized_threshold_iff D blocks hobs t ht K hNK).mp hn⟩
  · intro h
    obtain ⟨t, L, ht, he, hf, hc⟩ :=
      (realizedCartaDecision_iff_refinementDecision D blocks hobs hmix lambda K hNK).mpr h
    refine ⟨L, ⟨leaves t, ht, ?_⟩, hf, hc⟩
    rw [he]
    exact graft_has_frontier blocks t

/-- The canonical construction retains the full cut-certified cell-tree
    refinement domain, actual feasible labels and exact D_lambda threshold. -/
theorem full_canonical_frontier_carta_reduction {N m : ℕ} (D : MSSCInstance N m)
    (lambda : ℝ) (K : ℕ) (hN : 0 < N) (hm : 2 ≤ m)
    (hNK : N ≤ K) (hKmN : K ≤ m * N) :
    MSSCDecision D K ↔
      RealizedFrontierCartaDecision (canonicalBlockTree D) lambda K := by
  rw [realizedFrontierCartaDecision_iff_refinementDecision D (canonicalBlockTree D)
    (observed_canonicalBlockTree D) (canonicalBlockTree_mixed D) lambda K hNK]
  exact fullReductionClaim N m D K hN hm hNK hKmN

end RealizationAdapter
end PolytomyReductionModel
