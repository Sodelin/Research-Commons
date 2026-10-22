/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/certificate.

Total finite source-bit to independent typed-target map, including malformed,
empty, small and threshold-boundary cases. Fixed yes/no outputs are genuine
canonical one-polytomy instances with three composite children, not Boolean
sentinels or a substitute target language. Machine cost/target serialization
and formal source hardness remain separate obligations.
-/
import PolytomySourceSizeBounds

namespace PolytomyReductionModel
universe u v

abbrev AnyBlockTarget := Σ N : ℕ, Σ m : ℕ, BlockTargetData N m

def AnyTargetAccepted (G : AnyBlockTarget) : Prop :=
  ∃ bits : List Bool, checkBlockTargetBits G.2.2 bits = true

theorem msscDecision_lower {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (h : MSSCDecision D K) : N ≤ K := by
  obtain ⟨order, hp, hK⟩ := h
  exact (msscCost_bounds D order hp).1.trans hK

theorem msscDecision_upper {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (h : m * N ≤ K) : MSSCDecision D K := by
  let order := (Finset.univ : Finset (Fin m)).toList
  exact ⟨order, List.Perm.refl _, (msscCost_bounds D order (List.Perm.refl _)).2.trans h⟩

theorem msscDecision_zero {m : ℕ} (D : MSSCInstance 0 m) (K : ℕ) :
    MSSCDecision D K := msscDecision_upper D K (by simp)

theorem msscDecision_small {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) (hm : m ≤ 1) :
    MSSCDecision D K ↔ N ≤ K := by
  constructor
  · exact msscDecision_lower D K
  · intro hK
    apply msscDecision_upper D K
    have h := Nat.mul_le_mul_right N hm
    have h' : m * N ≤ N := by simpa using h
    exact h'.trans hK

theorem full_mssc_unbounded_bits {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (hN : 0 < N) (hm : 2 ≤ m) (hNK : N ≤ K) (hKmN : K ≤ m * N) :
    MSSCDecision D K ↔ ∃ bits : List Bool, checkCanonicalBits D K bits = true := by
  constructor
  · intro h
    obtain ⟨bits, hb, hc⟩ := (full_mssc_bit_reduction D K hN hm hNK hKmN).mp h
    exact ⟨bits, hc⟩
  · rintro ⟨bits, hc⟩
    exact (full_mssc_checked_tree_reduction D K hN hm hNK hKmN).mpr
      (checkCanonicalBits_sound D K bits hc)

def fixedBoundarySource : MSSCInstance 1 2 where
  sets _ := Finset.univ
  covers x := ⟨0, Finset.mem_univ x⟩

theorem fixedBoundarySource_yes : MSSCDecision fixedBoundarySource 1 := by
  have hf : ∀ xs : List (Fin 2), xs.takeWhile (fun _ => false) = [] := by
    intro xs
    cases xs <;> simp [List.takeWhile]
  refine ⟨Finset.univ.toList, List.Perm.refl _, ?_⟩
  simp [msscCost, firstCover, fixedBoundarySource, hf]

noncomputable def fixedYesTarget : AnyBlockTarget :=
  ⟨1, 2, canonicalBlockTarget fixedBoundarySource 1⟩

noncomputable def fixedNoTarget : AnyBlockTarget :=
  ⟨1, 2, ⟨canonicalBlockTree fixedBoundarySource, 0⟩⟩

theorem fixedYesTarget_accept : AnyTargetAccepted fixedYesTarget := by
  obtain ⟨bits, hb, hc⟩ := (full_mssc_bit_reduction fixedBoundarySource 1
    (by decide) (by decide) (by decide) (by decide)).mp fixedBoundarySource_yes
  exact ⟨bits, hc⟩

theorem starScore_pos_of_mixed_missing {A : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (tip : A → S) (T : BTree A)
    (hm : 2 ≤ (observed tip T).card) (z : S)
    (hz : z ∈ univ) (hn : z ∉ observed tip T) : 0 < starScore univ tip T := by
  cases T with
  | leaf a => simp [observed] at hm
  | node l r =>
      have hp : 0 < (univ \ observed tip (.node l r)).card :=
        Finset.card_pos.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hz, hn⟩⟩
      simp only [starScore, observed] at hp ⊢
      omega

theorem fixedBoundarySource_fixedCost_pos :
    0 < realizedFixedCost (canonicalBlockTree fixedBoundarySource) := by
  have hm : 2 ≤ (observed Prod.snd (canonicalBlockTree fixedBoundarySource none)).card := by
    rw [observed_canonicalBlockTree]
    have h := Finset.card_le_card (markers_subset_blockTypes fixedBoundarySource none)
    simpa only [markers_card] using h
  have hn : (Sum.inl (0 : Fin 1) : Terminal 1 2) ∉
      observed Prod.snd (canonicalBlockTree fixedBoundarySource none) := by
    rw [observed_canonicalBlockTree]
    simp [blockTypes, markers]
  have hp := starScore_pos_of_mixed_missing Finset.univ Prod.snd
    (canonicalBlockTree fixedBoundarySource none) hm (Sum.inl (0 : Fin 1))
    (Finset.mem_univ _) hn
  have hs : starScore Finset.univ Prod.snd (canonicalBlockTree fixedBoundarySource none) ≤
      realizedFixedCost (canonicalBlockTree fixedBoundarySource) := by
    unfold realizedFixedCost
    exact Finset.single_le_sum (fun b hb => Nat.zero_le _) (Finset.mem_univ none)
  exact hp.trans_le hs

theorem standardCanonicalRefinement_score_lower {N m : ℕ} (D : MSSCInstance N m)
    (T : BTree (Cell N m)) (hT : StandardBlockRefinement (canonicalBlockTree D) T) :
    realizedFixedCost (canonicalBlockTree D) ≤ starScore Finset.univ Prod.snd T := by
  obtain ⟨xs, hp, hf⟩ := (standardCanonicalRefinement_iff_frontier D T).mp hT
  obtain ⟨t, ht, hi⟩ := BlockFrontier.has_skeleton (canonicalBlockTree D) hf
  have hv : ValidJoiningTree t := by simpa only [ValidJoiningTree, ht] using hp
  rw [TreeIso.starScore_eq Finset.univ Prod.snd hi]
  change realizedFixedCost (canonicalBlockTree D) ≤ realizedScore (canonicalBlockTree D) t
  rw [realizedScore_decomposition D _ (observed_canonicalBlockTree D) t hv]
  omega

theorem fixedNoTarget_reject : ¬ AnyTargetAccepted fixedNoTarget := by
  rintro ⟨bits, hc⟩
  obtain ⟨T, hp, hT, hs⟩ :=
    (checkBlockTargetBits_spec (fixedNoTarget.2.2) bits).mp hc
  have hl := standardCanonicalRefinement_score_lower fixedBoundarySource T hT
  have hpos := fixedBoundarySource_fixedCost_pos
  change starScore Finset.univ Prod.snd T ≤ 0 at hs
  omega

/-- All directly decidable cases use the SAME genuine restricted target
    family. The nontrivial case retains the complete canonical construction. -/
noncomputable def totalMSSCTarget {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) : AnyBlockTarget :=
  if N = 0 then fixedYesTarget
  else if m ≤ 1 then (if N ≤ K then fixedYesTarget else fixedNoTarget)
  else if K < N then fixedNoTarget
  else if m * N ≤ K then fixedYesTarget
  else ⟨N, m, canonicalBlockTarget D K⟩

theorem totalMSSCTarget_correct {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) :
    MSSCDecision D K ↔ AnyTargetAccepted (totalMSSCTarget D K) := by
  by_cases h0 : N = 0
  · subst N
    simpa [totalMSSCTarget] using iff_of_true (msscDecision_zero D K) fixedYesTarget_accept
  · by_cases hsmall : m ≤ 1
    · by_cases hK : N ≤ K
      · simpa [totalMSSCTarget, h0, hsmall, hK] using
          iff_of_true ((msscDecision_small D K hsmall).mpr hK) fixedYesTarget_accept
      · have hn : ¬ MSSCDecision D K := by
          intro h
          exact hK ((msscDecision_small D K hsmall).mp h)
        simpa [totalMSSCTarget, h0, hsmall, hK] using iff_of_false hn fixedNoTarget_reject
    · by_cases hlow : K < N
      · have hn : ¬ MSSCDecision D K := by
          intro h
          have hl := msscDecision_lower D K h
          omega
        simpa [totalMSSCTarget, h0, hsmall, hlow] using iff_of_false hn fixedNoTarget_reject
      · by_cases hhigh : m * N ≤ K
        · simpa [totalMSSCTarget, h0, hsmall, hlow, hhigh] using
            iff_of_true (msscDecision_upper D K hhigh) fixedYesTarget_accept
        · simpa [totalMSSCTarget, h0, hsmall, hlow, hhigh,
            AnyTargetAccepted, checkCanonicalBits] using
            full_mssc_unbounded_bits D K (by omega) (by omega) (by omega) (by omega)

noncomputable def totalRawMSSCTarget (R : RawMSSCRecord) : AnyBlockTarget :=
  match decodeRawMSSC R with
  | none => fixedNoTarget
  | some D => totalMSSCTarget D R.K

theorem totalRawMSSCTarget_correct (R : RawMSSCRecord) :
    RawMSSCDecision R ↔ AnyTargetAccepted (totalRawMSSCTarget R) := by
  classical
  by_cases hv : RawMSSCValid R
  · rw [rawMSSCDecision_valid_iff R hv]
    simpa [totalRawMSSCTarget, decodeRawMSSC_valid R hv] using
      totalMSSCTarget_correct (rawToMSSC R hv) R.K
  · simpa [totalRawMSSCTarget, decodeRawMSSC_invalid R hv] using
      iff_of_false (rawMSSCDecision_invalid R hv) fixedNoTarget_reject

noncomputable def totalSourceBitTarget (bits : List Bool) : AnyBlockTarget :=
  match parseRawMSSC bits with
  | none => fixedNoTarget
  | some R => totalRawMSSCTarget R

theorem totalSourceBitTarget_correct (bits : List Bool) :
    SourceBitMSSCDecision bits ↔ AnyTargetAccepted (totalSourceBitTarget bits) := by
  cases hp : parseRawMSSC bits with
  | none =>
      simpa [totalSourceBitTarget, hp] using
        iff_of_false (sourceBitMSSCDecision_parse_failure bits hp) fixedNoTarget_reject
  | some R =>
      simpa [SourceBitMSSCDecision, totalSourceBitTarget, hp] using totalRawMSSCTarget_correct R

def BlockTargetCartaDecision {N m : ℕ} (G : BlockTargetData N m) (lambda : ℝ) : Prop :=
  ∃ L : StarLabeledTree (Cell N m) (Terminal N m),
    StandardBlockRefinement G.blocks (eraseStar L) ∧ StarFeasible Prod.snd L ∧
      cartaStarScore Prod.snd lambda L ≤ (G.budget : ℝ)

def AnyTargetCartaDecision (G : AnyBlockTarget) (lambda : ℝ) : Prop :=
  BlockTargetCartaDecision G.2.2 lambda

def CanonicalTargetBlocks (G : AnyBlockTarget) : Prop :=
  ∃ D : MSSCInstance G.1 G.2.1, G.2.2.blocks = canonicalBlockTree D

theorem canonicalTargetBlocks_actual_iff (G : AnyBlockTarget) (lambda : ℝ)
    (hG : CanonicalTargetBlocks G) :
    AnyTargetCartaDecision G lambda ↔ AnyTargetAccepted G := by
  rcases G with ⟨N, m, G⟩
  obtain ⟨D, hblocks⟩ := hG
  constructor
  · rintro ⟨L, hT, hf, hs⟩
    have hTc : StandardBlockRefinement (canonicalBlockTree D) (eraseStar L) := by
      simpa only [hblocks] using hT
    have hm := standardCanonicalRefinement_mixed D (eraseStar L) hTc
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm] at hs
    have hc : checkBlockTarget G (eraseStar L) = true :=
      (checkBlockTarget_spec G _).mpr ⟨hT, by exact_mod_cast hs⟩
    refine ⟨treeBits (eraseStar L), ?_⟩
    simpa [checkBlockTargetBits, parseBitTree_encode] using hc
  · rintro ⟨bits, hc⟩
    obtain ⟨T, hp, hT, hs⟩ := (checkBlockTargetBits_spec G bits).mp hc
    have hTc : StandardBlockRefinement (canonicalBlockTree D) T := by
      simpa only [hblocks] using hT
    let L : StarLabeledTree (Cell N m) (Terminal N m) := canonicalStar T
    have he : eraseStar L = T := canonicalStar_erase T
    have hf : StarFeasible Prod.snd L := canonicalStar_feasible Prod.snd T
    have hm : AllInternalMixed Prod.snd (eraseStar L) := by
      rw [he]
      exact standardCanonicalRefinement_mixed D T hTc
    refine ⟨L, by simpa only [he] using hT, hf, ?_⟩
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm, he]
    exact_mod_cast hs

theorem fixedYesTarget_canonical : CanonicalTargetBlocks fixedYesTarget :=
  ⟨fixedBoundarySource, rfl⟩

theorem fixedNoTarget_canonical : CanonicalTargetBlocks fixedNoTarget :=
  ⟨fixedBoundarySource, rfl⟩

theorem totalMSSCTarget_canonical {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) :
    CanonicalTargetBlocks (totalMSSCTarget D K) := by
  unfold totalMSSCTarget
  split_ifs <;> first
    | exact fixedYesTarget_canonical
    | exact fixedNoTarget_canonical
    | exact ⟨D, rfl⟩

theorem totalRawMSSCTarget_canonical (R : RawMSSCRecord) :
    CanonicalTargetBlocks (totalRawMSSCTarget R) := by
  cases hp : decodeRawMSSC R with
  | none => simpa [totalRawMSSCTarget, hp] using fixedNoTarget_canonical
  | some D => simpa [totalRawMSSCTarget, hp] using totalMSSCTarget_canonical D R.K

theorem totalSourceBitTarget_canonical (bits : List Bool) :
    CanonicalTargetBlocks (totalSourceBitTarget bits) := by
  cases hp : parseRawMSSC bits with
  | none => simpa [totalSourceBitTarget, hp] using fixedNoTarget_canonical
  | some R => simpa [totalSourceBitTarget, hp] using totalRawMSSCTarget_canonical R

/-- TOTAL finite map on every source string, retaining the actual objective
    and compatible-label quantifier. This is not a polynomial-machine theorem. -/
theorem full_total_source_actual_reduction (bits : List Bool) (lambda : ℝ) :
    SourceBitMSSCDecision bits ↔ AnyTargetCartaDecision (totalSourceBitTarget bits) lambda := by
  exact (totalSourceBitTarget_correct bits).trans
    (canonicalTargetBlocks_actual_iff (totalSourceBitTarget bits) lambda
      (totalSourceBitTarget_canonical bits)).symm

/- Still absent: elaboration; independent target-instance serialization and
its valid-domain parser; encoded total polynomial constructor/verifier proofs;
compatible formal source hardness and its composition. The preceding total
finite equivalence is not asserted to establish formal NP-completeness. -/

end PolytomyReductionModel
