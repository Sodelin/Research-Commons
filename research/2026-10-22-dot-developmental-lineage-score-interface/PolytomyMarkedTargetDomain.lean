/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/certificate.

Independent polynomially checkable marked-star target DOMAIN. Membership
does not ask for an MSSC source, a canonical-construction witness or a valid
refinement. It is a promised restricted family of the original objective,
containing every output of the total source reduction.
-/
import PolytomyTotalSourceReduction

namespace PolytomyReductionModel

structure MarkedTargetDomain {N m : ℕ} (G : BlockTargetData N m) : Prop where
  positiveN : 0 < N
  degree : 2 ≤ m
  blockNodup : ∀ b, (leaves (G.blocks b)).Nodup
  blockDisjoint : ∀ b c, b ≠ c → Disjoint (cellSet (G.blocks b)) (cellSet (G.blocks c))
  blockMixed : ∀ b, AllInternalMixed Prod.snd (G.blocks b)
  blockMarkers : ∀ b, markers N m ⊆ observed Prod.snd (G.blocks b)
  typeCoverage : (Finset.univ.biUnion fun b => observed Prod.snd (G.blocks b)) = Finset.univ

theorem marked_graft_mixed {N m : ℕ} (G : BlockTargetData N m)
    (h : MarkedTargetDomain G) (t : BTree (Block m)) :
    AllInternalMixed Prod.snd (graft G.blocks t) := by
  have hmarks : ∀ q : BTree (Block m),
      markers N m ⊆ observed Prod.snd (graft G.blocks q) := by
    intro q
    induction q with
    | leaf b => exact h.blockMarkers b
    | node l r ihl ihr => exact ihl.trans Finset.subset_union_left
  induction t with
  | leaf b => exact h.blockMixed b
  | node l r ihl ihr =>
      refine ⟨?_, ihl, ihr⟩
      have hc := Finset.card_le_card (hmarks (.node l r))
      simpa only [markers_card] using hc

theorem marked_refinement_mixed {N m : ℕ} (G : BlockTargetData N m)
    (h : MarkedTargetDomain G) (T : BTree (Cell N m))
    (hT : StandardBlockRefinement G.blocks T) : AllInternalMixed Prod.snd T := by
  obtain ⟨xs, hp, hf⟩ := standardBlockRefinement_has_frontier G.blocks
    h.blockNodup h.blockDisjoint T hT
  obtain ⟨t, ht, hi⟩ := BlockFrontier.has_skeleton G.blocks hf
  exact (TreeIso.mixed_iff Prod.snd hi).mpr (marked_graft_mixed G h t)

/-- Generic checker correctness on an INDEPENDENT target domain. No D,
    source cover proof or canonical reconstruction is provided to it. -/
theorem marked_target_actual_iff_bits {N m : ℕ} (G : BlockTargetData N m)
    (h : MarkedTargetDomain G) (lambda : ℝ) :
    BlockTargetCartaDecision G lambda ↔
      ∃ bits : List Bool, checkBlockTargetBits G bits = true := by
  constructor
  · rintro ⟨L, hT, hf, hs⟩
    have hm := marked_refinement_mixed G h (eraseStar L) hT
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm] at hs
    have hc : checkBlockTarget G (eraseStar L) = true :=
      (checkBlockTarget_spec G _).mpr ⟨hT, by exact_mod_cast hs⟩
    refine ⟨treeBits (eraseStar L), ?_⟩
    simpa [checkBlockTargetBits, parseBitTree_encode] using hc
  · rintro ⟨bits, hc⟩
    obtain ⟨T, hp, hT, hs⟩ := (checkBlockTargetBits_spec G bits).mp hc
    let L : StarLabeledTree (Cell N m) (Terminal N m) := canonicalStar T
    have he : eraseStar L = T := canonicalStar_erase T
    have hf : StarFeasible Prod.snd L := canonicalStar_feasible Prod.snd T
    have hm : AllInternalMixed Prod.snd (eraseStar L) := by
      rw [he]
      exact marked_refinement_mixed G h T hT
    refine ⟨L, by simpa only [he] using hT, hf, ?_⟩
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm, he]
    exact_mod_cast hs

theorem blockTypes_cover_terminal {N m : ℕ} (D : MSSCInstance N m)
    (s : Terminal N m) : ∃ b : Block m, s ∈ blockTypes D b := by
  rcases s with x | (z | k)
  · obtain ⟨i, hi⟩ := D.covers x
    exact ⟨some i, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hi, rfl⟩)⟩
  · exact ⟨none, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩)⟩
  · exact ⟨none, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)⟩

theorem canonical_blocks_typeCoverage {N m : ℕ} (D : MSSCInstance N m) :
    (Finset.univ.biUnion fun b => observed Prod.snd (canonicalBlockTree D b)) =
      (Finset.univ : Finset (Terminal N m)) := by
  apply Finset.eq_univ_of_forall
  intro s
  obtain ⟨b, hb⟩ := blockTypes_cover_terminal D s
  exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, by
    simpa only [observed_canonicalBlockTree] using hb⟩

theorem canonical_blocks_marked {N m : ℕ} (D : MSSCInstance N m)
    (budget : ℕ) (hN : 0 < N) (hm : 2 ≤ m) :
    MarkedTargetDomain (⟨canonicalBlockTree D, budget⟩ : BlockTargetData N m) := by
  refine ⟨hN, hm, canonicalBlockTree_cells_nodup D,
    canonicalBlock_cellSets_disjoint D, canonicalBlockTree_mixed D, ?_,
    canonical_blocks_typeCoverage D⟩
  intro b
  simpa only [observed_canonicalBlockTree] using markers_subset_blockTypes D b

theorem totalMSSCTarget_dimensions {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) :
    0 < (totalMSSCTarget D K).1 ∧ 2 ≤ (totalMSSCTarget D K).2.1 := by
  unfold totalMSSCTarget
  split_ifs <;> simp_all [fixedYesTarget, fixedNoTarget] <;> omega

theorem totalRawMSSCTarget_dimensions (R : RawMSSCRecord) :
    0 < (totalRawMSSCTarget R).1 ∧ 2 ≤ (totalRawMSSCTarget R).2.1 := by
  cases hp : decodeRawMSSC R with
  | none => simp [totalRawMSSCTarget, hp, fixedNoTarget]
  | some D => simpa [totalRawMSSCTarget, hp] using totalMSSCTarget_dimensions D R.K

theorem totalSourceBitTarget_dimensions (bits : List Bool) :
    0 < (totalSourceBitTarget bits).1 ∧ 2 ≤ (totalSourceBitTarget bits).2.1 := by
  cases hp : parseRawMSSC bits with
  | none => simp [totalSourceBitTarget, hp, fixedNoTarget]
  | some R => simpa [totalSourceBitTarget, hp] using totalRawMSSCTarget_dimensions R

theorem canonical_positive_target_marked (G : AnyBlockTarget)
    (hc : CanonicalTargetBlocks G) (hN : 0 < G.1) (hm : 2 ≤ G.2.1) :
    MarkedTargetDomain G.2.2 := by
  rcases G with ⟨N, m, G⟩
  obtain ⟨D, hblocks⟩ := hc
  have hG : G = (⟨canonicalBlockTree D, G.budget⟩ : BlockTargetData N m) := by
    cases G with
    | mk blocks budget => simp_all
  rw [hG]
  exact canonical_blocks_marked D G.budget hN hm

theorem totalSourceBitTarget_marked (bits : List Bool) :
    MarkedTargetDomain (totalSourceBitTarget bits).2.2 := by
  exact canonical_positive_target_marked (totalSourceBitTarget bits)
    (totalSourceBitTarget_canonical bits) (totalSourceBitTarget_dimensions bits).1
    (totalSourceBitTarget_dimensions bits).2

/-- Every produced target is a valid member of this independently defined
    marked-star family, and its decision retains the original actual score. -/
theorem full_total_marked_actual_reduction (bits : List Bool) (lambda : ℝ) :
    MarkedTargetDomain (totalSourceBitTarget bits).2.2 ∧
      (SourceBitMSSCDecision bits ↔
        BlockTargetCartaDecision (totalSourceBitTarget bits).2.2 lambda) := by
  exact ⟨totalSourceBitTarget_marked bits, full_total_source_actual_reduction bits lambda⟩

/- A finite target-domain predicate is now explicit and independent of the
source. Its raw-record/bit-level validator must be constructed without looping
over unvalidated huge target dimensions. No polynomial machine is claimed. -/

end PolytomyReductionModel
