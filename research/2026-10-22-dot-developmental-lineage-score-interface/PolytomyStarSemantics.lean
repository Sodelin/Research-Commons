/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/kernel execution or certificate.

Semantic continuation of the full PolytomyReductionModel source proposal.
The goal is the actual forced star-map labeling score, not a surrogate
sum of labels. Complexity encodings and the external refinement interface
remain separate obligations. No new biological assumptions are introduced.
-/
import PolytomyReductionModel

namespace PolytomyReductionModel

noncomputable section

universe u v

def AllInternalMixed {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) : BTree A → Prop
  | .leaf _ => True
  | .node l r => 2 ≤ (observed tip (.node l r)).card ∧
      AllInternalMixed tip l ∧ AllInternalMixed tip r

theorem allInternalMixed_of_nodup {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) (t : BTree A) (hn : ((leaves t).map tip).Nodup) :
    AllInternalMixed tip t := by
  revert hn
  induction t with
  | leaf a => intro hn; trivial
  | node l r ihl ihr =>
      intro hn
      have hnr : (((leaves l).map tip) ++ ((leaves r).map tip)).Nodup := by
        simpa only [leaves, List.map_append] using hn
      have hl := ihl hnr.of_append_left
      have hr := ihr hnr.of_append_right
      refine ⟨?_, hl, hr⟩
      rw [observed_eq_leaves_image, List.toFinset_card_of_nodup hn, List.length_map]
      have hll := leaves_length l
      have hlr := leaves_length r
      simp only [leaves, List.length_append]
      omega

theorem fixedBlockTree_type_nodup {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : ((leaves (fixedBlockTree D b)).map Prod.snd).Nodup := by
  rw [leaves_fixedBlockTree]
  simpa [blockCells, List.map_map] using (blockTypes D b).nodup_toList

theorem fixedBlockTree_mixed {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : AllInternalMixed Prod.snd (fixedBlockTree D b) :=
  allInternalMixed_of_nodup Prod.snd _ (fixedBlockTree_type_nodup D b)

theorem markers_card (N m : ℕ) : (markers N m).card = 2 := by
  unfold markers
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Sum.inr_injective (Sum.inr_injective h)

theorem markers_subset_blockTypes {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : markers N m ⊆ blockTypes D b := by
  cases b <;> exact Finset.subset_union_right

theorem markers_subset_graft {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) :
    markers N m ⊆ observed Prod.snd (graft (fixedBlockTree D) t) := by
  induction t with
  | leaf b =>
      simpa only [graft, observed_fixedBlockTree] using markers_subset_blockTypes D b
  | node l r ihl ihr =>
      exact ihl.trans Finset.subset_union_left

theorem every_graft_internal_mixed {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) :
    AllInternalMixed Prod.snd (graft (fixedBlockTree D) t) := by
  induction t with
  | leaf b => exact fixedBlockTree_mixed D b
  | node l r ihl ihr =>
      refine ⟨?_, ihl, ihr⟩
      have h := Finset.card_le_card (markers_subset_graft D (.node l r))
      simpa only [markers_card] using h

/-- A decorated cell tree. A leaf's state is forced to its observed singleton;
    an internal state is either the full potency (none) or a singleton (some). -/
inductive StarLabeledTree (A : Type u) (S : Type v) where
  | leaf (a : A)
  | node (state : Option S) («left» «right» : StarLabeledTree A S)

def eraseStar {A : Type u} {S : Type v} : StarLabeledTree A S → BTree A
  | .leaf a => .leaf a
  | .node _ l r => .node (eraseStar l) (eraseStar r)

def starRoot {A : Type u} {S : Type v} (tip : A → S) :
    StarLabeledTree A S → Option S
  | .leaf a => some (tip a)
  | .node p _ _ => p

def StarReaches {S : Type v} (p q : Option S) : Prop := p = none ∨ p = q

def StarDirect {S : Type v} (p q : Option S) : Prop := p = none ∧ q ≠ none

def StarFeasible {A : Type u} {S : Type v} (tip : A → S) :
    StarLabeledTree A S → Prop
  | .leaf _ => True
  | .node p l r => StarReaches p (starRoot tip l) ∧
      StarReaches p (starRoot tip r) ∧ StarFeasible tip l ∧ StarFeasible tip r

def starPotency {S : Type v} [Fintype S] [DecidableEq S] : Option S → Finset S
  | none => Finset.univ
  | some s => {s}

def canonicalStar {A : Type u} {S : Type v} : BTree A → StarLabeledTree A S
  | .leaf a => .leaf a
  | .node l r => .node none (canonicalStar l) (canonicalStar r)

theorem canonicalStar_erase {A : Type u} {S : Type v} (t : BTree A) :
    eraseStar (canonicalStar (S := S) t) = t := by
  induction t with
  | leaf a => rfl
  | node l r ihl ihr => simp only [canonicalStar, eraseStar, ihl, ihr]

theorem canonicalStar_feasible {A : Type u} {S : Type v}
    (tip : A → S) (t : BTree A) : StarFeasible tip (canonicalStar t) := by
  induction t with
  | leaf a => trivial
  | node l r ihl ihr =>
      exact ⟨Or.inl rfl, Or.inl rfl, ihl, ihr⟩

theorem feasible_singleton_descendants {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) (L : StarLabeledTree A S) (s : S)
    (hf : StarFeasible tip L) (hr : starRoot tip L = some s) :
    observed tip (eraseStar L) ⊆ {s} := by
  revert hf hr
  induction L with
  | leaf a =>
      intro hf hr
      have ha : tip a = s := Option.some_injective _ hr
      simp [eraseStar, observed, ha]
  | node p l r ihl ihr =>
      intro hf hr
      have hp : p = some s := hr
      subst p
      obtain ⟨hleft, hright, hfl, hfr⟩ := hf
      have hrl : starRoot tip l = some s := by
        rcases hleft with hfalse | heq
        · cases hfalse
        · exact heq.symm
      have hrr : starRoot tip r = some s := by
        rcases hright with hfalse | heq
        · cases hfalse
        · exact heq.symm
      exact Finset.union_subset (ihl hfl hrl) (ihr hfr hrr)

theorem mixed_node_state_forced {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) (p : Option S) (l r : StarLabeledTree A S)
    (hf : StarFeasible tip (.node p l r))
    (hm : 2 ≤ (observed tip (eraseStar (.node p l r))).card) : p = none := by
  cases p with
  | none => rfl
  | some s =>
      have hsub := feasible_singleton_descendants tip (.node (some s) l r) s hf rfl
      have hc := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hc
      omega

theorem mixed_feasible_labeling_unique {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) (L : StarLabeledTree A S)
    (hf : StarFeasible tip L) (hm : AllInternalMixed tip (eraseStar L)) :
    L = canonicalStar (eraseStar L) := by
  revert hf hm
  induction L with
  | leaf a => intro hf hm; rfl
  | node p l r ihl ihr =>
      intro hf hm
      have hp := mixed_node_state_forced tip p l r hf hm.1
      obtain ⟨hl, hr, hfl, hfr⟩ := hf
      have hel := ihl hfl hm.2.1
      have her := ihr hfr hm.2.2
      change .node p l r = .node none (canonicalStar (eraseStar l))
        (canonicalStar (eraseStar r))
      rw [hp]
      exact congrArg₂ (StarLabeledTree.node none) hel her

/-- Exact usual Carta resolution cost on the star, with unit resolution
    weights. Its value is zero for every compatible edge for any real lambda. -/
def starResolution {S : Type v} [DecidableEq S]
    (lambda : ℝ) (p q : Option S) : ℝ :=
  if p ≠ q ∧ ¬ StarDirect p q then lambda else 0

theorem starResolution_zero {S : Type v} [DecidableEq S]
    (lambda : ℝ) (p q : Option S) (h : StarReaches p q) :
    starResolution lambda p q = 0 := by
  rcases h with hp | hpq
  · subst p
    by_cases hq : q = none <;> simp [starResolution, StarDirect, hq]
  · simp [starResolution, hpq]

def cartaStarScore {A : Type u} {S : Type v} [Fintype S] [DecidableEq S]
    (tip : A → S) (lambda : ℝ) : StarLabeledTree A S → ℝ
  | .leaf _ => 0
  | .node p l r => cartaStarScore tip lambda l + cartaStarScore tip lambda r +
      ((starPotency p \ observed tip (eraseStar (.node p l r))).card : ℝ) +
      starResolution lambda p (starRoot tip l) +
      starResolution lambda p (starRoot tip r)

theorem feasible_mixed_score_exact {A : Type u} {S : Type v}
    [Fintype S] [DecidableEq S] (tip : A → S) (lambda : ℝ)
    (L : StarLabeledTree A S) (hf : StarFeasible tip L)
    (hm : AllInternalMixed tip (eraseStar L)) :
    cartaStarScore tip lambda L = (starScore Finset.univ tip (eraseStar L) : ℝ) := by
  revert hf hm
  induction L with
  | leaf a => intro hf hm; rfl
  | node p l r ihl ihr =>
      intro hf hm
      have hp := mixed_node_state_forced tip p l r hf hm.1
      obtain ⟨hl, hr, hfl, hfr⟩ := hf
      have hel := ihl hfl hm.2.1
      have her := ihr hfr hm.2.2
      simp only [cartaStarScore, starResolution_zero lambda p _ hl,
        starResolution_zero lambda p _ hr, hel, her, hp, starPotency,
        eraseStar, starScore, observed, Nat.cast_add, add_zero]

/-- The actual D_lambda score on every compatible labeling of each gadget
    refinement equals the finite reduction model's fullScore. -/
theorem gadget_carta_score_exact {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) (lambda : ℝ)
    (L : StarLabeledTree (Cell N m) (Terminal N m))
    (he : eraseStar L = graft (fixedBlockTree D) t)
    (hf : StarFeasible Prod.snd L) :
    cartaStarScore Prod.snd lambda L = (fullScore D t : ℝ) := by
  have hm : AllInternalMixed Prod.snd (eraseStar L) := by
    rw [he]
    exact every_graft_internal_mixed D t
  rw [feasible_mixed_score_exact Prod.snd lambda L hf hm, he]
  rfl

def CartaStarRefinementDecision {N m : ℕ} (D : MSSCInstance N m)
    (lambda : ℝ) (K : ℕ) : Prop :=
  ∃ t : BTree (Block m),
    ∃ L : StarLabeledTree (Cell N m) (Terminal N m),
      ValidJoiningTree t ∧ eraseStar L = graft (fixedBlockTree D) t ∧
      StarFeasible Prod.snd L ∧
      cartaStarScore Prod.snd lambda L ≤ (fixedCost D + K - N : ℕ)

/-- Adds the actual compatible-label quantifier and the real-valued full
    sampling/resolution objective to the finite reduction decision problem. -/
theorem cartaStarDecision_iff_refinementDecision {N m : ℕ}
    (D : MSSCInstance N m) (lambda : ℝ) (K : ℕ) :
    CartaStarRefinementDecision D lambda K ↔ RefinementDecision D K := by
  constructor
  · rintro ⟨t, L, ht, he, hf, hcost⟩
    rw [gadget_carta_score_exact D t lambda L he hf] at hcost
    refine ⟨t, ht, ?_⟩
    exact_mod_cast hcost
  · rintro ⟨t, ht, hcost⟩
    let L : StarLabeledTree (Cell N m) (Terminal N m) :=
      canonicalStar (graft (fixedBlockTree D) t)
    have he : eraseStar L = graft (fixedBlockTree D) t := canonicalStar_erase _
    have hf : StarFeasible Prod.snd L := canonicalStar_feasible Prod.snd _
    refine ⟨t, L, ht, he, hf, ?_⟩
    rw [gadget_carta_score_exact D t lambda L he hf]
    exact_mod_cast hcost

/-- Proposed whole finite reduction, now including feasible star-map labels
    and the actual resolution formula. Still UNELABORATED and not a formal
    polynomial many-one reduction or NP-completeness certificate. -/
theorem full_carta_star_reduction {N m : ℕ} (D : MSSCInstance N m)
    (lambda : ℝ) (K : ℕ) (hN : 0 < N) (hm : 2 ≤ m)
    (hNK : N ≤ K) (hKmN : K ≤ m * N) :
    MSSCDecision D K ↔ CartaStarRefinementDecision D lambda K := by
  rw [cartaStarDecision_iff_refinementDecision]
  exact fullReductionClaim N m D K hN hm hNK hKmN

theorem leaves_graft_flatMap {I : Type u} {A : Type v}
    (blocks : I → BTree A) (t : BTree I) :
    leaves (graft blocks t) = (leaves t).flatMap (fun i => leaves (blocks i)) := by
  induction t with
  | leaf i => simp [graft, leaves]
  | node l r ihl ihr => simp [graft, leaves, ihl, ihr]

theorem fixedBlockTree_cells_nodup {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : (leaves (fixedBlockTree D b)).Nodup := by
  rw [leaves_fixedBlockTree]
  apply List.Nodup.map
  · intro a c h
    exact congrArg Prod.snd h
  · exact (blockTypes D b).nodup_toList

/-- Repeated terminal TYPES across blocks do not duplicate CELL identities. -/
theorem valid_graft_cells_nodup {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) (ht : ValidJoiningTree t) :
    (leaves (graft (fixedBlockTree D) t)).Nodup := by
  have hn : (leaves t).Nodup := ht.nodup_iff.mpr Finset.univ.nodup_toList
  rw [leaves_graft_flatMap]
  apply List.nodup_flatMap.mpr
  constructor
  · intro b hb
    exact fixedBlockTree_cells_nodup D b
  · exact hn.imp fun {b c} hbc x hx hy => by
      rw [leaves_fixedBlockTree] at hx hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      obtain ⟨z, hz, he⟩ := List.mem_map.mp hy
      exact hbc (congrArg Prod.fst he).symm

theorem terminal_card (N m : ℕ) :
    Fintype.card (Terminal N m) = N + m * N + 3 := by
  simp [Terminal, privateCount]; omega

theorem fixedBlockTree_leaf_bound {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : (leaves (fixedBlockTree D b)).length ≤ N + m * N + 3 := by
  rw [leaves_fixedBlockTree]
  have h := Finset.card_le_card (Finset.subset_univ (blockTypes D b))
  simpa [blockCells, terminal_card] using h

theorem graft_leaf_count {I : Type u} {A : Type v}
    (blocks : I → BTree A) (t : BTree I) :
    (leaves (graft blocks t)).length =
      blockScoreSum (fun i => (leaves (blocks i)).length) t := by
  induction t with
  | leaf i => rfl
  | node l r ihl ihr => simp only [graft, leaves, List.length_append,
      blockScoreSum, ihl, ihr]

/-- A deliberately loose polynomial bound suffices for the explicit gadget;
    no fixed alphabet, hidden-size cap, or bounded degree is assumed. -/
theorem valid_graft_leaf_bound {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) (ht : ValidJoiningTree t) :
    (leaves (graft (fixedBlockTree D) t)).length ≤
      (m + 1) * (N + m * N + 3) := by
  rw [graft_leaf_count, blockScoreSum_as_list,
    (ht.map (fun b => (leaves (fixedBlockTree D b)).length)).sum_eq,
    Finset.sum_map_toList]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b hb => fixedBlockTree_leaf_bound D b)
  simpa using h

def vertexCount {A : Type u} : BTree A → ℕ
  | .leaf _ => 1
  | .node l r => vertexCount l + vertexCount r + 1

theorem vertexCount_add_one {A : Type u} (t : BTree A) :
    vertexCount t + 1 = 2 * (leaves t).length := by
  induction t with
  | leaf a => simp [vertexCount, leaves]
  | node l r ihl ihr =>
      simp only [vertexCount, leaves, List.length_append]
      omega

theorem valid_graft_vertex_bound {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) (ht : ValidJoiningTree t) :
    vertexCount (graft (fixedBlockTree D) t) + 1 ≤
      2 * ((m + 1) * (N + m * N + 3)) := by
  rw [vertexCount_add_one]
  exact Nat.mul_le_mul_left 2 (valid_graft_leaf_bound D t ht)

theorem starScore_bound {A : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (tip : A → S) (t : BTree A) :
    starScore univ tip t ≤ internalCount t * univ.card := by
  induction t with
  | leaf a => simp [starScore, internalCount]
  | node l r ihl ihr =>
      have h := Finset.card_le_card
        (Finset.sdiff_subset : univ \ (observed tip l ∪ observed tip r) ⊆ univ)
      simp only [starScore, internalCount, Nat.add_mul, Nat.one_mul]
      omega

end

end PolytomyReductionModel
