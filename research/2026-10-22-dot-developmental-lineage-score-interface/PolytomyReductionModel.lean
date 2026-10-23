/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No Lean/Lake execution or certificate.

This file proposes proof terms for the actual all-refinement MSSC gadget,
full decision equivalence and exact minimum-cost shift. It does NOT claim
that these terms elaborate, or that NP-completeness has been formalized.
The full chain is retained rather than replaced by a weaker component.
No additional axioms or sorry placeholders are introduced.
-/
import Mathlib

namespace PolytomyReductionModel

noncomputable section

universe u v

inductive BTree (A : Type u) where
  | leaf (a : A)
  | node («left» «right» : BTree A)
  deriving DecidableEq

def leaves {A : Type u} : BTree A → List A
  | .leaf a => [a]
  | .node l r => leaves l ++ leaves r

def observed {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) : BTree A → Finset S
  | .leaf a => {tip a}
  | .node l r => observed tip l ∪ observed tip r

def graft {I : Type u} {A : Type v} (blocks : I → BTree A) :
    BTree I → BTree A
  | .leaf i => blocks i
  | .node l r => .node (graft blocks l) (graft blocks r)

def joinedObserved {I : Type u} {S : Type v} [DecidableEq S]
    (B : I → Finset S) : BTree I → Finset S
  | .leaf i => B i
  | .node l r => joinedObserved B l ∪ joinedObserved B r

def starScore {A : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (tip : A → S) : BTree A → ℕ
  | .leaf _ => 0
  | .node l r => starScore univ tip l + starScore univ tip r +
      (univ \ (observed tip l ∪ observed tip r)).card

def joiningScore {I : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (B : I → Finset S) : BTree I → ℕ
  | .leaf _ => 0
  | .node l r => joiningScore univ B l + joiningScore univ B r +
      (univ \ (joinedObserved B l ∪ joinedObserved B r)).card

def blockScoreSum {I : Type u} (cost : I → ℕ) : BTree I → ℕ
  | .leaf i => cost i
  | .node l r => blockScoreSum cost l + blockScoreSum cost r

theorem observed_graft {I : Type u} {A : Type v} {S : Type*}
    [DecidableEq S] (tip : A → S) (blocks : I → BTree A) (t : BTree I) :
    observed tip (graft blocks t) =
      joinedObserved (fun i => observed tip (blocks i)) t := by
  induction t with
  | leaf i => rfl
  | node l r ihl ihr =>
      simp only [graft, observed, joinedObserved, ihl, ihr]

theorem star_graft_score {I : Type u} {A : Type v} {S : Type*}
    [DecidableEq S] (univ : Finset S) (tip : A → S)
    (blocks : I → BTree A) (t : BTree I) :
    starScore univ tip (graft blocks t) =
      blockScoreSum (fun i => starScore univ tip (blocks i)) t +
      joiningScore univ (fun i => observed tip (blocks i)) t := by
  induction t with
  | leaf i => simp [graft, starScore, blockScoreSum, joiningScore]
  | node l r ihl ihr =>
      simp only [graft, starScore, blockScoreSum, joiningScore,
        observed_graft, ihl, ihr]
      omega

inductive IsCaterpillar {A : Type u} : BTree A → Prop where
  | leaf (a : A) : IsCaterpillar (.leaf a)
  | extend {t : BTree A} (h : IsCaterpillar t) (a : A) :
      IsCaterpillar (.node t (.leaf a))

def support {A : Type u} [DecidableEq A] (t : BTree A) : Finset A :=
  (leaves t).toFinset

def mergeScore {A : Type u} [DecidableEq A]
    (f : Finset A → ℕ) : BTree A → ℕ
  | .leaf _ => 0
  | .node l r => mergeScore f l + mergeScore f r +
      f (support l ∪ support r)

def internalCount {A : Type u} : BTree A → ℕ
  | .leaf _ => 0
  | .node l r => internalCount l + internalCount r + 1

def attach {A : Type u} (t : BTree A) : List A → BTree A
  | [] => t
  | a :: rest => attach (.node t (.leaf a)) rest

theorem leaves_length {A : Type u} (t : BTree A) :
    (leaves t).length = internalCount t + 1 := by
  induction t with
  | leaf a => simp [leaves, internalCount]
  | node l r ihl ihr => simp [leaves, internalCount, ihl, ihr]; omega

theorem leaves_attach {A : Type u} (t : BTree A) (xs : List A) :
    leaves (attach t xs) = leaves t ++ xs := by
  induction xs generalizing t with
  | nil => simp [attach]
  | cons a xs ih => simp [attach, ih, leaves, List.append_assoc]

theorem support_node {A : Type u} [DecidableEq A] (l r : BTree A) :
    support (.node l r) = support l ∪ support r := by
  ext a
  simp [support, leaves]

theorem support_attach {A : Type u} [DecidableEq A]
    (t : BTree A) (xs : List A) :
    support (attach t xs) = support t ∪ xs.toFinset := by
  ext a
  simp [support, leaves_attach]

theorem caterpillar_attach {A : Type u} (t : BTree A) (xs : List A)
    (h : IsCaterpillar t) : IsCaterpillar (attach t xs) := by
  induction xs generalizing t with
  | nil => exact h
  | cons a xs ih => exact ih (.node t (.leaf a)) (.extend h a)

/-- Every old internal node costs at least the cost of the whole subtree.
    This supplies exactly q-1 old terms for a q-leaf subtree. -/
theorem internalCount_mul_le_score {A : Type u} [DecidableEq A]
    (f : Finset A → ℕ) (hf : ∀ J K, J ⊆ K → f K ≤ f J)
    (t : BTree A) : internalCount t * f (support t) ≤ mergeScore f t := by
  induction t with
  | leaf a => simp [internalCount, mergeScore]
  | node l r ihl ihr =>
      have hl : f (support l ∪ support r) ≤ f (support l) :=
        hf _ _ Finset.subset_union_left
      have hr : f (support l ∪ support r) ≤ f (support r) :=
        hf _ _ Finset.subset_union_right
      have hml := Nat.mul_le_mul_left (internalCount l) hl
      have hmr := Nat.mul_le_mul_left (internalCount r) hr
      simp only [internalCount, support_node, mergeScore, Nat.add_mul,
        Nat.one_mul]
      omega

/-- Retaining the final-root term avoids the incorrect q-versus-q-1 bound. -/
theorem attach_score_telescope {A : Type u} [DecidableEq A]
    (f : Finset A → ℕ) (hf : ∀ J K, J ⊆ K → f K ≤ f J)
    (t : BTree A) (xs : List A) :
    mergeScore f (attach t xs) + f (support t) ≤
      mergeScore f t + xs.length * f (support t) +
        f (support (attach t xs)) := by
  induction xs generalizing t with
  | nil => simp [attach]
  | cons a xs ih =>
      let u : BTree A := .node t (.leaf a)
      have h := ih u
      have hsub : support t ⊆ support u := by
        change support t ⊆ support (.node t (.leaf a))
        rw [support_node]
        exact Finset.subset_union_left
      have hm := Nat.mul_le_mul_left xs.length (hf _ _ hsub)
      have hu : mergeScore f u = mergeScore f t + f (support u) := by
        simp [u, mergeScore, support_node]
      rw [hu] at h
      change mergeScore f (attach u xs) + f (support t) ≤
        mergeScore f t + (xs.length + 1) * f (support t) +
          f (support (attach u xs))
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- Replace the cheaper-oriented root's other subtree by successive leaves. -/
theorem flatten_other_subtree {A : Type u} [DecidableEq A]
    (f : Finset A → ℕ) (hf : ∀ J K, J ⊆ K → f K ≤ f J)
    (a b : BTree A) (hab : f (support a) ≤ f (support b)) :
    mergeScore f (attach a (leaves b)) ≤ mergeScore f (.node a b) := by
  have ht := attach_score_telescope f hf a (leaves b)
  have hb := internalCount_mul_le_score f hf b
  have hm := Nat.mul_le_mul_left (internalCount b) hab
  have hs : support (attach a (leaves b)) = support a ∪ support b := by
    rw [support_attach]
    rfl
  rw [leaves_length, hs, Nat.add_mul, Nat.one_mul] at ht
  simp only [mergeScore]
  omega

/-- Proposed complete proof of the structural exchange, over ALL binary trees.
    No no-repetition, optimality-oracle, or disjoint-type hypothesis is used. -/
theorem caterpillar_exchange {A : Type u} [DecidableEq A]
    (f : Finset A → ℕ) (hf : ∀ J K, J ⊆ K → f K ≤ f J)
    (t : BTree A) : ∃ c : BTree A,
      (leaves c).Perm (leaves t) ∧ IsCaterpillar c ∧
        mergeScore f c ≤ mergeScore f t := by
  induction t with
  | leaf a => exact ⟨.leaf a, List.Perm.refl _, .leaf a, le_rfl⟩
  | node l r ihl ihr =>
      by_cases hlr : f (support l) ≤ f (support r)
      · obtain ⟨c, hp, hc, hcost⟩ := ihl
        have hs : support c = support l :=
          List.toFinset_eq_of_perm _ _ hp
        refine ⟨attach c (leaves r), ?_, caterpillar_attach c _ hc, ?_⟩
        · rw [leaves_attach]
          exact hp.append_right _
        · have hflat := flatten_other_subtree f hf c r (by simpa [hs] using hlr)
          have hnode : mergeScore f (.node c r) ≤ mergeScore f (.node l r) := by
            simp only [mergeScore, hs]
            omega
          exact hflat.trans hnode
      · obtain ⟨c, hp, hc, hcost⟩ := ihr
        have hrl : f (support r) ≤ f (support l) := by omega
        have hs : support c = support r :=
          List.toFinset_eq_of_perm _ _ hp
        refine ⟨attach c (leaves l), ?_, caterpillar_attach c _ hc, ?_⟩
        · rw [leaves_attach]
          exact (hp.append_right _).trans List.perm_append_comm
        · have hflat := flatten_other_subtree f hf c l (by simpa [hs] using hrl)
          have hnode : mergeScore f (.node c l) ≤ mergeScore f (.node l r) := by
            simp only [mergeScore, hs, Finset.union_comm (support r) (support l)]
            omega
          exact hflat.trans hnode

/-- A named whole structural claim. Permutation retains every block. -/
def CaterpillarLemmaClaim : Prop :=
  ∀ (A : Type) [DecidableEq A] (f : Finset A → ℕ),
    (∀ J K, J ⊆ K → f K ≤ f J) →
    ∀ t : BTree A, ∃ c : BTree A,
      (leaves c).Perm (leaves t) ∧ IsCaterpillar c ∧
      mergeScore f c ≤ mergeScore f t

theorem caterpillarLemmaClaim : CaterpillarLemmaClaim := by
  intro A inst f hf t
  exact caterpillar_exchange f hf t

structure MSSCInstance (N m : ℕ) where
  sets : Fin m → Finset (Fin N)
  covers : ∀ x : Fin N, ∃ i : Fin m, x ∈ sets i

def firstCover {N m : ℕ} (D : MSSCInstance N m)
    («order» : List (Fin m)) (x : Fin N) : ℕ :=
  (order.takeWhile (fun i => decide (x ∉ D.sets i))).length + 1

def msscCost {N m : ℕ} (D : MSSCInstance N m)
    («order» : List (Fin m)) : ℕ :=
  ∑ x : Fin N, firstCover D «order» x

def MSSCDecision {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) : Prop :=
  ∃ «order» : List (Fin m),
    order.Perm (Finset.univ : Finset (Fin m)).toList ∧ msscCost D «order» ≤ K

def privateCount (N m : ℕ) : ℕ := m * N + 1
abbrev Terminal (N m : ℕ) := Sum (Fin N) (Sum (Fin (privateCount N m)) (Fin 2))
abbrev Block (m : ℕ) := Option (Fin m)
abbrev Cell (N m : ℕ) := Block m × Terminal N m

def marker0 (N m : ℕ) : Terminal N m := Sum.inr (Sum.inr 0)

def markers (N m : ℕ) : Finset (Terminal N m) :=
  (Finset.univ : Finset (Fin 2)).image (fun x => Sum.inr (Sum.inr x))

def blockTypes {N m : ℕ} (D : MSSCInstance N m) :
    Block m → Finset (Terminal N m)
  | none =>
      (Finset.univ : Finset (Fin (privateCount N m))).image
        (fun z => Sum.inr (Sum.inl z)) ∪ markers N m
  | some i => (D.sets i).image Sum.inl ∪ markers N m

def combFrom {A : Type u} (start : A) (rest : List A) : BTree A :=
  rest.foldl (fun t a => BTree.node t (BTree.leaf a)) (BTree.leaf start)

def blockCells {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    List (Cell N m) :=
  ((blockTypes D b).toList).map (fun s => (b,s))

def fixedBlockTree {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    BTree (Cell N m) :=
  let xs := blockCells D b
  combFrom (xs.headD (b, marker0 N m)) xs.tail

def fullScore {N m : ℕ} (D : MSSCInstance N m) (t : BTree (Block m)) : ℕ :=
  starScore Finset.univ Prod.snd (graft (fixedBlockTree D) t)

def fixedCost {N m : ℕ} (D : MSSCInstance N m) : ℕ :=
  ∑ b : Block m, starScore Finset.univ Prod.snd (fixedBlockTree D b)

def ValidJoiningTree {m : ℕ} (t : BTree (Block m)) : Prop :=
  (leaves t).Perm (Finset.univ : Finset (Block m)).toList

/-- Quantifies over every binary joining topology, not a chosen caterpillar
    or a disjoint-triple subproblem. Grafting retains all original blocks. -/
def RefinementDecision {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) : Prop :=
  ∃ t : BTree (Block m), ValidJoiningTree t ∧
    fullScore D t ≤ fixedCost D + K - N

/-- The complete finite mathematical reduction target. A proposed, unelaborated
    proof term appears below. Encoding bounds and classical hardness are separate. -/
def FullReductionClaim : Prop :=
  ∀ (N m : ℕ) (D : MSSCInstance N m) (K : ℕ),
    0 < N → 2 ≤ m → N ≤ K → K ≤ m * N →
    (MSSCDecision D K ↔ RefinementDecision D K)

/- The next terms connect the concrete anchor gadget to the actual first-cover
   objective. They are not a different label-count or clade-packing problem. -/

def chainCost {I : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (B : I → Finset S) (covered : Finset S) : List I → ℕ
  | [] => 0
  | i :: rest => (univ \ (covered ∪ B i)).card +
      chainCost univ B (covered ∪ B i) rest

theorem joiningScore_attach {I : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (B : I → Finset S) (t : BTree I) (xs : List I) :
    joiningScore univ B (attach t xs) = joiningScore univ B t +
      chainCost univ B (joinedObserved B t) xs := by
  induction xs generalizing t with
  | nil => simp [attach, chainCost]
  | cons i xs ih =>
      simp only [attach, chainCost, ih, joiningScore, joinedObserved]
      omega

def coveredTypes {N m : ℕ} (D : MSSCInstance N m)
    (covered : Finset (Fin N)) : Finset (Terminal N m) :=
  covered.image Sum.inl ∪ blockTypes D none

theorem coveredTypes_union {N m : ℕ} (D : MSSCInstance N m)
    (covered : Finset (Fin N)) (i : Fin m) :
    coveredTypes D covered ∪ blockTypes D (some i) =
      coveredTypes D (covered ∪ D.sets i) := by
  ext s
  cases s with
  | inl x => simp [coveredTypes, blockTypes, markers, or_assoc]
  | inr z =>
      cases z with
      | inl z => simp [coveredTypes, blockTypes, markers]
      | inr a => simp [coveredTypes, blockTypes, markers]

theorem coveredTypes_complement {N m : ℕ} (D : MSSCInstance N m)
    (covered : Finset (Fin N)) :
    (Finset.univ \ coveredTypes D covered) =
      (Finset.univ \ covered).image (Sum.inl : Fin N → Terminal N m) := by
  ext s
  cases s with
  | inl x => simp [coveredTypes, blockTypes, markers]
  | inr z =>
      cases z with
      | inl z => simp [coveredTypes, blockTypes, markers]
      | inr a => simp [coveredTypes, blockTypes, markers]

theorem coveredTypes_missing_card {N m : ℕ} (D : MSSCInstance N m)
    (covered : Finset (Fin N)) :
    (Finset.univ \ coveredTypes D covered).card =
      (Finset.univ \ covered).card := by
  rw [coveredTypes_complement]
  exact Finset.card_image_of_injective _ Sum.inl_injective

def originalContinuation {N m : ℕ} (D : MSSCInstance N m)
    (covered : Finset (Fin N)) : List (Fin m) → ℕ
  | [] => 0
  | i :: rest => (Finset.univ \ (covered ∪ D.sets i)).card +
      originalContinuation D (covered ∪ D.sets i) rest

theorem chainCost_anchor_map {N m : ℕ} (D : MSSCInstance N m)
    (covered : Finset (Fin N)) («order» : List (Fin m)) :
    chainCost Finset.univ (blockTypes D) (coveredTypes D covered)
      (order.map some) = originalContinuation D covered «order» := by
  induction «order» generalizing covered with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.map_cons, chainCost, originalContinuation,
        coveredTypes_union, coveredTypes_missing_card, ih]

theorem complement_card_as_sum {N : ℕ} (covered : Finset (Fin N)) :
    (Finset.univ \ covered).card =
      ∑ x : Fin N, if x ∈ covered then 0 else 1 := by
  have h : Finset.univ \ covered =
      (Finset.univ : Finset (Fin N)).filter (fun x => x ∉ covered) := by
    ext x
    simp
  rw [h, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hc : x ∈ covered <;> simp [hc]

/-- Each type is charged once per successive prefix that still misses it.
    This identity is valid even before assuming an ordering covers U. -/
theorem originalContinuation_firstCover {N m : ℕ} (D : MSSCInstance N m)
    (covered : Finset (Fin N)) («order» : List (Fin m)) :
    originalContinuation D covered «order» = ∑ x : Fin N,
      if x ∈ covered then 0 else
        (order.takeWhile (fun i => decide (x ∉ D.sets i))).length := by
  induction «order» generalizing covered with
  | nil => simp [originalContinuation]
  | cons i rest ih =>
      rw [originalContinuation, ih, complement_card_as_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hc : x ∈ covered <;> by_cases hi : x ∈ D.sets i <;>
        simp [hc, hi, List.takeWhile, Nat.add_comm]

def anchorTree {m : ℕ} («order» : List (Fin m)) : BTree (Block m) :=
  attach (.leaf none) (order.map some)

/-- Exact MSSC shift for the concrete joining score, not a surrogate score. -/
theorem anchored_joining_score {N m : ℕ} (D : MSSCInstance N m)
    («order» : List (Fin m)) :
    joiningScore Finset.univ (blockTypes D) (anchorTree «order») + N =
      msscCost D «order» := by
  have h := chainCost_anchor_map D (∅ : Finset (Fin N)) «order»
  simp only [coveredTypes, Finset.image_empty, Finset.empty_union] at h
  simp only [anchorTree, joiningScore_attach, joiningScore,
    joinedObserved, zero_add]
  rw [h, originalContinuation_firstCover]
  simp [msscCost, firstCover, Finset.sum_add_distrib]

/-- The additive identity gives the exact natural-number threshold without
    replacing subtraction by an unjustified integer calculation. -/
theorem anchored_joining_threshold {N m : ℕ} (D : MSSCInstance N m)
    («order» : List (Fin m)) (C0 K : ℕ) (hNK : N ≤ K) :
    C0 + joiningScore Finset.univ (blockTypes D) (anchorTree «order») ≤ C0 + K - N
      ↔ msscCost D «order» ≤ K := by
  have h := anchored_joining_score D «order»
  omega

theorem foldl_node_eq_attach {A : Type u} (t : BTree A) (xs : List A) :
    xs.foldl (fun q a => BTree.node q (.leaf a)) t = attach t xs := by
  induction xs generalizing t with
  | nil => rfl
  | cons a xs ih => simp only [List.foldl_cons, attach, ih]

theorem marker0_mem_blockTypes {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : marker0 N m ∈ blockTypes D b := by
  cases b <;> simp [marker0, blockTypes, markers]

theorem leaves_fixedBlockTree {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : leaves (fixedBlockTree D b) = blockCells D b := by
  have hm : (b, marker0 N m) ∈ blockCells D b := by
    simp [blockCells, marker0_mem_blockTypes]
  cases hx : blockCells D b with
  | nil => simp [hx] at hm
  | cons a rest =>
      simp [fixedBlockTree, hx, combFrom, foldl_node_eq_attach,
        leaves_attach, leaves]

theorem observed_eq_leaves_image {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) (t : BTree A) :
    observed tip t = ((leaves t).map tip).toFinset := by
  induction t with
  | leaf a => simp [observed, leaves]
  | node l r ihl ihr =>
      ext s
      simp [observed, leaves, ihl, ihr]

theorem observed_fixedBlockTree {N m : ℕ} (D : MSSCInstance N m)
    (b : Block m) : observed Prod.snd (fixedBlockTree D b) = blockTypes D b := by
  rw [observed_eq_leaves_image, leaves_fixedBlockTree]
  ext s
  simp [blockCells, List.map_map]

theorem blockScoreSum_as_list {I : Type u} (cost : I → ℕ) (t : BTree I) :
    blockScoreSum cost t = ((leaves t).map cost).sum := by
  induction t with
  | leaf i => simp [blockScoreSum, leaves]
  | node l r ihl ihr => simp [blockScoreSum, leaves, ihl, ihr]

theorem fullScore_decomposition {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) (ht : ValidJoiningTree t) :
    fullScore D t = fixedCost D + joiningScore Finset.univ (blockTypes D) t := by
  have hsum := (ht.map (fun b => starScore Finset.univ Prod.snd
    (fixedBlockTree D b))).sum_eq
  rw [Finset.sum_map_toList] at hsum
  simp only [fullScore, star_graft_score, observed_fixedBlockTree,
    blockScoreSum_as_list]
  rw [hsum]
  rfl

theorem anchorTree_valid {m : ℕ} («order» : List (Fin m))
    (ho : order.Perm (Finset.univ : Finset (Fin m)).toList) :
    ValidJoiningTree (anchorTree «order») := by
  have hn : order.Nodup := ho.nodup_iff.mpr Finset.univ.nodup_toList
  have hmap : (order.map (some : Fin m → Block m)).Nodup :=
    List.Nodup.map (Option.some_injective _) hn
  have hn' : (none :: order.map (some : Fin m → Block m)).Nodup := by
    simp [hmap]
  change (leaves (attach (.leaf none) (order.map some))).Perm _
  rw [leaves_attach]
  change (none :: order.map some).Perm _
  apply List.perm_of_nodup_nodup_toFinset_eq hn' Finset.univ.nodup_toList
  ext b
  cases b with
  | none => simp
  | some i =>
      have hi : i ∈ «order» := ho.mem_iff.mpr (by simp)
      simp [hi]

/-- One whole direction of the original decision reduction, with concrete
    block trees, all internal sampling terms, and the exact C0+K-N threshold. -/
theorem msscDecision_implies_refinementDecision {N m : ℕ}
    (D : MSSCInstance N m) (K : ℕ) (hNK : N ≤ K) :
    MSSCDecision D K → RefinementDecision D K := by
  rintro ⟨«order», ho, hcost⟩
  have hv := anchorTree_valid «order» ho
  refine ⟨anchorTree «order», hv, ?_⟩
  rw [fullScore_decomposition D _ hv]
  exact (anchored_joining_threshold D «order» (fixedCost D) K hNK).mpr hcost

def missingMergeCost {I : Type u} {S : Type v} [DecidableEq I] [DecidableEq S]
    (univ : Finset S) (B : I → Finset S) (J : Finset I) : ℕ :=
  (univ \ J.biUnion B).card

theorem joinedObserved_as_union {I : Type u} {S : Type v}
    [DecidableEq I] [DecidableEq S] (B : I → Finset S) (t : BTree I) :
    joinedObserved B t = (support t).biUnion B := by
  induction t with
  | leaf i => simp [joinedObserved, support, leaves]
  | node l r ihl ihr =>
      simp only [joinedObserved, support_node, Finset.union_biUnion, ihl, ihr]

theorem joiningScore_as_mergeScore {I : Type u} {S : Type v}
    [DecidableEq I] [DecidableEq S] (univ : Finset S) (B : I → Finset S)
    (t : BTree I) :
    joiningScore univ B t = mergeScore (missingMergeCost univ B) t := by
  induction t with
  | leaf i => rfl
  | node l r ihl ihr =>
      simp only [joiningScore, mergeScore, ihl, ihr, missingMergeCost,
        Finset.union_biUnion, joinedObserved_as_union]

theorem missingMergeCost_antitone {I : Type u} {S : Type v}
    [DecidableEq I] [DecidableEq S] (univ : Finset S) (B : I → Finset S)
    (J K : Finset I) (hJK : J ⊆ K) :
    missingMergeCost univ B K ≤ missingMergeCost univ B J := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hu, hnot⟩ := Finset.mem_sdiff.mp hx
  refine Finset.mem_sdiff.mpr ⟨hu, ?_⟩
  intro hj
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hj
  exact hnot (Finset.mem_biUnion.mpr ⟨i, hJK hi, hxi⟩)

theorem joining_caterpillar_exchange {N m : ℕ} (D : MSSCInstance N m)
    (t : BTree (Block m)) (ht : ValidJoiningTree t) :
    ∃ c : BTree (Block m), ValidJoiningTree c ∧ IsCaterpillar c ∧
      joiningScore Finset.univ (blockTypes D) c ≤
        joiningScore Finset.univ (blockTypes D) t := by
  obtain ⟨c, hp, hc, hs⟩ := caterpillar_exchange
    (missingMergeCost Finset.univ (blockTypes D))
    (missingMergeCost_antitone Finset.univ (blockTypes D)) t
  exact ⟨c, hp.trans ht, hc, by simpa only [joiningScore_as_mergeScore] using hs⟩

theorem attach_append {A : Type u} (t : BTree A) (xs ys : List A) :
    attach t (xs ++ ys) = attach (attach t xs) ys := by
  induction xs generalizing t with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, attach, ih]

theorem caterpillar_representation {A : Type u} (t : BTree A)
    (ht : IsCaterpillar t) :
    ∃ a : A, ∃ xs : List A, t = attach (.leaf a) xs := by
  induction ht with
  | leaf a => exact ⟨a, [], rfl⟩
  | @extend t h a ih =>
      obtain ⟨b, xs, rfl⟩ := ih
      refine ⟨b, xs ++ [a], ?_⟩
      rw [attach_append]
      rfl

theorem joiningScore_le_attach {I : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (B : I → Finset S) (t : BTree I) (xs : List I) :
    joiningScore univ B t ≤ joiningScore univ B (attach t xs) := by
  rw [joiningScore_attach]
  omega

/-- If the first two blocks are real sets, every private type is absent at
    their first merge. Nonnegative later terms cannot erase this H penalty. -/
theorem set_pair_private_penalty {N m : ℕ} (D : MSSCInstance N m)
    (i j : Fin m) :
    privateCount N m ≤
      (Finset.univ \ (blockTypes D (some i) ∪ blockTypes D (some j))).card := by
  let Z : Finset (Terminal N m) :=
    (Finset.univ : Finset (Fin (privateCount N m))).image
      (fun z => Sum.inr (Sum.inl z))
  have hZ : Z.card = privateCount N m := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b h
      exact Sum.inl_injective (Sum.inr_injective h)
  have hsub : Z ⊆
      Finset.univ \ (blockTypes D (some i) ∪ blockTypes D (some j)) := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    simp [blockTypes, markers]
  have hcard := Finset.card_le_card hsub
  omega

theorem first_two_set_penalty {N m : ℕ} (D : MSSCInstance N m)
    (i j : Fin m) (rest : List (Block m)) :
    privateCount N m ≤ joiningScore Finset.univ (blockTypes D)
      (attach (.leaf (some i)) (some j :: rest)) := by
  have h := joiningScore_le_attach Finset.univ (blockTypes D)
    (.node (.leaf (some i)) (.leaf (some j))) rest
  have hp := set_pair_private_penalty D i j
  simp only [joiningScore, joinedObserved, zero_add] at h
  change privateCount N m ≤ joiningScore Finset.univ (blockTypes D)
    (attach (.node (.leaf (some i)) (.leaf (some j))) rest)
  omega

theorem swap_first_two_score {I : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (B : I → Finset S) (a b : I) (rest : List I) :
    joiningScore univ B (attach (.leaf a) (b :: rest)) =
      joiningScore univ B (attach (.leaf b) (a :: rest)) := by
  simp only [attach, joiningScore_attach, joiningScore, joinedObserved, zero_add]
  rw [Finset.union_comm (B a) (B b)]

theorem map_some_filterMap {A : Type u} (xs : List (Option A))
    (hn : none ∉ xs) : (xs.filterMap id).map some = xs := by
  revert hn
  induction xs with
  | nil => intro hn; rfl
  | cons a xs ih =>
      intro hn
      have hnxs : none ∉ xs := List.not_mem_of_not_mem_cons hn
      cases a with
      | none => simp at hn
      | some a => simp [ih hnxs]

theorem real_order_perm {m : ℕ} («order» : List (Fin m))
    (hp : (none :: order.map some).Perm
      (Finset.univ : Finset (Block m)).toList) :
    order.Perm (Finset.univ : Finset (Fin m)).toList := by
  have hn : (none :: order.map some).Nodup :=
    hp.nodup_iff.mpr Finset.univ.nodup_toList
  have hno : order.Nodup := (List.nodup_map_iff (Option.some_injective _)).mp
    (List.nodup_cons.mp hn).2
  apply List.perm_of_nodup_nodup_toFinset_eq hno Finset.univ.nodup_toList
  ext i
  have hi : some i ∈ none :: order.map some := hp.mem_iff.mpr (by simp)
  simpa using hi

theorem anchor_tail_order {m : ℕ} (rest : List (Block m))
    (hp : (none :: rest).Perm (Finset.univ : Finset (Block m)).toList) :
    ∃ «order» : List (Fin m),
      order.Perm (Finset.univ : Finset (Fin m)).toList ∧ rest = order.map some := by
  have hn : (none :: rest).Nodup := hp.nodup_iff.mpr Finset.univ.nodup_toList
  have hm := map_some_filterMap rest (List.nodup_cons.mp hn).1
  refine ⟨rest.filterMap id, ?_, hm.symm⟩
  apply real_order_perm
  rw [hm]
  exact hp

/-- Below H, a valid caterpillar must begin with the anchor in one of its
    first two positions. Swapping those positions changes no merge score. -/
theorem low_score_caterpillar_has_anchor_order {N m : ℕ}
    (D : MSSCInstance N m) (hm : 2 ≤ m) (c : BTree (Block m))
    (hv : ValidJoiningTree c) (hc : IsCaterpillar c)
    (hlow : joiningScore Finset.univ (blockTypes D) c < privateCount N m) :
    ∃ «order» : List (Fin m),
      order.Perm (Finset.univ : Finset (Fin m)).toList ∧
      joiningScore Finset.univ (blockTypes D) (anchorTree «order») =
        joiningScore Finset.univ (blockTypes D) c := by
  obtain ⟨a, xs, rfl⟩ := caterpillar_representation c hc
  cases xs with
  | nil =>
      have hlen := hv.length_eq
      simp [attach, leaves] at hlen
      omega
  | cons b rest =>
      have hp : (a :: b :: rest).Perm
          (Finset.univ : Finset (Block m)).toList := by
        simpa [leaves_attach, leaves] using hv
      cases a with
      | none =>
          obtain ⟨«order», ho, he⟩ := anchor_tail_order (b :: rest) hp
          refine ⟨«order», ho, ?_⟩
          change joiningScore Finset.univ (blockTypes D)
            (attach (.leaf none) (order.map some)) = _
          rw [← he]
      | some i =>
          cases b with
          | none =>
              have hs : (none :: some i :: rest).Perm
                  (some i :: none :: rest) := List.Perm.swap _ _ _
              obtain ⟨«order», ho, he⟩ := anchor_tail_order (some i :: rest)
                (hs.trans hp)
              refine ⟨«order», ho, ?_⟩
              change joiningScore Finset.univ (blockTypes D)
                (attach (.leaf none) (order.map some)) = _
              rw [← he]
              exact swap_first_two_score Finset.univ (blockTypes D) none (some i) rest
          | some j =>
              have hpen := first_two_set_penalty D i j rest
              omega

/-- Reverse implication ranges over every binary refinement witness. The
    structural exchange and H penalty are used, not assumed away. -/
theorem refinementDecision_implies_msscDecision {N m : ℕ}
    (D : MSSCInstance N m) (K : ℕ) (hm : 2 ≤ m) (hNK : N ≤ K)
    (hKmN : K ≤ m * N) :
    RefinementDecision D K → MSSCDecision D K := by
  rintro ⟨t, ht, hcost⟩
  rw [fullScore_decomposition D t ht] at hcost
  obtain ⟨c, hv, hc, hct⟩ := joining_caterpillar_exchange D t ht
  have hlow : joiningScore Finset.univ (blockTypes D) c < privateCount N m := by
    simp only [privateCount]
    omega
  obtain ⟨«order», ho, hscore⟩ :=
    low_score_caterpillar_has_anchor_order D hm c hv hc hlow
  refine ⟨«order», ho, ?_⟩
  have hs := anchored_joining_score D «order»
  rw [hscore] at hs
  omega

/-- Proposed proof term for the FULL finite mathematical reduction target.
    UNELABORATED: this is not a compilation certificate, nor by itself a
    polynomial-encoding / NP-completeness formalization. -/
theorem fullReductionClaim : FullReductionClaim := by
  intro N m D K hN hm hNK hKmN
  exact ⟨msscDecision_implies_refinementDecision D K hNK,
    refinementDecision_implies_msscDecision D K hm hNK hKmN⟩

theorem firstCover_le_length_of_witness {N m : ℕ} (D : MSSCInstance N m)
    («order» : List (Fin m)) (x : Fin N)
    (hx : ∃ i ∈ «order», x ∈ D.sets i) : firstCover D «order» x ≤ order.length := by
  revert hx
  induction «order» with
  | nil => intro hx; simp at hx
  | cons a rest ih =>
      intro hx
      by_cases ha : x ∈ D.sets a
      · simp [firstCover, List.takeWhile, ha]
      · have hr : ∃ i ∈ rest, x ∈ D.sets i := by
          obtain ⟨i, hi, hxi⟩ := hx
          rcases List.mem_cons.mp hi with hia | hir
          · subst i
            exact (ha hxi).elim
          · exact ⟨i, hir, hxi⟩
        have h := ih hr
        simp [firstCover, List.takeWhile, ha] at h ⊢
        omega

theorem msscCost_bounds {N m : ℕ} (D : MSSCInstance N m)
    («order» : List (Fin m))
    (ho : order.Perm (Finset.univ : Finset (Fin m)).toList) :
    N ≤ msscCost D «order» ∧ msscCost D «order» ≤ m * N := by
  have hlen : order.length = m := by simpa using ho.length_eq
  have hl : ∀ x : Fin N, 1 ≤ firstCover D «order» x := by
    intro x
    simp [firstCover]
  have hu : ∀ x : Fin N, firstCover D «order» x ≤ m := by
    intro x
    obtain ⟨i, hi⟩ := D.covers x
    have him : i ∈ «order» := ho.mem_iff.mpr (by simp)
    simpa [hlen] using firstCover_le_length_of_witness D «order» x ⟨i, him, hi⟩
  constructor
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun x hx => hl x)
    simpa [msscCost] using h
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun x hx => hu x)
    simpa [msscCost, Nat.mul_comm] using h

/-- Exact optimizer correspondence, stated without invoking an optimum oracle.
    Given an actual minimizing MSSC order, its anchored tree minimizes over
    ALL valid binary refinements and realizes the precise additive cost shift. -/
theorem exact_anchor_optimum {N m : ℕ} (D : MSSCInstance N m) (hm : 2 ≤ m)
    («order» : List (Fin m))
    (ho : order.Perm (Finset.univ : Finset (Fin m)).toList)
    (hmin : ∀ p : List (Fin m),
      p.Perm (Finset.univ : Finset (Fin m)).toList →
        msscCost D «order» ≤ msscCost D p) :
    ValidJoiningTree (anchorTree «order») ∧
      fullScore D (anchorTree «order») + N = fixedCost D + msscCost D «order» ∧
      ∀ t : BTree (Block m), ValidJoiningTree t →
        fullScore D (anchorTree «order») ≤ fullScore D t := by
  have hv := anchorTree_valid «order» ho
  have hs := anchored_joining_score D «order»
  have hb := (msscCost_bounds D «order» ho).2
  refine ⟨hv, ?_, ?_⟩
  · rw [fullScore_decomposition D _ hv]
    omega
  · intro t ht
    rw [fullScore_decomposition D _ hv, fullScore_decomposition D _ ht]
    by_cases hlow : joiningScore Finset.univ (blockTypes D) t < privateCount N m
    · obtain ⟨c, hcv, hcc, hct⟩ := joining_caterpillar_exchange D t ht
      obtain ⟨p, hp, hpc⟩ := low_score_caterpillar_has_anchor_order D hm c hcv hcc
        (lt_of_le_of_lt hct hlow)
      have hps := anchored_joining_score D p
      have hmp := hmin p hp
      rw [hpc] at hps
      omega
    · simp only [privateCount] at hlow
      omega

theorem exists_mssc_minimizer {N m : ℕ} (D : MSSCInstance N m) :
    ∃ «order» : List (Fin m),
      order.Perm (Finset.univ : Finset (Fin m)).toList ∧
      ∀ p : List (Fin m), p.Perm (Finset.univ : Finset (Fin m)).toList →
        msscCost D «order» ≤ msscCost D p := by
  classical
  let P : ℕ → Prop := fun n => ∃ «order» : List (Fin m),
    order.Perm (Finset.univ : Finset (Fin m)).toList ∧ msscCost D «order» = n
  have hex : ∃ n, P n := ⟨_, Finset.univ.toList, List.Perm.refl _, rfl⟩
  obtain ⟨«order», ho, hs⟩ := Nat.find_spec hex
  refine ⟨«order», ho, ?_⟩
  intro p hp
  rw [hs]
  exact Nat.find_min' hex ⟨p, hp, rfl⟩

/-- An existential exact optimum identity, with minimizer existence proved
    rather than supplied as an oracle or an extra hypothesis. -/
theorem exists_exact_optimum_pair {N m : ℕ} (D : MSSCInstance N m) (hm : 2 ≤ m) :
    ∃ «order» : List (Fin m), ∃ t : BTree (Block m),
      order.Perm (Finset.univ : Finset (Fin m)).toList ∧ ValidJoiningTree t ∧
      (∀ p : List (Fin m), p.Perm (Finset.univ : Finset (Fin m)).toList →
        msscCost D «order» ≤ msscCost D p) ∧
      (∀ u : BTree (Block m), ValidJoiningTree u → fullScore D t ≤ fullScore D u) ∧
      fullScore D t + N = fixedCost D + msscCost D «order» := by
  obtain ⟨«order», ho, hmin⟩ := exists_mssc_minimizer D
  obtain ⟨hv, heq, htree⟩ := exact_anchor_optimum D hm «order» ho hmin
  exact ⟨«order», anchorTree «order», ho, hv, hmin, htree, heq⟩

/- Remaining proof obligations, not supplied as assumptions:
1. Elaborate/check the concrete block-cell and score proofs, together with the
   distinct-cell and mixed-descendant terms in PolytomyStarSemantics.lean.
2. ValidJoiningTree grafts are exactly binary refinements of the one-polytomy
   input with these fixed blocks. The companion proposes forced-label proofs;
   the external edge-contraction/clade-preservation adapter is still missing.
3. Elaborate/check the proposed full q-1-node caterpillar exchange proof above.
4. Elaborate/check the anchored first-cover identity, private-type first-pair
   penalty and anchor-order extraction. No arbitrary first-position sum is needed.
5. Elaborate/check both decision directions and exact_anchor_optimum.
6. Check the companion's explicit D_lambda adapter. Define encoded instances
   and connect the external original refinement representation.
7. Give polynomial encoding/size bounds and an NP certificate checker.
8. Formalize the separate general-DAG full-score subset recurrence and its
   correctness/complexity, rather than treating it as this star special case.
-/

end

end PolytomyReductionModel
