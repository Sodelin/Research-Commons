import RootBlobSwitching

/-!
# Rooted-tree marginal elimination, source-only development

Author: dot (OpenAI), 22 October 2026.
UNELABORATED proof terms; no runtime or formal verification.
Pinned source API: mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

This module develops the actual weighted state-sum elimination needed for
ResolvedPathFormula. It does not replace that obligation by an axiom.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobOpenProof RootBlobDAGNormalization
namespace RootBlobTreeMarginals
universe u v w
variable {S : Type u} [Fintype S]
variable {V : Type v} [Fintype V] [DecidableEq V]

/-- Eliminate one leaf coordinate with an arbitrary observable, retaining
its conditional expectation. This is the state-sum step for joint marginals,
not merely normalization of a scalar partition function. -/
theorem weighted_leaf_elimination (v : V) (k : S)
    (f : V → (V → S) → ℝ) (obs : (V → S) → ℝ)
    (hignore : ∀ u : {u : V // u ≠ v}, ∀ a s,
      f u.val (Function.update a v s) = f u.val a) :
    (∑ a : V → S, (∏ u, f u a) * obs a) =
      ∑ b : {u : V // u ≠ v} → S,
        (∏ u : {u : V // u ≠ v}, f u.val (extendAt v k b)) *
        (∑ s : S, f v (extendAt v s b) * obs (extendAt v s b)) := by
  classical
  calc
    (∑ a : V → S, (∏ u, f u a) * obs a) =
        ∑ p : S × ({u : V // u ≠ v} → S),
          (∏ u, f u ((splitAt v).symm p)) * obs ((splitAt v).symm p) := by
      apply Fintype.sum_equiv (splitAt v)
      intro a
      rw [Equiv.symm_apply_apply]
    _ = ∑ b : {u : V // u ≠ v} → S, ∑ s : S,
        (∏ u, f u (extendAt v s b)) * obs (extendAt v s b) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      have hrest : ∀ s, (∏ u : {u : V // u ≠ v}, f u.val (extendAt v s b)) =
          ∏ u : {u : V // u ≠ v}, f u.val (extendAt v k b) := by
        intro s
        apply Finset.prod_congr rfl
        intro u _
        rw [extendAt_update_outer v k s b]
        exact hignore u (extendAt v k b) s
      simp_rw [prod_split v, hrest]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- Unique original root and one selected original parent for each nonroot
vertex. Strict rank is the well-foundedness witness, not a clock model. -/
structure ParentTree (V : Type v) where
  root : V
  rank : V → ℕ
  parent : {v : V // v ≠ root} → V
  parent_rank : ∀ v, rank (parent v) < rank v.val

namespace ParentTree
variable (T : ParentTree V)

abbrev NR := {v : V // v ≠ T.root}

def IsLeaf (v : V) : Prop := ∀ u : T.NR, T.parent u ≠ v

noncomputable def factor (π : S → ℝ) (K : T.NR → Mat S)
    (v : V) (a : V → S) : ℝ := by
  classical
  exact if h : v = T.root then π (a T.root)
    else K ⟨v, h⟩ (a (T.parent ⟨v, h⟩)) (a v)

noncomputable def mass (π : S → ℝ) (K : T.NR → Mat S) (a : V → S) : ℝ :=
  ∏ v, T.factor π K v a

noncomputable def joint (π : S → ℝ) (K : T.NR → Mat S)
    (u v : V) : Mat S := by
  classical
  exact fun i j => ∑ a : V → S, T.mass π K a *
    (if a u = i ∧ a v = j then 1 else 0)

theorem factor_ignores_leaf (π : S → ℝ) (K : T.NR → Mat S)
    (v : T.NR) (hv : T.IsLeaf v.val)
    (u : {u : V // u ≠ v.val}) (a : V → S) (s : S) :
    T.factor π K u.val (Function.update a v.val s) = T.factor π K u.val a := by
  classical
  unfold factor
  split_ifs with hu
  · simp only [Function.update_of_ne (Ne.symm v.property)]
  · simp only [Function.update_of_ne (hv ⟨u.val, hu⟩),
      Function.update_of_ne u.property]

/-- Every nonsingleton rooted parent tree has a nonroot leaf. The proof
selects a maximum-rank nonroot vertex, so no tree-library convention is used. -/
theorem exists_nonroot_leaf (h : ∃ v : V, v ≠ T.root) :
    ∃ v : T.NR, T.IsLeaf v.val := by
  classical
  have hn : (Finset.univ.filter (fun v : V => v ≠ T.root)).Nonempty := by
    rcases h with ⟨v, hv⟩
    exact ⟨v, by simp [hv]⟩
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun v : V => v ≠ T.root)) T.rank hn
  have hvr : v ≠ T.root := (Finset.mem_filter.mp hv).2
  refine ⟨⟨v, hvr⟩, ?_⟩
  intro u hu
  have hlt := T.parent_rank u
  have hle : T.rank u.val ≤ T.rank v := hmax u.val (by simp [u.property])
  rw [hu] at hlt
  exact (not_lt_of_ge hle) hlt

/-- Remove a nonroot leaf while retaining every other selected parent. -/
def prune (v : T.NR) (hv : T.IsLeaf v.val) :
    ParentTree {u : V // u ≠ v.val} where
  root := ⟨T.root, Ne.symm v.property⟩
  rank := fun u => T.rank u.val
  parent := fun u =>
    let hu : u.val.val ≠ T.root := fun he => u.property (Subtype.ext he)
    ⟨T.parent ⟨u.val.val, hu⟩, hv ⟨u.val.val, hu⟩⟩
  parent_rank := by
    intro u
    exact T.parent_rank
      ⟨u.val.val, fun he => u.property (Subtype.ext he)⟩

def oldNonroot (v : T.NR) (hv : T.IsLeaf v.val)
    (u : (T.prune v hv).NR) : T.NR :=
  ⟨u.val.val, fun he => u.property (Subtype.ext he)⟩

def prunedMatrices (v : T.NR) (hv : T.IsLeaf v.val)
    (K : T.NR → Mat S) : (T.prune v hv).NR → Mat S :=
  fun u => K (T.oldNonroot v hv u)

theorem factor_pruned (v : T.NR) (hv : T.IsLeaf v.val)
    (π : S → ℝ) (K : T.NR → Mat S)
    (s : S) (b : {u : V // u ≠ v.val} → S) (u : {u : V // u ≠ v.val}) :
    T.factor π K u.val (extendAt v.val s b) =
      (T.prune v hv).factor π (T.prunedMatrices v hv K) u b := by
  classical
  by_cases hu : u.val = T.root
  · have hsub : u = (T.prune v hv).root := Subtype.ext hu
    simp [factor, hu, hsub, extendAt, prune, Ne.symm v.property]
  · have hsub : u ≠ (T.prune v hv).root := by
      intro he
      exact hu (congrArg Subtype.val he)
    simp [factor, hu, hsub, extendAt, u.property,
      hv ⟨u.val, hu⟩, prune, prunedMatrices, oldNonroot]

theorem leaf_factor (v : T.NR) (hv : T.IsLeaf v.val)
    (π : S → ℝ) (K : T.NR → Mat S)
    (s : S) (b : {u : V // u ≠ v.val} → S) :
    T.factor π K v.val (extendAt v.val s b) =
      K v (b ⟨T.parent v, hv v⟩) s := by
  classical
  simp [factor, v.property, extendAt, hv v]

/-- Full weighted leaf marginalization on the actual parent-tree mass.
All retained factors are exactly those of the pruned original tree. -/
theorem eliminate_leaf (v : T.NR) (hv : T.IsLeaf v.val)
    (π : S → ℝ) (K : T.NR → Mat S) (k : S) (obs : (V → S) → ℝ) :
    (∑ a : V → S, T.mass π K a * obs a) =
      ∑ b : {u : V // u ≠ v.val} → S,
        (T.prune v hv).mass π (T.prunedMatrices v hv K) b *
        (∑ s, K v (b ⟨T.parent v, hv v⟩) s * obs (extendAt v.val s b)) := by
  unfold mass
  rw [weighted_leaf_elimination v.val k (T.factor π K) obs
    (T.factor_ignores_leaf π K v hv)]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  · apply Finset.prod_congr rfl
    intro u _
    exact T.factor_pruned v hv π K k b u
  · apply Finset.sum_congr rfl
    intro s _
    rw [T.leaf_factor v hv π K s b]

end ParentTree

/-- The selected functional parent tree is extracted directly from the
original switching. Its rank proof was already derived from original edges. -/
def selectedTree {E : Type w} [Fintype E]
    (N : RootBlobEdgeIndexed.Network V E (Fin 2))
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (σ : RootBlobSwitching.Switching N) : ParentTree V where
  root := N.root
  rank := N.rank
  parent := RootBlobSwitching.parent N σ
  parent_rank := RootBlobSwitching.parent_rank N hG σ


namespace ParentTree
variable (T : ParentTree V)

theorem joint_swap (π : S → ℝ) (K : T.NR → Mat S) (u v : V) (i j : S) :
    T.joint π K u v i j = T.joint π K v u j i := by
  classical
  unfold joint
  apply Finset.sum_congr rfl
  intro a _
  rw [and_comm]

end ParentTree

noncomputable def stationaryPair (μ : S → ℝ) (c : ℝ) : Mat S :=
  fun i j => μ j * equalInput μ c j i

theorem stationaryPair_swap (μ : S → ℝ) (c : ℝ) (i j : S) :
    stationaryPair μ c i j = stationaryPair μ c j i := by
  exact equalInput_reversible μ c j i

theorem stationaryPair_one (μ : S → ℝ) (i j : S) :
    stationaryPair μ 1 i j = if i = j then μ i else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [stationaryPair, equalInput]
  · simp [stationaryPair, equalInput, h, Ne.symm h]

theorem stationaryPair_step_left {μ : S → ℝ}
    (hμ : (∑ i, μ i) = 1) (c t : ℝ) (i j : S) :
    (∑ k, stationaryPair μ c k j * equalInput μ t k i) =
      stationaryPair μ (c * t) i j := by
  unfold stationaryPair
  calc
    (∑ k, (μ j * equalInput μ c j k) * equalInput μ t k i) =
        μ j * matMul (equalInput μ c) (equalInput μ t) j i := by
      unfold matMul
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = μ j * equalInput μ (c * t) j i := by
      rw [equalInput_semigroup hμ]

theorem stationaryPair_step_right {μ : S → ℝ}
    (hμ : (∑ i, μ i) = 1) (c t : ℝ) (i j : S) :
    (∑ k, stationaryPair μ c i k * equalInput μ t k j) =
      stationaryPair μ (c * t) i j := by
  simp_rw [stationaryPair_swap μ c i]
  rw [stationaryPair_step_left hμ]
  exact stationaryPair_swap μ (c * t) j i

/-- The terminal arbitrary A is composed on its actual side. -/
theorem stationaryPair_terminal (μ : S → ℝ) (c : ℝ)
    (A : Mat S) (i j : S) :
    (∑ k, stationaryPair μ c k j * A k i) = blendPair μ c A i j := by
  unfold stationaryPair blendPair
  calc
    (∑ k, (μ j * equalInput μ c j k) * A k i) =
        μ j * matMul (equalInput μ c) A j i := by
      unfold matMul
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [equalInput_mul]

/-- Finite binning identity used in leaf-to-parent marginal contraction. -/
theorem binning_contract (m : (V → S) → ℝ) (p q : V)
    (K : Mat S) (i j : S) :
    (∑ k, (∑ b : V → S, m b *
      (if b p = k ∧ b q = j then 1 else 0)) * K k i) =
    ∑ b : V → S, m b * K (b p) i * (if b q = j then 1 else 0) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hq : b q = j
  · simp only [hq, and_true, if_true]
    have ht : ∀ k, m b * (if b p = k then 1 else 0) * K k i =
        if b p = k then m b * K k i else 0 := by
      intro k
      split_ifs <;> ring
    simp_rw [ht]
    simp
  · simp [hq]


theorem diagonal_binning (m : (V → S) → ℝ) (p : V) (K : Mat S) (i : S) :
    (∑ k, (∑ b : V → S, m b * (if b p = k ∧ b p = k then 1 else 0)) * K k i) =
      ∑ b : V → S, m b * K (b p) i := by
  classical
  simp_rw [and_self, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have ht : ∀ k, m b * (if b p = k then 1 else 0) * K k i =
      if b p = k then m b * K k i else 0 := by
    intro k
    split_ifs <;> ring
  simp_rw [ht]
  simp

theorem equalInput_row_sum {μ : S → ℝ} (hμ : (∑ i, μ i) = 1)
    (t : ℝ) (i : S) : (∑ j, equalInput μ t i j) = 1 := by
  classical
  unfold equalInput
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hμ]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

namespace ParentTree
variable (T : ParentTree V)

theorem joint_keep_leaf [Nonempty S]
    (v : T.NR) (hv : T.IsLeaf v.val)
    (π : S → ℝ) (K : T.NR → Mat S)
    (hK : ∀ i, (∑ j, K v i j) = 1)
    (u w : {u : V // u ≠ v.val}) :
    T.joint π K u.val w.val =
      (T.prune v hv).joint π (T.prunedMatrices v hv K) u w := by
  classical
  funext i j
  unfold joint
  rw [T.eliminate_leaf v hv π K (Classical.choice inferInstance)]
  apply Finset.sum_congr rfl
  intro b _
  have ho : ∀ s,
      (if extendAt v.val s b u.val = i ∧ extendAt v.val s b w.val = j
       then (1 : ℝ) else 0) = if b u = i ∧ b w = j then 1 else 0 := by
    intro s
    simp [extendAt, u.property, w.property]
  simp_rw [ho]
  rw [← Finset.sum_mul, hK, one_mul]

theorem joint_leaf_other [Nonempty S]
    (v : T.NR) (hv : T.IsLeaf v.val)
    (π : S → ℝ) (K : T.NR → Mat S)
    (u : {u : V // u ≠ v.val}) :
    T.joint π K v.val u.val =
      fun i j => ∑ k,
        (T.prune v hv).joint π (T.prunedMatrices v hv K)
          ⟨T.parent v, hv v⟩ u k j * K v k i := by
  classical
  funext i j
  unfold joint
  rw [T.eliminate_leaf v hv π K (Classical.choice inferInstance)]
  rw [binning_contract]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hq : b u = j
  · simp [extendAt, u.property, hq, mul_ite]
  · simp [extendAt, u.property, hq]

theorem joint_leaf_self [Nonempty S]
    (v : T.NR) (hv : T.IsLeaf v.val)
    (π : S → ℝ) (K : T.NR → Mat S) (i j : S) :
    T.joint π K v.val v.val i j =
      if i = j then
        ∑ k, (T.prune v hv).joint π (T.prunedMatrices v hv K)
          ⟨T.parent v, hv v⟩ ⟨T.parent v, hv v⟩ k k * K v k i
      else 0 := by
  classical
  unfold joint
  rw [T.eliminate_leaf v hv π K (Classical.choice inferInstance)]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, diagonal_binning]
    apply Finset.sum_congr rfl
    intro b _
    simp [extendAt, mul_ite]
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro b _
    have ho : ∀ s,
        (if extendAt v.val s b v.val = i ∧ extendAt v.val s b v.val = j
         then (1 : ℝ) else 0) = 0 := by
      intro s
      have hn : ¬(s = i ∧ s = j) := by
        rintro ⟨hi, hj⟩
        exact hij (hi.symm.trans hj)
      simp [extendAt, hn]
    simp_rw [ho]
    simp

theorem joint_leaf_self_stationary [Nonempty S]
    (v : T.NR) (hv : T.IsLeaf v.val)
    (μ : S → ℝ) (hμ : (∑ i, μ i) = 1) (t : ℝ)
    (hparent : ∀ k,
      (T.prune v hv).joint μ (fun _ => equalInput μ t)
        ⟨T.parent v, hv v⟩ ⟨T.parent v, hv v⟩ k k = μ k) :
    T.joint μ (fun _ => equalInput μ t) v.val v.val =
      stationaryPair μ 1 := by
  classical
  funext i j
  rw [T.joint_leaf_self v hv μ (fun _ => equalInput μ t)]
  change (if i = j then
    ∑ k, (T.prune v hv).joint μ (fun _ => equalInput μ t)
      ⟨T.parent v, hv v⟩ ⟨T.parent v, hv v⟩ k k * equalInput μ t k i
    else 0) = _
  simp_rw [hparent]
  have hrow : (∑ k, μ k * equalInput μ t k i) = μ i :=
    congrFun (rowAction_equalInput hμ t) i
  rw [hrow, stationaryPair_one]

end ParentTree


namespace ParentTree
variable (T : ParentTree V)

def singletonEval (h : ∀ v, v = T.root) : (V → S) ≃ S where
  toFun := fun a => a T.root
  invFun := fun s _ => s
  left_inv := by
    intro a
    funext v
    rw [h v]
  right_inv := by intro s; rfl

theorem joint_singleton (h : ∀ v, v = T.root)
    (μ : S → ℝ) (K : T.NR → Mat S) (u v : V) :
    T.joint μ K u v = stationaryPair μ 1 := by
  classical
  letI : IsEmpty T.NR := ⟨fun q => q.property (h q.val)⟩
  have hm : ∀ a : V → S, T.mass μ K a = μ (a T.root) := by
    intro a
    unfold mass
    rw [prod_split T.root]
    simp [factor]
  funext i j
  unfold joint
  simp_rw [hm, h u, h v]
  calc
    (∑ a : V → S, μ (a T.root) *
        (if a T.root = i ∧ a T.root = j then 1 else 0)) =
      ∑ s : S, μ s * (if s = i ∧ s = j then 1 else 0) := by
        apply Fintype.sum_equiv (T.singletonEval h)
        intro a
        rfl
    _ = stationaryPair μ 1 i j := by
      rw [stationaryPair_one]
      by_cases hij : i = j
      · subst j
        simp [mul_ite]
      · have hn : ∀ s : S, ¬(s = i ∧ s = j) := by
          intro s
          rintro ⟨hi, hj⟩
          exact hij (hi.symm.trans hj)
        simp [hij, hn]

theorem joint_leaf_other_stationary [Nonempty S]
    (v : T.NR) (hv : T.IsLeaf v.val)
    (u : {u : V // u ≠ v.val})
    (μ : S → ℝ) (hμ : (∑ i, μ i) = 1) (t c : ℝ)
    (hp : (T.prune v hv).joint μ (fun _ => equalInput μ t)
      ⟨T.parent v, hv v⟩ u = stationaryPair μ c) :
    T.joint μ (fun _ => equalInput μ t) v.val u.val =
      stationaryPair μ (c * t) := by
  classical
  rw [T.joint_leaf_other v hv μ (fun _ => equalInput μ t) u]
  funext i j
  change (∑ k, (T.prune v hv).joint μ (fun _ => equalInput μ t)
    ⟨T.parent v, hv v⟩ u k j * equalInput μ t k i) = _
  rw [hp]
  exact stationaryPair_step_left hμ c t i j

/-- A finite, target-independent combinatorial distance with the proved
equal-input joint law. This record is constructed below, not assumed. -/
structure DistanceCertificate where
  distance : V → V → ℕ
  zero_iff : ∀ u v, distance u v = 0 ↔ u = v
  formula : ∀ (μ : S → ℝ), (∑ i, μ i) = 1 → ∀ (t : ℝ) (u v : V),
    T.joint μ (fun _ => equalInput μ t) u v =
      stationaryPair μ (t ^ distance u v)

/-- Reverse leaf induction computes a graph-only distance and proves the
actual two-output state sum. No LCA/path identity is postulated. The
auxiliary identity is polynomial, so its proof needs only sum μ = 1. -/
theorem distanceCertificate_nonempty [Nonempty S] :
    Nonempty (T.DistanceCertificate (S := S)) := by
  classical
  have aux : ∀ n : ℕ, ∀ (U : Type v) [Fintype U] [DecidableEq U]
      (R : ParentTree U), Fintype.card U = n →
      Nonempty (R.DistanceCertificate (S := S)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ _ R hcard
      by_cases hn : ∃ q : U, q ≠ R.root
      · obtain ⟨v, hv⟩ := R.exists_nonroot_leaf hn
        let U' := {q : U // q ≠ v.val}
        let R' := R.prune v hv
        let p : U' := ⟨R.parent v, hv v⟩
        have hlt : Fintype.card U' < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (by simp : ¬(v.val ≠ v.val))
        obtain ⟨D⟩ := ih (Fintype.card U') hlt U' R' rfl
        let d : U → U → ℕ := fun a b =>
          if ha : a = v.val then
            if hb : b = v.val then 0 else D.distance p ⟨b, hb⟩ + 1
          else if hb : b = v.val then D.distance p ⟨a, ha⟩ + 1
          else D.distance ⟨a, ha⟩ ⟨b, hb⟩
        have hd : ∀ a b, d a b = 0 ↔ a = b := by
          intro a b
          by_cases ha : a = v.val
          · subst a
            by_cases hb : b = v.val
            · subst b; simp [d]
            · simp [d, hb, Ne.symm hb]
          · by_cases hb : b = v.val
            · subst b; simp [d, ha]
            · simp only [d, dif_neg ha, dif_neg hb]
              rw [D.zero_iff]
              exact Subtype.ext_iff
        refine ⟨⟨d, hd, ?_⟩⟩
        intro μ hμ t a b
        have hpp : ∀ k, R'.joint μ (fun _ => equalInput μ t) p p k k = μ k := by
          intro k
          rw [D.formula μ hμ t p p, (D.zero_iff p p).mpr rfl]
          simp [stationaryPair_one]
        by_cases ha : a = v.val
        · subst a
          by_cases hb : b = v.val
          · subst b
            simpa [d] using R.joint_leaf_self_stationary v hv μ hμ t hpp
          · have hp := D.formula μ hμ t p (⟨b, hb⟩ : U')
            have hh := R.joint_leaf_other_stationary v hv (⟨b, hb⟩ : U')
              μ hμ t (t ^ D.distance p ⟨b, hb⟩) hp
            simpa [d, hb, pow_succ] using hh
        · by_cases hb : b = v.val
          · subst b
            have hp := D.formula μ hμ t p (⟨a, ha⟩ : U')
            have hh := R.joint_leaf_other_stationary v hv (⟨a, ha⟩ : U')
              μ hμ t (t ^ D.distance p ⟨a, ha⟩) hp
            funext i j
            rw [R.joint_swap μ (fun _ => equalInput μ t) a v.val i j]
            rw [hh]
            rw [stationaryPair_swap]
            simp only [d, dif_neg ha, dif_pos rfl, pow_succ]
          · have hh := R.joint_keep_leaf v hv μ (fun _ => equalInput μ t)
              (equalInput_row_sum hμ t) (⟨a, ha⟩ : U') (⟨b, hb⟩ : U')
            rw [hh]
            change R'.joint μ (fun _ => equalInput μ t)
              (⟨a, ha⟩ : U') (⟨b, hb⟩ : U') = _
            rw [D.formula μ hμ t]
            simp only [d, dif_neg ha, dif_neg hb]
      · have hs : ∀ q : U, q = R.root := by
          intro q
          by_contra hq
          exact hn ⟨q, hq⟩
        refine ⟨⟨fun _ _ => 0, ?_, ?_⟩⟩
        · intro a b
          constructor
          · intro _; exact (hs a).trans (hs b).symm
          · intro _; rfl
        · intro μ hμ t a b
          simpa using R.joint_singleton hs μ (fun _ => equalInput μ t) a b
  exact aux (Fintype.card V) V T rfl

noncomputable def distanceCertificate [Nonempty S] :
    T.DistanceCertificate (S := S) := Classical.choice T.distanceCertificate_nonempty

end ParentTree

theorem selectedTree_mass {E : Type w} [Fintype E]
    (N : RootBlobEdgeIndexed.Network V E (Fin 2))
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (σ : RootBlobSwitching.Switching N) (π : S → ℝ) (M : E → Mat S)
    (a : V → S) :
    (selectedTree N hG σ).mass π (fun v => M (σ v).val) a =
      RootBlobSwitching.resolvedMass N π M σ a := by
  classical
  unfold ParentTree.mass
  rw [prod_split N.root]
  unfold RootBlobSwitching.resolvedMass
  simp only [ParentTree.factor, selectedTree, dif_pos rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  simp only [v.property, dif_neg]
  rfl

theorem selectedTree_joint {E : Type w} [Fintype E]
    (N : RootBlobEdgeIndexed.Network V E (Fin 2))
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (σ : RootBlobSwitching.Switching N) (π : S → ℝ) (M : E → Mat S) :
    (selectedTree N hG σ).joint π (fun v => M (σ v).val)
      (N.observed 0) (N.observed 1) =
      RootBlobSwitching.resolvedPair N π M σ := by
  classical
  funext i j
  unfold ParentTree.joint RootBlobSwitching.resolvedPair
  apply Finset.sum_congr rfl
  intro a _
  rw [selectedTree_mass N hG σ π M a]
  have hc : (∀ o : Fin 2, a (N.observed o) = if o = 0 then i else j) ↔
      a (N.observed 0) = i ∧ a (N.observed 1) = j := by
    constructor
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1⟩
    · rintro ⟨h0, h1⟩ o
      fin_cases o
      · simpa using h0
      · simpa using h1
  rw [hc]
  split_ifs <;> simp

theorem selectedTree_output_leaf {E : Type w} [Fintype E]
    (N : RootBlobEdgeIndexed.Network V E (Fin 2))
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (σ : RootBlobSwitching.Switching N) (o : Fin 2) :
    (selectedTree N hG σ).IsLeaf (N.observed o) := by
  intro v
  exact Ne.symm (RootBlobSwitching.observed_not_parent N hG σ o v)


namespace ParentTree
variable (T : ParentTree V)

/-- A sits only on the edge into the first terminal vertex. -/
noncomputable def terminalMatrices (v : T.NR) (A B : Mat S) : T.NR → Mat S := by
  classical
  exact fun u => if u.val = v.val then A else B

theorem terminal_pruned (v : T.NR) (hv : T.IsLeaf v.val) (A B : Mat S) :
    T.prunedMatrices v hv (T.terminalMatrices v A B) = fun _ => B := by
  classical
  funext u
  simp [prunedMatrices, terminalMatrices, oldNonroot, u.val.property]

/-- Actual marginal of the original tree with one terminal A edge.
The exponent is distance in the pruned tree, hence graph-only. -/
theorem terminal_leaf_pair [Nonempty S]
    (v : T.NR) (hv : T.IsLeaf v.val) (u : {u : V // u ≠ v.val})
    (μ : S → ℝ) (hμ : (∑ i, μ i) = 1) (t : ℝ) (A : Mat S) :
    T.joint μ (T.terminalMatrices v A (equalInput μ t)) v.val u.val =
      blendPair μ
        (t ^ (T.prune v hv).distanceCertificate.distance
          ⟨T.parent v, hv v⟩ u) A := by
  classical
  rw [T.joint_leaf_other v hv μ (T.terminalMatrices v A (equalInput μ t)) u]
  rw [T.terminal_pruned]
  funext i j
  simp_rw [(T.prune v hv).distanceCertificate.formula μ hμ t]
  simp only [terminalMatrices, if_pos rfl]
  exact stationaryPair_terminal μ
    (t ^ (T.prune v hv).distanceCertificate.distance ⟨T.parent v, hv v⟩ u) A i j

end ParentTree

namespace Edge
variable {E : Type w} [Fintype E]
variable (N : RootBlobEdgeIndexed.Network V E (Fin 2))
variable (hG : RootBlobEdgeIndexed.GraphAdmitted N)

def firstVertex (σ : RootBlobSwitching.Switching N) :
    (selectedTree N hG σ).NR := ⟨N.observed 0, hG.2.1 0⟩

theorem firstLeaf (σ : RootBlobSwitching.Switching N) :
    (selectedTree N hG σ).IsLeaf (firstVertex N hG σ).val :=
  selectedTree_output_leaf N hG σ 0

def secondVertex : {u : V // u ≠ N.observed 0} :=
  ⟨N.observed 1, by
    intro he
    have h := hG.1 he
    norm_num at h⟩

def prunedTree (σ : RootBlobSwitching.Switching N) :
    ParentTree {u : V // u ≠ N.observed 0} :=
  (selectedTree N hG σ).prune (firstVertex N hG σ) (firstLeaf N hG σ)

def parentPort (σ : RootBlobSwitching.Switching N) :
    {u : V // u ≠ N.observed 0} :=
  ⟨(selectedTree N hG σ).parent (firstVertex N hG σ),
    firstLeaf N hG σ (firstVertex N hG σ)⟩

theorem parentPort_ne_second (σ : RootBlobSwitching.Switching N) :
    parentPort N hG σ ≠ secondVertex N hG := by
  intro he
  have hv := congrArg Subtype.val he
  exact (RootBlobSwitching.observed_not_parent N hG σ 1
    (firstVertex N hG σ)) hv.symm

noncomputable def pathExponent [Nonempty S] (σ : RootBlobSwitching.Switching N) : ℕ :=
  ((prunedTree N hG σ).distanceCertificate (S := S)).distance
    (parentPort N hG σ) (secondVertex N hG)

theorem pathExponent_pos [Nonempty S] (σ : RootBlobSwitching.Switching N) :
    0 < pathExponent (S := S) N hG σ := by
  apply Nat.pos_of_ne_zero
  intro he
  exact parentPort_ne_second N hG σ
    (((prunedTree N hG σ).distanceCertificate.zero_iff _ _).mp he)

theorem terminal_parameter_bridge (σ : RootBlobSwitching.Switching N)
    (A B : Mat S) :
    (fun v : (selectedTree N hG σ).NR =>
      RootBlobOpenProof.Edge.terminalAssignment N A B (σ v).val) =
    (selectedTree N hG σ).terminalMatrices (firstVertex N hG σ) A B := by
  classical
  funext v
  unfold RootBlobOpenProof.Edge.terminalAssignment ParentTree.terminalMatrices
  rw [(σ v).property]
  rfl

/-- Discharges the formerly explicit resolved-path obligation. Every
selected edge is the original edge occurrence; there is no independent
parameter copy for different resolutions. -/
noncomputable def resolvedPaths [Nonempty S]
    (H : Subgroup (Equiv.Perm S)) : RootBlobSwitching.ResolvedPathFormula N H where
  exponent := pathExponent N hG
  exponent_pos := pathExponent_pos N hG
  formula := by
    intro σ μ A t hμ hμpos hA ht0 ht1
    rw [← selectedTree_joint N hG σ μ
      (RootBlobOpenProof.Edge.terminalAssignment N A (equalInput μ t))]
    rw [terminal_parameter_bridge N hG σ]
    exact (selectedTree N hG σ).terminal_leaf_pair
      (firstVertex N hG σ) (firstLeaf N hG σ) (secondVertex N hG)
      μ hμ.1.2 t A

/-- Full original edge-indexed two-output image endpoint. Unlike previous
conditional wrappers, neither normalization nor resolved paths are inputs.
This remains unelaborated source, not a kernel-checked theorem. -/
theorem openImageClaim [Nonempty S] (W : E → ℝ)
    (H : Subgroup (Equiv.Perm S)) :
    RootBlobEdgeIndexed.OpenImageClaim N W H :=
  RootBlobSwitching.openImageClaim_of_resolvedPaths N W H
    (fun hG => resolvedPaths N hG H)

end Edge


/-- The named fork has the same graph and parameter contract. -/
theorem rootedFork_graph :
    RootBlobEdgeIndexed.GraphAdmitted RootBlobEdgeIndexed.rootedFork := by
  decide

theorem rootedFork_weights :
    RootBlobEdgeIndexed.WeightsAdmitted RootBlobEdgeIndexed.rootedFork
      RootBlobEdgeIndexed.forkWeights := by
  constructor
  · intro e
    norm_num [RootBlobEdgeIndexed.forkWeights]
  · intro v hv
    fin_cases v <;>
      norm_num [RootBlobEdgeIndexed.rootedFork, RootBlobEdgeIndexed.forkWeights,
        Fin.sum_univ_two] at *

namespace Edge
variable {E : Type w} [Fintype E]
variable (N : RootBlobEdgeIndexed.Network V E (Fin 2))

theorem openRealizationClaim [Nonempty S] (W : E → ℝ)
    (H : Subgroup (Equiv.Perm S)) :
    RootBlobEdgeIndexed.OpenRealizationClaim N W H := by
  intro hS hG hW
  exact RootBlobOpenProof.Edge.realize_of_resolution N W H
    (RootBlobSwitching.resolutionCertificate N W H hW (resolvedPaths N hG H))

/-- Full contextual fork replacement. The context is a joint-port kernel;
no independence of its two inputs is assumed or substituted. -/
theorem rootForkContextClaim [Nonempty S] {Z : Type*} [Fintype Z]
    (W : E → ℝ) (H : Subgroup (Equiv.Perm S)) (Q : S → S → Z → ℝ) :
    RootBlobEdgeIndexed.RootForkContextClaim N W H Q := by
  intro hS hG hW hQ
  rw [openImageClaim N W H hS hG hW,
    openImageClaim RootBlobEdgeIndexed.rootedFork RootBlobEdgeIndexed.forkWeights H
      hS rootedFork_graph rootedFork_weights]

end Edge

end RootBlobTreeMarginals
