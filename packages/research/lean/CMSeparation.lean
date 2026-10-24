import CMFoundations
import Mathlib.Tactic.NormNum

/-!
COMMON-MOMENT-HAND-001-v1, CM-T02 SOURCE CANDIDATE.
UNCOMPILED / UNEXECUTED; no physical compiler or executable binding.
The doubled-root budget argument reuses the proof pattern of
DotG4.ActualSparseCertificateExistence.orient_sparse_double_zero.
-/

namespace Astra.CommonMoment

open Polynomial
open DotG4.ActualSparseCertificateExistence
open scoped BigOperators

/-- Exact positive zero-set corollary needed beyond nonnegativity. -/
theorem eval_ne_zero_off_double_roots
    (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a)
    (P : ℝ[X]) (hp : P ≠ 0) (hs : P.support.card ≤ 2 * A.card + 1)
    (hz : ∀ a ∈ A, P.IsRoot a ∧ (Polynomial.derivative P).IsRoot a)
    (x : ℝ) (hx : 0 < x) (hxA : x ∉ A) : P.eval x ≠ 0 := by
  classical
  let S : Multiset ℝ := A.val + A.val
  have hS : S ≤ P.roots := by
    apply Multiset.le_iff_count.mpr
    intro a
    by_cases ha : a ∈ A
    · have hc : A.val.count a = 1 := Multiset.count_eq_one_of_mem A.nodup ha
      have hm := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr (hz a ha)
      have hm2 : 2 ≤ Polynomial.rootMultiplicity a P := by omega
      simpa only [S, Multiset.count_add, hc, Polynomial.count_roots] using hm2
    · have hc : A.val.count a = 0 := Multiset.count_eq_zero.mpr ha
      simp only [S, Multiset.count_add, hc, zero_add, Nat.zero_le]
  obtain ⟨R, hR⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hp S).mpr hS
  have hprod : (S.map (fun a => Polynomial.X - Polynomial.C a)).prod * R ≠ 0 := by
    rwa [← hR]
  have hroots : P.roots = S + R.roots := by
    rw [hR, Polynomial.roots_mul hprod, Polynomial.roots_multiset_prod_X_sub_C]
  have hcountA : A.val.countP (0 < ·) = A.card :=
    Multiset.countP_eq_card.mpr hA
  have hcountS : S.countP (0 < ·) = 2 * A.card := by
    simp only [S, Multiset.countP_add, hcountA]
    omega
  have hb : P.roots.countP (0 < ·) ≤ 2 * A.card := by
    have h := cm_l01_positive_root_bound P hp (2 * A.card + 1) hs
    omega
  have hcountR : R.roots.countP (0 < ·) = 0 := by
    rw [hroots, Multiset.countP_add, hcountS] at hb
    omega
  intro hzero
  have hmem : x ∈ P.roots := (Polynomial.mem_roots hp).mpr hzero
  rw [hroots] at hmem
  rcases Multiset.mem_add.mp hmem with hmemS | hmemR
  · have : x ∈ A := by simpa [S] using hmemS
    exact hxA this
  · exact (Multiset.countP_eq_zero.mp hcountR) x hmemR hx

/-- Existing double-zero and orientation suppliers, strengthened to strictness
off the prescribed positive support by its exhausted root budget. -/
theorem exists_strict_sparse_separator
    (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a)
    (e : Fin (2 * A.card + 1) → ℕ) (he : Function.Injective e) :
    ∃ c : Fin (2 * A.card + 1) → ℝ,
      sparseCombination e c ≠ 0 ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ (sparseCombination e c).eval x) ∧
      (∀ a ∈ A, (sparseCombination e c).eval a = 0) ∧
      ∀ x : ℝ, 0 < x → x ∉ A → 0 < (sparseCombination e c).eval x := by
  classical
  obtain ⟨c, hp, hz⟩ := exists_sparse_double_zero A e he
  have hs : (sparseCombination e c).support.card ≤ 2 * A.card + 1 :=
    (Finset.card_le_card (sparseCombination_support e c)).trans
      ((Finset.card_image_le).trans (by simp))
  have hne := eval_ne_zero_off_double_roots A hA (sparseCombination e c) hp hs hz
  rcases orient_sparse_double_zero A hA _ hp hs hz with hpos | hneg
  · refine ⟨c, hp, hpos, fun a ha => (hz a ha).1, ?_⟩
    intro x hx hxA
    rcases lt_or_eq_of_le (hpos x hx.le) with hlt | heq
    · exact hlt
    · exact False.elim (hne x hx hxA heq.symm)
  · refine ⟨-c, ?_, ?_, ?_, ?_⟩
    · simpa only [map_neg, neg_ne_zero] using hp
    · intro x hx
      simpa only [map_neg, Polynomial.eval_neg, neg_nonneg] using hneg x hx
    · intro a ha
      simpa only [map_neg, Polynomial.eval_neg, neg_eq_zero, Polynomial.IsRoot]
        using (hz a ha).1
    · intro x hx hxA
      rcases lt_or_eq_of_le (hneg x hx.le) with hlt | heq
      · simpa only [map_neg, Polynomial.eval_neg] using (neg_pos.mpr hlt)
      · exact False.elim (hne x hx hxA heq)

noncomputable def expectation (μ : FinitePositiveLaw) (f : ℝ → ℝ) : ℝ :=
  ∑ x ∈ μ.nodes, μ.weight x * f x

/-- The expectation uses only the supplied sparse moments. -/
theorem expectation_sparseCombination {ι : Type*} [Fintype ι]
    (μ : FinitePositiveLaw) (e : ι → ℕ) (c : ι → ℝ) :
    expectation μ (fun x => (sparseCombination e c).eval x) =
      ∑ i, c i * moment μ (e i) := by
  classical
  have heval (x : ℝ) :
      (sparseCombination e c).eval x = ∑ i, c i * x ^ (e i) := by
    simp [sparseCombination, Fintype.linearCombination_apply, Polynomial.smul_monomial,
      Polynomial.eval_finsetSum]
  unfold expectation
  simp_rw [heval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  unfold moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Positive finite laws cannot match a smaller positive support on a sparse
Chebyshev moment set of size twice that smaller support plus one. -/
theorem support_card_le_of_equal_sparse_moments
    (σ τ : FinitePositiveLaw)
    (e : Fin (2 * τ.nodes.card + 1) → ℕ) (he : Function.Injective e)
    (hm : ∀ i, moment σ (e i) = moment τ (e i)) :
    σ.nodes.card ≤ τ.nodes.card := by
  classical
  by_contra hcard
  have hc : τ.nodes.card < σ.nodes.card := lt_of_not_ge hcard
  obtain ⟨c, _hp, hnonneg, hzero, hstrict⟩ :=
    exists_strict_sparse_separator τ.nodes τ.node_pos e he
  obtain ⟨x, hx, hxτ⟩ : ∃ x ∈ σ.nodes, x ∉ τ.nodes := by
    by_contra h
    have hsub : σ.nodes ⊆ τ.nodes := by
      intro x hx
      by_contra hxτ
      exact h ⟨x, hx, hxτ⟩
    exact (not_le_of_gt hc) (Finset.card_le_card hsub)
  have hσ : 0 < expectation σ (fun x => (sparseCombination e c).eval x) := by
    apply Finset.sum_pos'
    · intro y hy
      exact mul_nonneg (σ.weight_pos y hy).le (hnonneg y (σ.node_pos y hy).le)
    · exact ⟨x, hx, mul_pos (σ.weight_pos x hx) (hstrict x (σ.node_pos x hx) hxτ)⟩
  have hτ : expectation τ (fun x => (sparseCombination e c).eval x) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    change τ.weight y * (sparseCombination e c).eval y = 0
    rw [hzero y hy, mul_zero]
  have heq : expectation σ (fun x => (sparseCombination e c).eval x) =
      expectation τ (fun x => (sparseCombination e c).eval x) := by
    rw [expectation_sparseCombination, expectation_sparseCombination]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hm i]
  rw [heq, hτ] at hσ
  exact (lt_irrefl (0 : ℝ)) hσ

def capFiveLevels : Finset ℕ := {0, 1, 3, 6, 10}

/-- CM-T02 abstract finite-law endpoint. This declaration is SOURCE ONLY until
the sole compiler workflow actually elaborates and audits it. -/
theorem cm_t02_cap_five_separation
    (σ τ : FinitePositiveLaw) (hσ : 3 ≤ σ.nodes.card) (hτ : τ.nodes.card ≤ 2) :
    ∃ k ∈ capFiveLevels, moment σ k ≠ moment τ k := by
  classical
  by_contra hnot
  have hm : ∀ k ∈ capFiveLevels, moment σ k = moment τ k := by
    intro k hk
    by_contra hne
    exact hnot ⟨k, hk, hne⟩
  let e : Fin (2 * τ.nodes.card + 1) → ℕ := fun i => (i.val + 1).choose 2
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact momentExponent_strictMono.injective hij
  have hbound : σ.nodes.card ≤ τ.nodes.card :=
    support_card_le_of_equal_sparse_moments σ τ e he (by
      intro i
      have hi := i.isLt
      have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by
        omega
      rcases hcases with h | h | h | h | h
      all_goals exact hm _ (by norm_num [capFiveLevels, e, h, Nat.choose_two_right]))
  omega

end Astra.CommonMoment
