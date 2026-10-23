import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Polynomial.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
CM-T02 abstract supplier extraction, source proposal only.
Original proof author: dot, 12 October 2026, G4ActualSparseCertificateExistence
SHA256 9ea04cbe390030381624d25b20be10751dff62f75d5d6e7752b88b9599a46418.
This file preserves that abstract proof-body prefix through momentExponent_strictMono.
Only the physical-bank import/open and unused later physical declarations are omitted.
Extraction: existing lane2, 15 October 2026. UNCOMPILED; requires fresh source review.
Original namespace and declaration names are preserved; do not co-import the original module.
No graph, physical receiver, runtime or executable claim is imported.
-/

namespace DotG4.ActualSparseCertificateExistence
set_option backward.isDefEq.respectTransparency false
open Polynomial Module
open scoped Classical BigOperators Polynomial

lemma signVariations_lt_support_card (P : ℝ[X]) (hP : P ≠ 0) :
    P.signVariations < P.support.card := by
  suffices ∀ n, ∀ P : ℝ[X], P.support.card = n → P ≠ 0 → P.signVariations < n by
    exact this _ P rfl hP
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hc hp
    by_cases he : P.eraseLead = 0
    · have hm : P = monomial P.natDegree P.leadingCoeff := by
        simpa only [he,zero_add] using (P.eraseLead_add_monomial_natDegree_leadingCoeff).symm
      have hv : P.signVariations = 0 := by rw [hm,signVariations_monomial]
      have hn : 0 < P.support.card := Finset.card_pos.mpr
        ⟨P.natDegree,natDegree_mem_support_of_nonzero hp⟩
      omega
    · have hl := eraseLead_support_card_lt hp
      have hi := ih P.eraseLead.support.card (by omega) P.eraseLead rfl he
      have hv := P.signVariations_le_eraseLead_succ
      have hs := card_support_eraseLead_add_one hp
      omega

noncomputable def sparseCombination {ι : Type*} [Fintype ι]
    (e : ι → Nat) : (ι → ℝ) →ₗ[ℝ] ℝ[X] :=
  Fintype.linearCombination ℝ (fun i => monomial (e i) 1)

lemma sparseCombination_injective {ι : Type*} [Fintype ι]
    (e : ι → Nat) (he : Function.Injective e) : Function.Injective (sparseCombination e) := by
  have h := (Polynomial.basisMonomials ℝ).linearIndependent.comp e he
  simpa only [sparseCombination,Polynomial.coe_basisMonomials,Function.comp_def] using
    h.fintypeLinearCombination_injective

lemma sparseCombination_support {ι : Type*} [Fintype ι]
    (e : ι → Nat) (c : ι → ℝ) :
    (sparseCombination e c).support ⊆ Finset.univ.image e := by
  intro n hn
  by_contra hnot
  have hne : ∀ i, e i ≠ n := by
    intro i hi
    exact hnot (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hi⟩)
  have hz : (sparseCombination e c).coeff n = 0 := by
    simp [sparseCombination,Fintype.linearCombination_apply,Polynomial.finset_sum_coeff,
      Polynomial.coeff_smul,Polynomial.coeff_monomial,hne]
  exact (Polynomial.mem_support_iff.mp hn) hz

/-- Underdetermined evaluation/derivative constraints, using the existing
monomial basis and finite-dimensional nonzero-kernel theorem. -/
lemma exists_sparse_double_zero (A : Finset ℝ) (e : Fin (2*A.card+1) → Nat)
    (he : Function.Injective e) :
    ∃ c : Fin (2*A.card+1) → ℝ, sparseCombination e c ≠ 0 ∧
      ∀ a ∈ A, (sparseCombination e c).IsRoot a ∧
        (Polynomial.derivative (sparseCombination e c)).IsRoot a := by
  let ev : ℝ[X] →ₗ[ℝ] (A → ℝ) := LinearMap.pi (fun a => Polynomial.leval (a:ℝ))
  let L : (Fin (2*A.card+1) → ℝ) →ₗ[ℝ] ((A → ℝ) × (A → ℝ)) :=
    (ev.prod (ev.comp Polynomial.derivative)).comp (sparseCombination e)
  have hdim : Module.finrank ℝ ((A → ℝ) × (A → ℝ)) <
      Module.finrank ℝ (Fin (2*A.card+1) → ℝ) := by
    simp only [Module.finrank_prod,Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe,Fintype.card_fin]
    omega
  obtain ⟨c,hc,hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim)
  have hp : sparseCombination e c ≠ 0 := by
    intro hz
    apply hc0
    apply sparseCombination_injective e he
    simpa using hz
  refine ⟨c,hp,?_⟩
  intro a ha
  have h := LinearMap.mem_ker.mp hc
  have h0 := congrArg (fun z : (A → ℝ) × (A → ℝ) => z.1 ⟨a,ha⟩) h
  have h1 := congrArg (fun z : (A → ℝ) × (A → ℝ) => z.2 ⟨a,ha⟩) h
  exact ⟨by simpa [L,ev,Polynomial.IsRoot] using h0,
    by simpa [L,ev,Polynomial.IsRoot] using h1⟩

/-- The doubled positive atoms exhaust Descartes' root budget. The remaining
factor has no positive root, so one orientation is nonnegative on x >= 0. -/
lemma orient_sparse_double_zero (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a)
    (P : ℝ[X]) (hp : P ≠ 0) (hs : P.support.card ≤ 2*A.card+1)
    (hz : ∀ a ∈ A, P.IsRoot a ∧ (Polynomial.derivative P).IsRoot a) :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ P.eval x) ∨
      (∀ x : ℝ, 0 ≤ x → P.eval x ≤ 0) := by
  let S : Multiset ℝ := A.val + A.val
  let Q : ℝ[X] := (S.map (fun a => Polynomial.X - Polynomial.C a)).prod
  have hS : S ≤ P.roots := by
    apply Multiset.le_iff_count.mpr
    intro a
    by_cases ha : a ∈ A
    · have hc : A.val.count a = 1 := Multiset.count_eq_one_of_mem A.nodup ha
      have hm := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr (hz a ha)
      have hm2 : 2 ≤ Polynomial.rootMultiplicity a P := by omega
      simpa only [S,Multiset.count_add,hc,Polynomial.count_roots] using hm2
    · have hc : A.val.count a = 0 := Multiset.count_eq_zero.mpr ha
      simp only [S,Multiset.count_add,hc,zero_add,Nat.zero_le]
  obtain ⟨R,hR⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hp S).mpr hS
  have hprod : Q*R ≠ 0 := by change (S.map (fun a => X-C a)).prod * R ≠ 0; rwa [← hR]
  have hr : R ≠ 0 := by intro h; simp [h] at hprod
  have hroots : P.roots = S + R.roots := by
    rw [hR,Polynomial.roots_mul hprod,Polynomial.roots_multiset_prod_X_sub_C]
  have hcountA : A.val.countP (0 < ·) = A.card :=
    Multiset.countP_eq_card.mpr hA
  have hcountS : S.countP (0 < ·) = 2*A.card := by
    simp only [S,Multiset.countP_add,hcountA]
    omega
  have hb : P.roots.countP (0 < ·) ≤ 2*A.card := by
    have hd := P.roots_countP_pos_le_signVariations
    have hv := signVariations_lt_support_card P hp
    omega
  have hcountR : R.roots.countP (0 < ·) = 0 := by
    rw [hroots,Multiset.countP_add,hcountS] at hb
    omega
  have hrootR : ∀ y, R.IsRoot y → y ≤ 0 := by
    intro y hy
    exact le_of_not_gt ((Multiset.countP_eq_zero.mp hcountR) y ((Polynomial.mem_roots hr).mpr hy))
  have hQ : ∀ x : ℝ, 0 ≤ Q.eval x := by
    intro x
    simp only [Q,S,Multiset.map_add,Multiset.prod_add,Polynomial.eval_mul]
    exact mul_self_nonneg _
  by_cases hl : 0 ≤ R.leadingCoeff
  · left
    intro x hx
    rw [hR,Polynomial.eval_mul]
    exact mul_nonneg (hQ x) (Polynomial.zero_le_eval_of_roots_le_of_leadingCoeff_nonneg
      (fun y hy => (hrootR y hy).trans hx) hl)
  · right
    intro x hx
    rw [hR,Polynomial.eval_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hQ x)
      (Polynomial.eval_le_zero_of_roots_le_of_leadingCoeff_nonpos
        (fun y hy => (hrootR y hy).trans hx) (le_of_not_ge hl))

/-- Nonnegative sparse exposing polynomial on any 2m+1 distinct exponents.
The atoms may include one, but must be strictly positive. -/
theorem exists_nonnegative_sparse_polynomial (A : Finset ℝ)
    (hA : ∀ a ∈ A, 0 < a) (e : Fin (2*A.card+1) → Nat) (he : Function.Injective e) :
    ∃ c : Fin (2*A.card+1) → ℝ, sparseCombination e c ≠ 0 ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ (sparseCombination e c).eval x) ∧
      ∀ a ∈ A, (sparseCombination e c).eval a = 0 := by
  obtain ⟨c,hp,hz⟩ := exists_sparse_double_zero A e he
  have hs : (sparseCombination e c).support.card ≤ 2*A.card+1 :=
    (Finset.card_le_card (sparseCombination_support e c)).trans
      ((Finset.card_image_le).trans (by simp))
  rcases orient_sparse_double_zero A hA _ hp hs hz with hpos | hneg
  · exact ⟨c,hp,hpos,fun a ha => (hz a ha).1⟩
  · refine ⟨-c,?_,?_,?_⟩
    · simpa only [map_neg,neg_ne_zero] using hp
    · intro x hx
      simpa only [map_neg,Polynomial.eval_neg,neg_nonneg] using hneg x hx
    · intro a ha
      simpa only [map_neg,Polynomial.eval_neg,neg_eq_zero,Polynomial.IsRoot] using (hz a ha).1

lemma momentExponent_strictMono : StrictMono (fun n : Nat => (n+1).choose 2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs : (n+1+1).choose 2 = (n+1) + (n+1).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ (n+1) 1
  omega

end DotG4.ActualSparseCertificateExistence
