import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Polynomial.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Logic.Function.Basic


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


/-!
COMMON-MOMENT-HAND-001-v1: first disjoint lane2 SOURCE CANDIDATE.
UNCOMPILED AND UNEXECUTED. No CM-T02 endpoint or physical compiler binding
is claimed. Reuses the existing sparse-certificate module and Mathlib rule
of signs; no new axiom, opaque certificate assumption or placeholder proof.
-/

namespace Astra.CommonMoment

open Polynomial
open scoped BigOperators

/-- Positive-axis laws for CM-T02; CM-T01 additionally requires nodes below one. -/
structure FinitePositiveLaw where
  nodes : Finset ℝ
  weight : ℝ → ℝ
  node_pos : ∀ x ∈ nodes, 0 < x
  weight_pos : ∀ x ∈ nodes, 0 < weight x
  mass_one : (∑ x ∈ nodes, weight x) = 1

noncomputable def moment (μ : FinitePositiveLaw) (k : ℕ) : ℝ :=
  ∑ x ∈ μ.nodes, μ.weight x * x ^ k

def StrictlyInterior (μ : FinitePositiveLaw) : Prop :=
  ∀ x ∈ μ.nodes, x < 1

theorem moment_zero (μ : FinitePositiveLaw) : moment μ 0 = 1 := by
  simpa [moment] using μ.mass_one

/-- CM-L01, via the already selected Descartes and sparse-support suppliers.
Polynomial.roots is a multiset, so this count includes multiplicities. -/
theorem positive_root_count_lt_support_card (P : ℝ[X]) (hP : P ≠ 0) :
    P.roots.countP (0 < ·) < P.support.card := by
  exact lt_of_le_of_lt P.roots_countP_pos_le_signVariations
    (DotG4.ActualSparseCertificateExistence.signVariations_lt_support_card P hP)

theorem cm_l01_positive_root_bound (P : ℝ[X]) (hP : P ≠ 0)
    (r : ℕ) (hs : P.support.card ≤ r) :
    P.roots.countP (0 < ·) ≤ r - 1 := by
  have h := positive_root_count_lt_support_card P hP
  omega

/-- The singleton competitor repair uses only exponents zero, one and three. -/
def singletonPolynomial (a x : ℝ) : ℝ :=
  (x - a) ^ 2 * (x + 2 * a)

theorem singletonPolynomial_expansion (a x : ℝ) :
    singletonPolynomial a x = x ^ 3 - 3 * a ^ 2 * x + 2 * a ^ 3 := by
  unfold singletonPolynomial
  ring

theorem singletonPolynomial_at_node (a : ℝ) :
    singletonPolynomial a a = 0 := by
  simp [singletonPolynomial]

theorem singletonPolynomial_nonneg {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 ≤ singletonPolynomial a x := by
  unfold singletonPolynomial
  exact mul_nonneg (sq_nonneg _) (by linarith)

theorem singletonPolynomial_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxa : x ≠ a) : 0 < singletonPolynomial a x := by
  unfold singletonPolynomial
  have hs : 0 < (x - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxa)
  exact mul_pos hs (by linarith)

theorem three_products_strict {a b c d : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hab : a < b) (hcd : c < d) :
    a * c < a * d ∧ a * d < b * d := by
  exact ⟨mul_lt_mul_of_pos_left hcd ha, mul_lt_mul_of_pos_right hab hd⟩

end Astra.CommonMoment


namespace Astra.RationalBankMoments

open scoped BigOperators

def rationalMoment {A : Type*} [Fintype A] (weight value : A → ℚ) (k : ℕ) : ℚ :=
  ∑ a, weight a * value a ^ (k.choose 2)

noncomputable def realMoment {A : Type*} [Fintype A]
    (weight value : A → ℝ) (k : ℕ) : ℝ :=
  ∑ a, weight a * value a ^ (k.choose 2)

/-- One fixed rational bank is cast once; changing k changes only its exponent. -/
theorem cast_moment {A : Type*} [Fintype A] (weight value : A → ℚ) (k : ℕ) :
    realMoment (fun a => (weight a : ℝ)) (fun a => (value a : ℝ)) k =
      (rationalMoment weight value k : ℝ) := by
  unfold realMoment rationalMoment
  have h := map_sum (Rat.castHom ℝ)
    (fun a => weight a * value a ^ (k.choose 2)) Finset.univ
  simpa only [Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow] using h.symm

theorem cast_normalized_bank {A : Type*} [Fintype A]
    (weight value : A → ℚ) (hw : ∀ a, 0 ≤ weight a)
    (hx : ∀ a, 0 < value a ∧ value a ≤ 1) (hmass : ∑ a, weight a = 1) :
    (∀ a, (0:ℝ) ≤ weight a) ∧
    (∀ a, (0:ℝ) < value a ∧ (value a : ℝ) ≤ 1) ∧
    (∑ a, (weight a : ℝ)) = 1 ∧
    ∀ k, realMoment (fun a => (weight a : ℝ)) (fun a => (value a : ℝ)) k =
      (rationalMoment weight value k : ℝ) := by
  refine ⟨?_,?_,?_,cast_moment weight value⟩
  · intro a
    exact_mod_cast hw a
  · intro a
    constructor
    · exact_mod_cast (hx a).1
    · exact_mod_cast (hx a).2
  · calc
      _ = ((∑ a, weight a : ℚ) : ℝ) := (map_sum (Rat.castHom ℝ) weight Finset.univ).symm
      _ = 1 := by rw [hmass]; norm_num

end Astra.RationalBankMoments


/-! A typed receiver for an ALREADY grouped distinct rational bank.
This does not compute the positive image or refine a native grouping program.
The imported CM structure is the exact existing accepted component source. -/

namespace Astra.CommonMoment.RationalBank

open scoped BigOperators

noncomputable def castWeight (w : ℚ → ℚ) : ℝ → ℝ :=
  Function.extend (fun q : ℚ => (q : ℝ)) (fun q => (w q : ℝ)) (fun _ => 0)

theorem castWeight_at (w : ℚ → ℚ) (q : ℚ) :
    castWeight w (q : ℝ) = (w q : ℝ) :=
  Rat.cast_injective.extend_apply _ _ q

theorem cast_nodes_sum (S : Finset ℚ) (f : ℝ → ℝ) :
    (∑ x ∈ S.image (fun q : ℚ => (q : ℝ)), f x) = ∑ q ∈ S, f (q : ℝ) := by
  classical
  exact Finset.sum_image (fun a _ b _ h => Rat.cast_injective h)

/-- No normalization or removal is performed here: the caller supplies exactly
the distinct positive-mass rational scalar image and its grouped weights. -/
noncomputable def fromGroupedRationals (S : Finset ℚ) (w : ℚ → ℚ)
    (hx : ∀ q ∈ S, 0 < q) (hw : ∀ q ∈ S, 0 < w q)
    (hmass : ∑ q ∈ S, w q = 1) : FinitePositiveLaw := by
  classical
  refine { nodes := S.image (fun q : ℚ => (q : ℝ))
           weight := castWeight w
           node_pos := ?_
           weight_pos := ?_
           mass_one := ?_ }
  · intro x hxmem
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hxmem
    exact_mod_cast hx q hq
  · intro x hxmem
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hxmem
    rw [castWeight_at]
    exact_mod_cast hw q hq
  · rw [cast_nodes_sum]
    simp only [castWeight_at]
    calc
      _ = ((∑ q ∈ S, w q : ℚ) : ℝ) := (map_sum (Rat.castHom ℝ) w S).symm
      _ = 1 := by rw [hmass]; norm_num

theorem fromGroupedRationals_moment (S : Finset ℚ) (w : ℚ → ℚ)
    (hx : ∀ q ∈ S, 0 < q) (hw : ∀ q ∈ S, 0 < w q)
    (hmass : ∑ q ∈ S, w q = 1) (n : ℕ) :
    moment (fromGroupedRationals S w hx hw hmass) n =
      ((∑ q ∈ S, w q * q^n : ℚ) : ℝ) := by
  classical
  change (∑ x ∈ S.image (fun q : ℚ => (q : ℝ)), castWeight w x*x^n) = _
  rw [cast_nodes_sum]
  simp only [castWeight_at]
  have h := map_sum (Rat.castHom ℝ) (fun q => w q*q^n) S
  simpa only [Rat.coe_castHom,Rat.cast_mul,Rat.cast_pow] using h.symm

/-- The CM positive-axis constructor does not itself impose an upper bound.
This separate survival fact retains the old weighted-square receiver domain. -/
theorem fromGroupedRationals_survival_and_sparse_moments
    (S : Finset ℚ) (w : ℚ → ℚ)
    (hx : ∀ q ∈ S, 0 < q) (hx1 : ∀ q ∈ S, q ≤ 1)
    (hw : ∀ q ∈ S, 0 < w q) (hmass : ∑ q ∈ S, w q = 1) :
    let mu := fromGroupedRationals S w hx hw hmass
    (∀ x ∈ mu.nodes, x ≤ 1) ∧
      ∀ k : ℕ, moment mu (k.choose 2) =
        ((∑ q ∈ S, w q*q^(k.choose 2) : ℚ) : ℝ) := by
  classical
  dsimp only
  refine ⟨?_,fun k => fromGroupedRationals_moment S w hx hw hmass (k.choose 2)⟩
  intro x hxmem
  change x ∈ S.image (fun q : ℚ => (q : ℝ)) at hxmem
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hxmem
  exact_mod_cast hx1 q hq

end Astra.CommonMoment.RationalBank
