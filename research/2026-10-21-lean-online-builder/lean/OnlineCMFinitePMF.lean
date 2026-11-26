import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Polynomial.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith


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
namespace UnifiedLean.Source.SourcePoissonExponential
open scoped BigOperators
lemma bind_probability_real {A B : Type*} (p : PMF A) (f : A → PMF B) (b : B) :
    ((p.bind f) b).toReal = ∑' a, (p a).toReal * (f a b).toReal := by
  rw [PMF.bind_apply,ENNReal.tsum_toReal_eq (fun a =>
    ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (f a) b))]
  simp only [ENNReal.toReal_mul]


end UnifiedLean.Source.SourcePoissonExponential

namespace DotG4.ActualPositiveGridUniqueness
open scoped Classical BigOperators
noncomputable def gridWeight {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (x : ι → ℝ) (a : ℝ) : ℝ := ∑ i, if x i = a then w i else 0

lemma gridWeight_moment {ι : Type*} [Fintype ι] (A : Finset ℝ)
    (w x : ι → ℝ) (hx : ∀ i, x i ∈ A) (n : Nat) :
    ∑ a : A, gridWeight w x (a:ℝ) * (a:ℝ)^n = ∑ i, w i * x i ^ n := by
  simp only [gridWeight,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let a0 : A := ⟨x i,hx i⟩
  rw [Finset.sum_eq_single a0]
  · simp [a0]
  · intro a _ hne
    have hne' : x i ≠ (a:ℝ) := by
      intro h
      apply hne
      apply Subtype.ext
      exact h.symm
    simp [hne']
  · simp

lemma gridWeight_zero_outside {ι : Type*} [Fintype ι] (A : Finset ℝ)
    (w x : ι → ℝ) (hx : ∀ i, x i ∈ A) (a : ℝ) (ha : a ∉ A) :
    gridWeight w x a = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hne : x i ≠ a := by intro h; exact ha (h ▸ hx i)
  simp [hne]

lemma gridWeight_eq_mapped_mass {ι : Type*} [Fintype ι] (p : PMF ι)
    (x : ι → ℝ) (a : ℝ) :
    gridWeight (fun i => (p i).toReal) x a = ((p.map x) a).toReal := by
  rw [PMF.map_apply,tsum_fintype,ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i = a
    · simp [h]
    · simp [h,Ne.symm h]
  · intro i _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top


end DotG4.ActualPositiveGridUniqueness

namespace DotG4.WholeProfileDetermination
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι]
noncomputable def positiveSupportPMF (p : PMF ι) : PMF {a : ι // p a ≠ 0} :=
  PMF.ofFintype (fun a => p a.val) (by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a => p a ≠ 0))
      (fun a => by simp) (fun a => p a)]
    have hs : (∑ a ∈ Finset.univ.filter (fun a => p a ≠ 0), p a) = ∑ a, p a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : p a = 0 <;> simp [h]
    rw [hs]
    simpa only [tsum_fintype] using p.tsum_coe)

lemma positiveSupportPMF_positive (p : PMF ι) (a : {a : ι // p a ≠ 0}) :
    0 < (positiveSupportPMF p a).toReal :=
  ENNReal.toReal_pos a.property (p.apply_ne_top a.val)

lemma positiveSupportPMF_sum (p : PMF ι) (f : ι → ℝ) :
    (∑ a : {a : ι // p a ≠ 0}, (positiveSupportPMF p a).toReal * f a.val) =
      ∑ a, (p a).toReal * f a := by
  change (∑ a : {a : ι // p a ≠ 0}, (p a.val).toReal * f a.val) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a => p a ≠ 0))
    (fun a => by simp) (fun a => (p a).toReal * f a),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : p a = 0 <;> simp [h]

lemma positiveSupportPMF_map {β : Type*} (p : PMF ι) (f : ι → β) :
    (positiveSupportPMF p).map (fun a => f a.val) = p.map f := by
  apply PMF.ext
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [PMF.map,UnifiedLean.Source.SourcePoissonExponential.bind_probability_real,tsum_fintype]
  exact positiveSupportPMF_sum p (fun a => (PMF.pure (f a) b).toReal)


end DotG4.WholeProfileDetermination

namespace DotG4.WholeProfileDetermination
open scoped BigOperators
noncomputable def finiteBankMoment {ι : Type*} [Fintype ι]
    (p : PMF ι) (x : ι → ℝ) (k : Nat) : ℝ :=
  ∑ a, (p a).toReal * x a ^ k.choose 2


end DotG4.WholeProfileDetermination


/-! Semantic packaging of an existing finite PMF, without a new grouping
algorithm. The physical import context uses the original sparse supplier
instead of importing the duplicate extracted CMSparseSupplier. -/

namespace Astra.CommonMoment.FinitePMF

open scoped BigOperators Classical
open DotG4.ActualPositiveGridUniqueness DotG4.WholeProfileDetermination

variable {ι : Type*} [Fintype ι]

noncomputable def positiveImage (p : PMF ι) (x : ι → ℝ) : Finset ℝ :=
  Finset.univ.image (fun a : {i : ι // p i ≠ 0} => x a.val)

noncomputable def groupedWeight (p : PMF ι) (x : ι → ℝ) : ℝ → ℝ :=
  gridWeight (fun a => (positiveSupportPMF p a).toReal)
    (fun a => x a.val)

theorem grouped_moment (p : PMF ι) (x : ι → ℝ) (n : ℕ) :
    (∑ a ∈ positiveImage p x, groupedWeight p x a * a ^ n) =
      ∑ i, (p i).toReal * x i ^ n := by
  classical
  have h := gridWeight_moment (positiveImage p x)
    (fun a => (positiveSupportPMF p a).toReal) (fun a => x a.val)
    (fun a => Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩) n
  rw [positiveSupportPMF_sum p (fun i => x i ^ n)] at h
  calc
    _ = ∑ a : positiveImage p x,
        groupedWeight p x a * (a : ℝ) ^ n :=
      (Finset.sum_coe_sort (positiveImage p x)
        (fun a => groupedWeight p x a * a ^ n)).symm
    _ = _ := h

theorem grouped_weight_positive (p : PMF ι) (x : ι → ℝ)
    (a : ℝ) (ha : a ∈ positiveImage p x) :
    0 < groupedWeight p x a := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset {j : ι // p j ≠ 0}))
    (f := fun j => if x j.val = x i.val then
      (positiveSupportPMF p j).toReal else 0)
    (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
  exact lt_of_lt_of_le (positiveSupportPMF_positive p i)
    (by simpa [groupedWeight, gridWeight] using h)

theorem grouped_mass_one (p : PMF ι) (x : ι → ℝ) :
    (∑ a ∈ positiveImage p x, groupedWeight p x a) = 1 := by
  classical
  have hsum : (∑ i, (p i).toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun i _ => p.apply_ne_top i)]
    simpa only [tsum_fintype, ENNReal.toReal_one] using
      congrArg ENNReal.toReal p.tsum_coe
  calc
    _ = ∑ i, (p i).toReal := by
      simpa only [pow_zero, mul_one] using grouped_moment p x 0
    _ = 1 := hsum

noncomputable def fromFinitePMF (p : PMF ι) (x : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i) : FinitePositiveLaw where
  nodes := positiveImage p x
  weight := groupedWeight p x
  node_pos := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hx i.val i.property
  weight_pos := grouped_weight_positive p x
  mass_one := grouped_mass_one p x

theorem fromFinitePMF_moment (p : PMF ι) (x : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i) (n : ℕ) :
    moment (fromFinitePMF p x hx) n = ∑ i, (p i).toReal * x i ^ n :=
  grouped_moment p x n

theorem fromFinitePMF_sparse_moment (p : PMF ι) (x : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i) (k : ℕ) :
    moment (fromFinitePMF p x hx) (k.choose 2) = finiteBankMoment p x k :=
  fromFinitePMF_moment p x hx (k.choose 2)

theorem fromFinitePMF_nodes_Ioc (p : PMF ι) (x : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i)
    (hx1 : ∀ i, p i ≠ 0 → x i ≤ 1) :
    ∀ a ∈ (fromFinitePMF p x hx).nodes, a ∈ Set.Ioc (0 : ℝ) 1 := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨hx i.val i.property, hx1 i.val i.property⟩

theorem fromFinitePMF_weight_mapped_mass (p : PMF ι) (x : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i) (a : ℝ) :
    (fromFinitePMF p x hx).weight a = ((p.map x) a).toReal := by
  change gridWeight (fun i => (positiveSupportPMF p i).toReal)
    (fun i => x i.val) a = _
  rw [gridWeight_eq_mapped_mass, positiveSupportPMF_map]

end Astra.CommonMoment.FinitePMF
