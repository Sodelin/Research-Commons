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
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum.Ineq


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


/-!
Exact semantic kernel for the executable rational certificate slice.

This new component proves the mathematical weighted-square and finite-support
steps. It is not the unavailable physical representative provider, and does not
claim a refinement proof of Python/Rust parsing, arithmetic or source admission.
The selected1613 providers remain authoritative for their stronger actual-source
and sparse positive-root cardinality statements.
-/

namespace Astra.CommonCertificateKernel

open scoped BigOperators

def evalPolynomial : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: rest, x => a + x * evalPolynomial rest x

structure SquareTerm where
  weight : ℝ
  left : Bool
  right : Bool
  square : List ℝ

def SquareTerm.eval (t : SquareTerm) (x : ℝ) : ℝ :=
  t.weight * (if t.left then x else 1) * (if t.right then 1-x else 1) *
    (evalPolynomial t.square x)^2

theorem squareTerm_nonnegative (t : SquareTerm) (hw : 0 ≤ t.weight)
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ t.eval x := by
  unfold SquareTerm.eval
  apply mul_nonneg
  · apply mul_nonneg
    · exact mul_nonneg hw (by split; exact hx; exact zero_le_one)
    · split
      · exact sub_nonneg.mpr hx1
      · exact zero_le_one
  · exact sq_nonneg _

theorem square_identity_nonnegative {T : Type*} [Fintype T]
    (terms : T → SquareTerm) (hw : ∀ t, 0 ≤ (terms t).weight)
    (p : ℝ → ℝ) (identity : ∀ x, p x = ∑ t, (terms t).eval x)
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ p x := by
  rw [identity]
  exact Finset.sum_nonneg (fun t _ => squareTerm_nonnegative (terms t) (hw t) x hx hx1)

/-- One supported atom is forced to an exact root. Zero mass atoms need no
extra observation and are not incorrectly constrained by zero expectation. -/
theorem supported_atom_is_root {A : Type*} [Fintype A]
    (weight value : A → ℝ) (p : ℝ → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hp : ∀ a, 0 ≤ p (value a))
    (hz : ∑ a, weight a * p (value a) = 0)
    (a : A) (ha : 0 < weight a) : p (value a) = 0 := by
  have hsum := (Finset.sum_eq_zero_iff_of_nonneg
    (fun b (_ : b ∈ (Finset.univ : Finset A)) => mul_nonneg (hw b) (hp b))).mp hz
  have hproduct := hsum a (Finset.mem_univ a)
  exact (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt ha)

/-- The complete joint configuration is retained. Independence of its internal
coordinates is not an input. Every bank of every positive-mass configuration
is constrained by the same supplied certificate. -/
theorem joint_supported_bank_is_root {C B T : Type*}
    [Fintype C] [Fintype B] [Fintype T]
    (configWeight : C → ℝ) (bankWeight : B → ℝ) (value : C × B → ℝ)
    (hc : ∀ c, 0 ≤ configWeight c) (hb : ∀ b, 0 < bankWeight b)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (terms : T → SquareTerm) (ht : ∀ t, 0 ≤ (terms t).weight)
    (p : ℝ → ℝ) (identity : ∀ x, p x = ∑ t, (terms t).eval x)
    (hz : ∑ a : C × B, (configWeight a.1 * bankWeight a.2) * p (value a) = 0)
    (c : C) (hpositive : 0 < configWeight c) (b : B) :
    p (value (c,b)) = 0 ∧ value (c,b) ∈ Set.Ioc (0 : ℝ) 1 := by
  refine ⟨supported_atom_is_root _ value p ?_ ?_ hz (c,b) ?_, hv (c,b)⟩
  · intro a
    exact mul_nonneg (hc a.1) (hb a.2).le
  · intro a
    exact square_identity_nonnegative terms ht p identity _ (hv a).1.le (hv a).2
  · exact mul_pos hpositive (hb b)

/-- The deterministic generator uses only the supplied first and cubic moments.
This is a bounded sufficient acquisition rule, not universal acquisition. -/
theorem singleton_generator_identity (a x : ℝ) :
    2*a^3 - 3*a^2*x + x^3 = 2*a*(x-a)^2 + x*(x-a)^2 := by
  ring

theorem singleton_generator_nonnegative (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    0 ≤ 2*a^3 - 3*a^2*x + x^3 := by
  rw [singleton_generator_identity]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha) (sq_nonneg _))
    (mul_nonneg hx (sq_nonneg _))

theorem singleton_generator_annihilates (a : ℝ) :
    (2*a^3)*1 + (-3*a^2)*a + 1*a^3 = 0 := by
  ring

theorem singleton_generator_nonzero (a : ℝ) (ha : 0 < a) :
    (fun x : ℝ => 2*a^3 - 3*a^2*x + x^3) ≠ (fun _ => 0) := by
  intro h
  have hzero := congrFun h 0
  have hpositive : 0 < 2*a^3 := mul_pos (by norm_num) (pow_pos ha 3)
  simp only [mul_zero, sub_zero, zero_pow (by decide : 3 ≠ 0), add_zero] at hzero
  exact (ne_of_gt hpositive) hzero

#print axioms squareTerm_nonnegative
#print axioms square_identity_nonnegative
#print axioms supported_atom_is_root
#print axioms joint_supported_bank_is_root
#print axioms singleton_generator_identity
#print axioms singleton_generator_nonnegative
#print axioms singleton_generator_annihilates
#print axioms singleton_generator_nonzero

end Astra.CommonCertificateKernel


/- Exact certificate SHA256: 776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939. Generation is not compilation. -/
namespace Astra.Generated.Certificate_776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939
open Astra.CommonCertificateKernel
open scoped BigOperators

noncomputable def polynomial (x : ℝ) : ℝ := (((151168 : ℝ) / 13640319) * (x)^0 + ((-3856 : ℝ) / 72171) * (x)^1 + ((11428 : ℝ) / 56133) * (x)^3 + ((-11323 : ℝ) / 18711) * (x)^6 + ((1 : ℝ) / 1) * (x)^10)

theorem nonnegative (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ polynomial x := by
  have h0 := squareTerm_nonnegative ({ weight := ((37792 : ℝ) / 168399), left := false, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h1 := squareTerm_nonnegative ({ weight := ((17548 : ℝ) / 18711), left := true, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h2 := squareTerm_nonnegative ({ weight := ((35108 : ℝ) / 18711), left := false, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h3 := squareTerm_nonnegative ({ weight := ((8 : ℝ) / 3), left := true, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h4 := squareTerm_nonnegative ({ weight := ((23 : ℝ) / 9), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h5 := squareTerm_nonnegative ({ weight := ((2 : ℝ) / 1), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h6 := squareTerm_nonnegative ({ weight := ((1 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have hsum : 0 ≤ ((({ weight := ((37792 : ℝ) / 168399), left := false, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((17548 : ℝ) / 18711), left := true, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((35108 : ℝ) / 18711), left := false, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((8 : ℝ) / 3), left := true, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((23 : ℝ) / 9), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((2 : ℝ) / 1), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((1 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6)
  have identity : polynomial x = ((({ weight := ((37792 : ℝ) / 168399), left := false, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((17548 : ℝ) / 18711), left := true, right := false, square := [((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((35108 : ℝ) / 18711), left := false, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((8 : ℝ) / 3), left := true, right := false, square := [((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((23 : ℝ) / 9), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((2 : ℝ) / 1), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((1 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((2 : ℝ) / 9), ((-1 : ℝ) / 1), ((1 : ℝ) / 1)] } : SquareTerm)).eval x) := by
    dsimp [polynomial, SquareTerm.eval, evalPolynomial]
    ring
  rw [identity]
  exact hsum

theorem nonzero_value : polynomial 0 ≠ 0 := by
  norm_num [polynomial]

theorem annihilation : (((151168 : ℝ) / 13640319) * ((1 : ℝ) / 1) + ((-3856 : ℝ) / 72171) * ((1 : ℝ) / 2) + ((11428 : ℝ) / 56133) * ((1 : ℝ) / 6) + ((-11323 : ℝ) / 18711) * ((65 : ℝ) / 1458) + ((1 : ℝ) / 1) * ((1025 : ℝ) / 118098)) = 0 := by
  norm_num

theorem finite_supported_bank {A : Type*} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 2))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 6))
    (moment3 : ∑ a, weight a * (value a)^6 = ((65 : ℝ) / 1458))
    (moment4 : ∑ a, weight a * (value a)^10 = ((1025 : ℝ) / 118098))
    (a : A) (ha : 0 < weight a) :
    polynomial (value a) = 0 ∧ value a ∈ Set.Ioc (0 : ℝ) 1 := by
  have zero : ∑ b, weight b * polynomial (value b) = 0 := by
    calc
      _ = ∑ b, (((151168 : ℝ) / 13640319) * (weight b * (value b)^0) + ((-3856 : ℝ) / 72171) * (weight b * (value b)^1) + ((11428 : ℝ) / 56133) * (weight b * (value b)^3) + ((-11323 : ℝ) / 18711) * (weight b * (value b)^6) + ((1 : ℝ) / 1) * (weight b * (value b)^10)) := by
        apply Finset.sum_congr rfl
        intro b _
        dsimp [polynomial]
        ring
      _ = (((151168 : ℝ) / 13640319) * (∑ b, weight b * (value b)^0) + ((-3856 : ℝ) / 72171) * (∑ b, weight b * (value b)^1) + ((11428 : ℝ) / 56133) * (∑ b, weight b * (value b)^3) + ((-11323 : ℝ) / 18711) * (∑ b, weight b * (value b)^6) + ((1 : ℝ) / 1) * (∑ b, weight b * (value b)^10)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by
        rw [moment0, moment1, moment2, moment3, moment4]
        norm_num
  exact ⟨supported_atom_is_root weight value polynomial hw
    (fun b => nonnegative (value b) (hv b).1.le (hv b).2) zero a ha, hv a⟩

#print axioms nonnegative
#print axioms nonzero_value
#print axioms annihilation
#print axioms finite_supported_bank

end Astra.Generated.Certificate_776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939


namespace Astra.Generated.BankWitness_4efaf02ca21e032cc08c26d2901d8fe3d11a5d2909894a3c0caea77bffe0c8e8

open scoped BigOperators
open Astra.CommonMoment
open Astra.CommonMoment.RationalBank

def nodes : Finset ℚ := {((1 : ℚ) / (3 : ℚ)), ((2 : ℚ) / (3 : ℚ))}

def groupedWeight (q : ℚ) : ℚ :=
  if q = ((1 : ℚ) / (3 : ℚ)) then ((1 : ℚ) / (2 : ℚ)) else if q = ((2 : ℚ) / (3 : ℚ)) then ((1 : ℚ) / (2 : ℚ)) else (0 : ℚ)

def rawMoment (n : ℕ) : ℚ :=
  ((((1 : ℚ) / (4 : ℚ)) * ((1 : ℚ) / (3 : ℚ))^n + ((1 : ℚ) / (4 : ℚ)) * ((2 : ℚ) / (6 : ℚ))^n) + (((1 : ℚ) / (2 : ℚ)) * ((2 : ℚ) / (3 : ℚ))^n + (0 : ℚ) * (-7 : ℚ)^n))

theorem nodes_positive : ∀ q ∈ nodes, 0 < q := by
  intro q hq
  norm_num [nodes] at hq
  rcases hq with rfl | rfl <;> norm_num

theorem nodes_le_one : ∀ q ∈ nodes, q ≤ 1 := by
  intro q hq
  norm_num [nodes] at hq
  rcases hq with rfl | rfl <;> norm_num

theorem weights_positive : ∀ q ∈ nodes, 0 < groupedWeight q := by
  intro q hq
  norm_num [nodes] at hq
  rcases hq with rfl | rfl <;> norm_num [groupedWeight]

theorem mass_one : (∑ q ∈ nodes, groupedWeight q) = 1 := by
  norm_num [nodes, groupedWeight]

/-- All original rows are retained in rawMoment, including exactly zero mass
and distinct spellings of equal rationals. This is one all-exponent identity. -/
theorem grouped_moment_raw (n : ℕ) :
    (∑ q ∈ nodes, groupedWeight q * q^n) = rawMoment n := by
  norm_num [nodes, groupedWeight, rawMoment] <;> ring

noncomputable def law : FinitePositiveLaw :=
  fromGroupedRationals nodes groupedWeight nodes_positive weights_positive mass_one

theorem law_moment_raw (n : ℕ) :
    moment law n = (rawMoment n : ℝ) := by
  calc
    moment law n = ((∑ q ∈ nodes, groupedWeight q * q^n : ℚ) : ℝ) :=
      fromGroupedRationals_moment nodes groupedWeight nodes_positive weights_positive mass_one n
    _ = (rawMoment n : ℝ) := by rw [grouped_moment_raw]

theorem law_nodes_Ioc : ∀ x ∈ law.nodes, 0 < x ∧ x ≤ 1 := by
  intro x hx
  have h := fromGroupedRationals_survival_and_sparse_moments nodes groupedWeight
    nodes_positive nodes_le_one weights_positive mass_one
  exact ⟨law.node_pos x hx, h.1 x hx⟩

theorem sparse_moment_1 : moment law ((1 : ℕ).choose 2) = ((1 : ℚ) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_2 : moment law ((2 : ℕ).choose 2) = (((1 : ℚ) / (2 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_3 : moment law ((3 : ℕ).choose 2) = (((1 : ℚ) / (6 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_4 : moment law ((4 : ℕ).choose 2) = (((65 : ℚ) / (1458 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_5 : moment law ((5 : ℕ).choose 2) = (((1025 : ℚ) / (118098 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]


/-- Literal roots for this supplied mathematical bank. The unchanged certificate
also retains its separate conditional finite_supported_bank theorem. -/
theorem bank_nodes_root : ∀ x ∈ law.nodes, Astra.Generated.Certificate_776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939.polynomial x = 0 := by
  classical
  intro x hx
  change x ∈ nodes.image (fun q : ℚ => (q : ℝ)) at hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
  norm_num [nodes] at hq
  rcases hq with rfl | rfl <;> norm_num [Astra.Generated.Certificate_776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939.polynomial]

end Astra.Generated.BankWitness_4efaf02ca21e032cc08c26d2901d8fe3d11a5d2909894a3c0caea77bffe0c8e8
