import G4ActualObservableBankCertificate
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Polynomial.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Semantic sparse certificate existence for original finite COMMON banks

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED draft.
Formal composition of inherited ALL-CAP Section 4 / D2, using pinned Mathlib
Descartes, rank-nullity, root multiplicity and polynomial order theorems.
Supplier audit SHA 7bbd0603d00a4be4ad31516e95937e5b7ef6db50b169da9724253290b993af36;
pins SHA f52c48f09545041ef2590f2b0b2dcbed7b96c4104608ba6d5c31733806cb2fa3.
Atoms are distinct and positive; endpoint one is retained. The conclusion is
real semantic existence, not an executable QE producer, algebraic witness
transfer, or an implemented observable stopping algorithm.
-/
namespace DotG4.ActualSparseCertificateExistence
set_option backward.isDefEq.respectTransparency false
open Polynomial Module
open DotG4.ActualObservableBankCertificate
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

noncomputable def momentLevels (L : Nat) : Finset Nat :=
  Finset.univ.image (fun n : Fin L => n.val+1)

noncomputable def extendCoefficients {L : Nat} (c : Fin L → ℝ) (k : Nat) : ℝ :=
  if h : k-1 < L then c ⟨k-1,h⟩ else 0

lemma momentLevels_positive (L : Nat) : ∀ k ∈ momentLevels L, 0 < k := by
  intro k hk
  obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp hk
  omega

lemma sparsePolynomial_extend {L : Nat} (c : Fin L → ℝ) :
    sparsePolynomial (momentLevels L) (extendCoefficients c) =
      sparseCombination (fun n : Fin L => (n.val+1).choose 2) c := by
  unfold sparsePolynomial momentLevels
  rw [Finset.sum_image (by
    intro a _ b _ h
    exact Fin.ext (Nat.add_right_cancel h))]
  simp [extendCoefficients,sparseCombination,Fintype.linearCombination_apply,
    Polynomial.smul_monomial]

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture

variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- Semantic finite-stage existence for the ORIGINAL finite positive bank.
The hidden atom count is not supplied to an algorithm; it bounds a witness.
No algebraic representation, QE oracle or search termination is asserted. -/
theorem actual_exists_sparse_observable_certificate (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (i j : X) :
    ∃ (L : Nat) (c : Nat → ℝ), 0 < L ∧
      sparsePolynomial (momentLevels L) c ≠ 0 ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ (sparsePolynomial (momentLevels L) c).eval x) ∧
      (∑ k ∈ momentLevels L, c k * observedMoment N C H p r i j k = 0) := by
  let A : Finset ℝ := Finset.univ.image (realSurvival N C H p r i j)
  have hA : ∀ a ∈ A, 0 < a := by
    intro a ha
    obtain ⟨coin,_,rfl⟩ := Finset.mem_image.mp ha
    exact realSurvival_positive N C H p r i j coin
  let L := 2*A.card+1
  let e : Fin L → Nat := fun n => (n.val+1).choose 2
  have he : Function.Injective e := by
    intro a b hab
    apply Fin.ext
    exact momentExponent_strictMono.injective hab
  obtain ⟨v,hv,hpos,hzero⟩ := exists_nonnegative_sparse_polynomial A hA e he
  let c := extendCoefficients v
  have hp : sparsePolynomial (momentLevels L) c = sparseCombination e v :=
    sparsePolynomial_extend v
  refine ⟨L,c,by omega,?_,?_,?_⟩
  · rwa [hp]
  · intro x hx
    rw [hp]
    exact hpos x hx.1
  · have hz : ∀ coin, (sparsePolynomial (momentLevels L) c).eval
        (realSurvival N C H p r i j coin) = 0 := by
      intro coin
      rw [hp]
      exact hzero _ (Finset.mem_image.mpr ⟨coin,Finset.mem_univ coin,rfl⟩)
    calc
      _ = ∑ k ∈ momentLevels L, c k * (∑ coin, coinWeight N p coin *
          realSurvival N C H p r i j coin ^ k.choose 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [actual_observed_moment N C H p r i j k (momentLevels_positive L k hk)]
      _ = ∑ coin, coinWeight N p coin *
          (sparsePolynomial (momentLevels L) c).eval (realSurvival N C H p r i j coin) := by
        simp only [sparsePolynomial_eval,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro coin _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by simp only [hz,mul_zero,Finset.sum_const_zero]

/-- The same finite observed certificate restricts every rival that matches
its queried canonical moments. No bound on the rival's bank is required. -/
theorem actual_matching_moments_restrict_bank
    {V' E' : Type*} [DecidableEq V'] [DecidableEq E'] [Fintype V'] [Fintype E']
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (N' : RootedBinary V' E' X) (C' : Calendar N'.graph) (H' : OriginalParentRegistry N')
    (p' : HybridProbabilities N') (r' : PositivePairRates E') (i j : X)
    (L : Nat) (c : Nat → ℝ)
    (hne : sparsePolynomial (momentLevels L) c ≠ 0)
    (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ (sparsePolynomial (momentLevels L) c).eval x)
    (hzero : ∑ k ∈ momentLevels L, c k * observedMoment N C H p r i j k = 0)
    (hmatch : ∀ k ∈ momentLevels L,
      observedMoment N' C' H' p' r' i j k = observedMoment N C H p r i j k)
    (coin : Hybrid N' → Bool) :
    realSurvival N' C' H' p' r' i j coin ∈ (sparsePolynomial (momentLevels L) c).roots.toFinset := by
  apply actual_observable_certificate_roots N' C' H' p' r' i j (momentLevels L) c
    (momentLevels_positive L) hne hpos
  calc
    _ = ∑ k ∈ momentLevels L, c k * observedMoment N C H p r i j k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hmatch k hk]
    _ = 0 := hzero

#print axioms exists_nonnegative_sparse_polynomial
#print axioms actual_exists_sparse_observable_certificate
#print axioms actual_matching_moments_restrict_bank
end DotG4.ActualSparseCertificateExistence
