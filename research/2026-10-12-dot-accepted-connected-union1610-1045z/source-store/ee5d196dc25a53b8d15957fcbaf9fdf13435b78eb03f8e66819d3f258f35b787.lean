import G4ActualSparseCertificateExistence

/-!
# Sparse-moment uniqueness of the original-bank survival distribution

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED draft.
Formal composition of inherited ALL-CAP D2 finite-grid weight recovery.
Supplier audit b64f51c5538267b0565d1790509e3a26c467a4cd3291f3d7b4ae34bed09e2c33.
Weights are aggregated over all banks sharing a survival value. Rivals may
have different graphs and banks; absent grid points have zero weight.
No individual-bank or physical-graph identification is asserted.
-/
namespace DotG4.ActualPositiveGridUniqueness
set_option backward.isDefEq.respectTransparency false
open Polynomial Module
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open scoped Classical BigOperators Polynomial ENNReal

lemma zero_of_positive_grid_roots (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a)
    (P : ℝ[X]) (hs : P.support.card ≤ A.card)
    (hz : ∀ a ∈ A, P.IsRoot a) : P = 0 := by
  by_contra hp
  have hsub : A.val ≤ P.roots := by
    apply Multiset.le_iff_count.mpr
    intro a
    by_cases ha : a ∈ A
    · have hc : A.val.count a = 1 := Multiset.count_eq_one_of_mem A.nodup ha
      rw [hc]
      exact Nat.succ_le_iff.mpr (Multiset.count_pos.mpr ((Polynomial.mem_roots hp).mpr (hz a ha)))
    · have hc : A.val.count a = 0 := Multiset.count_eq_zero.mpr ha
      simp only [hc,Nat.zero_le]
  have hc : A.val.countP (0 < ·) = A.card := Multiset.countP_eq_card.mpr hA
  have hle := Multiset.countP_le_of_le (p := (0 < ·)) hsub
  have hd := P.roots_countP_pos_le_signVariations
  have hv := signVariations_lt_support_card P hp
  omega

noncomputable def gridEvaluation (A : Finset ℝ) (e : Fin A.card → Nat) :
    (Fin A.card → ℝ) →ₗ[ℝ] (A → ℝ) :=
  (LinearMap.pi (fun a : A => Polynomial.leval (a:ℝ))).comp (sparseCombination e)

lemma gridEvaluation_injective (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a)
    (e : Fin A.card → Nat) (he : Function.Injective e) :
    Function.Injective (gridEvaluation A e) := by
  intro c d hcd
  have hz : ∀ a ∈ A, (sparseCombination e (c-d)).IsRoot a := by
    intro a ha
    have h := congrFun hcd ⟨a,ha⟩
    change (sparseCombination e c).eval a = (sparseCombination e d).eval a at h
    simpa only [map_sub,Polynomial.IsRoot,Polynomial.eval_sub,sub_eq_zero] using h
  have hs : (sparseCombination e (c-d)).support.card ≤ A.card :=
    (Finset.card_le_card (sparseCombination_support e (c-d))).trans
      (Finset.card_image_le.trans (by simp))
  have hp := zero_of_positive_grid_roots A hA _ hs hz
  have hc : c-d = 0 := sparseCombination_injective e he (by simpa using hp)
  exact sub_eq_zero.mp hc

lemma gridEvaluation_surjective (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a)
    (e : Fin A.card → Nat) (he : Function.Injective e) :
    Function.Surjective (gridEvaluation A e) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℝ (Fin A.card → ℝ) = Module.finrank ℝ (A → ℝ) by simp)).mp
  exact gridEvaluation_injective A hA e he

/-- Signed differences are allowed: zero weights and repeated original-bank
values need no extra nondegeneracy assumption. -/
theorem positive_grid_weights_unique (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a)
    (e : Fin A.card → Nat) (he : Function.Injective e) (u v : A → ℝ)
    (hm : ∀ i, ∑ a, u a * (a:ℝ) ^ e i = ∑ a, v a * (a:ℝ) ^ e i) : u = v := by
  funext a0
  obtain ⟨c,hc⟩ := gridEvaluation_surjective A hA e he (fun a => if a = a0 then 1 else 0)
  have heval : ∀ a : A, (sparseCombination e c).eval (a:ℝ) = if a = a0 then 1 else 0 := by
    intro a
    exact congrFun hc a
  have hd : ∀ i, ∑ a, (u a-v a) * (a:ℝ) ^ e i = 0 := by
    intro i
    simp only [sub_mul,Finset.sum_sub_distrib,hm i,sub_self]
  have hz : ∑ a : A, (u a-v a) * (sparseCombination e c).eval (a:ℝ) = 0 := by
    calc
      _ = ∑ i, c i * (∑ a : A, (u a-v a) * (a:ℝ) ^ e i) := by
        simp only [sparseCombination,Fintype.linearCombination_apply,Polynomial.eval_finsetSum,
          Polynomial.eval_smul,Polynomial.eval_monomial,smul_eq_mul,mul_one,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = 0 := by simp only [hd,mul_zero,Finset.sum_const_zero]
  have : u a0-v a0 = 0 := by simpa [heval] using hz
  exact sub_eq_zero.mp this

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

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
variable {V E X V' E' : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V'] [DecidableEq E'] [Fintype V'] [Fintype E']

/-- Equality is of aggregated pushforward masses. Distinct original banks at
the same X are summed; unused rival grid points receive zero mass. -/
theorem actual_matching_grid_moments_survival_law
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (N' : RootedBinary V' E' X) (C' : Calendar N'.graph) (H' : OriginalParentRegistry N')
    (p' : HybridProbabilities N') (r' : PositivePairRates E') (i j : X)
    (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a)
    (ha : ∀ coin, realSurvival N C H p r i j coin ∈ A)
    (ha' : ∀ coin, realSurvival N' C' H' p' r' i j coin ∈ A)
    (hmatch : ∀ k ∈ momentLevels A.card,
      observedMoment N C H p r i j k = observedMoment N' C' H' p' r' i j k) :
    ((originalRegisterMeasure N p).toPMF.map (realSurvival N C H p r i j)) =
      ((originalRegisterMeasure N' p').toPMF.map (realSurvival N' C' H' p' r' i j)) := by
  let x := realSurvival N C H p r i j
  let x' := realSurvival N' C' H' p' r' i j
  let u : A → ℝ := fun a => gridWeight (coinWeight N p) x a
  let v : A → ℝ := fun a => gridWeight (coinWeight N' p') x' a
  let e : Fin A.card → Nat := fun n => (n.val+1).choose 2
  have he : Function.Injective e := by
    intro a b hab
    exact Fin.ext (momentExponent_strictMono.injective hab)
  have hm : ∀ n, ∑ a : A, u a * (a:ℝ)^e n = ∑ a : A, v a * (a:ℝ)^e n := by
    intro n
    change (∑ a : A, gridWeight (coinWeight N p) x a * (a:ℝ)^e n) =
      ∑ a : A, gridWeight (coinWeight N' p') x' a * (a:ℝ)^e n
    rw [gridWeight_moment A _ x ha,gridWeight_moment A _ x' ha']
    exact (actual_observed_moment N C H p r i j (n.val+1) (by omega)).symm.trans
      ((hmatch _ (Finset.mem_image.mpr ⟨n,Finset.mem_univ n,rfl⟩)).trans
        (actual_observed_moment N' C' H' p' r' i j (n.val+1) (by omega)))
  have huv := positive_grid_weights_unique A hA e he u v hm
  have hall : ∀ a : ℝ, gridWeight (coinWeight N p) x a = gridWeight (coinWeight N' p') x' a := by
    intro a
    by_cases h : a ∈ A
    · exact congrFun huv ⟨a,h⟩
    · rw [gridWeight_zero_outside A _ x ha a h,gridWeight_zero_outside A _ x' ha' a h]
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  exact (gridWeight_eq_mapped_mass (originalRegisterMeasure N p).toPMF x a).symm.trans
    ((hall a).trans (gridWeight_eq_mapped_mass (originalRegisterMeasure N' p').toPMF x' a))


lemma sparsePolynomial_support_card_le_levels (L : Nat) (c : Nat → ℝ) :
    (sparsePolynomial (momentLevels L) c).support.card ≤ L := by
  have hs : (sparsePolynomial (momentLevels L) c).support ⊆
      (momentLevels L).image (fun k => k.choose 2) := by
    intro n hn
    by_contra hnot
    have hne : ∀ k ∈ momentLevels L, k.choose 2 ≠ n := by
      intro k hk h
      exact hnot (Finset.mem_image.mpr ⟨k,hk,h⟩)
    have hz : (sparsePolynomial (momentLevels L) c).coeff n = 0 := by
      unfold sparsePolynomial
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro k hk
      simp [Polynomial.coeff_monomial,hne k hk]
    exact (Polynomial.mem_support_iff.mp hn) hz
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans
    ((Finset.card_image_le (s := (Finset.univ : Finset (Fin L)))).trans (by simp)))

noncomputable def positiveCertificateGrid (L : Nat) (c : Nat → ℝ) : Finset ℝ :=
  (sparsePolynomial (momentLevels L) c).roots.toFinset.filter (fun x => 0 < x ∧ x ≤ 1)

lemma positiveCertificateGrid_card_lt (L : Nat) (c : Nat → ℝ)
    (hp : sparsePolynomial (momentLevels L) c ≠ 0) :
    (positiveCertificateGrid L c).card < L := by
  let A := positiveCertificateGrid L c
  have hA : ∀ a ∈ A, 0 < a := fun a ha => (Finset.mem_filter.mp ha).2.1
  have hz : ∀ a ∈ A, (sparsePolynomial (momentLevels L) c).IsRoot a := by
    intro a ha
    exact (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp (Finset.mem_filter.mp ha).1)
  have hlt : A.card < (sparsePolynomial (momentLevels L) c).support.card := by
    by_contra h
    exact hp (zero_of_positive_grid_roots A hA _ (Nat.le_of_not_gt h) hz)
  exact hlt.trans_le (sparsePolynomial_support_card_le_levels L c)

/-- A nonzero observed certificate already leaves fewer positive grid atoms
than queried levels. The same finite queries therefore determine the entire
survival pushforward distribution among arbitrary admitted finite rivals. -/
theorem actual_certificate_matching_moments_survival_law
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (N' : RootedBinary V' E' X) (C' : Calendar N'.graph) (H' : OriginalParentRegistry N')
    (p' : HybridProbabilities N') (r' : PositivePairRates E') (i j : X)
    (L : Nat) (c : Nat → ℝ)
    (hne : sparsePolynomial (momentLevels L) c ≠ 0)
    (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ (sparsePolynomial (momentLevels L) c).eval x)
    (hzero : ∑ k ∈ momentLevels L, c k * observedMoment N C H p r i j k = 0)
    (hmatch : ∀ k ∈ momentLevels L,
      observedMoment N C H p r i j k = observedMoment N' C' H' p' r' i j k) :
    ((originalRegisterMeasure N p).toPMF.map (realSurvival N C H p r i j)) =
      ((originalRegisterMeasure N' p').toPMF.map (realSurvival N' C' H' p' r' i j)) := by
  let A := positiveCertificateGrid L c
  have hA : ∀ a ∈ A, 0 < a := fun a ha => (Finset.mem_filter.mp ha).2.1
  have ha : ∀ coin, realSurvival N C H p r i j coin ∈ A := by
    intro coin
    exact Finset.mem_filter.mpr ⟨actual_observable_certificate_roots N C H p r i j
      (momentLevels L) c (momentLevels_positive L) hne hpos hzero coin,
      realSurvival_positive N C H p r i j coin,realSurvival_le_one N C H p r i j coin⟩
  have ha' : ∀ coin, realSurvival N' C' H' p' r' i j coin ∈ A := by
    intro coin
    exact Finset.mem_filter.mpr ⟨actual_matching_moments_restrict_bank N C H p r
      N' C' H' p' r' i j L c hne hpos hzero (fun k hk => (hmatch k hk).symm) coin,
      realSurvival_positive N' C' H' p' r' i j coin,realSurvival_le_one N' C' H' p' r' i j coin⟩
  apply actual_matching_grid_moments_survival_law N C H p r N' C' H' p' r' i j A hA ha ha'
  intro k hk
  obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp hk
  apply hmatch
  exact Finset.mem_image.mpr ⟨⟨n.val,n.isLt.trans (positiveCertificateGrid_card_lt L c hne)⟩,
    Finset.mem_univ _,rfl⟩

/-- Semantic finite determination of one directed survival distribution.
This existential query bound is not an executable stopping algorithm. -/
theorem actual_exists_finite_survival_law_determination
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (i j : X) :
    ∃ L : Nat, 0 < L ∧ ∀ (V' E' : Type*) [DecidableEq V'] [DecidableEq E']
      [Fintype V'] [Fintype E'] (N' : RootedBinary V' E' X) (C' : Calendar N'.graph)
      (H' : OriginalParentRegistry N') (p' : HybridProbabilities N') (r' : PositivePairRates E'),
      (∀ k ∈ momentLevels L, observedMoment N C H p r i j k =
        observedMoment N' C' H' p' r' i j k) →
      ((originalRegisterMeasure N p).toPMF.map (realSurvival N C H p r i j)) =
        ((originalRegisterMeasure N' p').toPMF.map (realSurvival N' C' H' p' r' i j)) := by
  obtain ⟨L,c,hL,hne,hpos,hzero⟩ := actual_exists_sparse_observable_certificate N C H p r i j
  refine ⟨L,hL,?_⟩
  intro V' E' _ _ _ _ N' C' H' p' r' hmatch
  exact actual_certificate_matching_moments_survival_law N C H p r N' C' H' p' r' i j
    L c hne hpos hzero hmatch

#print axioms positive_grid_weights_unique
#print axioms actual_matching_grid_moments_survival_law
#print axioms actual_exists_finite_survival_law_determination
end DotG4.ActualPositiveGridUniqueness
