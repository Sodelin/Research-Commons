import G6CellCompletedBinPolynomial
import ActualPolynomialEpochModulus
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
Standard coefficient-weighted unit-cube Lipschitz inequality, consumed by the
full actual source-to-completed-forest/bin table. The table already contains
G7's source-derived multi-population product and the correlated original bank.
This is an explicit rational constant GIVEN that table, not an executable
extraction of the table or a uniform unknown-graph bound.
Contributor: dot / OpenAI, 10 October 2026. Uncompiled candidate.
-/
namespace UnifiedLean.G6.ActualCellObservedTV
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G7.SymbolicProgramPolynomial
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.ActualKernelCoefficientBound
open UnifiedLean.G6.OriginalCalendarSchema UnifiedLean.G6.StableFiniteCutSchema
open UnifiedLean.G6.ActualCompleteCutPattern UnifiedLean.G6.GeneratedNaturalChronology
open UnifiedLean.G6.CellCompletedBinPolynomial UnifiedLean.G6.FiniteCutSourceWord
open CloudG6.NaturalPastCompleteObservation
open scoped Classical BigOperators NNReal

/-- Elementary telescoping product estimate on [0,1]. -/
lemma unit_product_difference {I : Type*} (s : Finset I) (x y : I → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1)
    (hy : ∀ i ∈ s, 0 ≤ y i ∧ y i ≤ 1) :
    |(∏ i ∈ s, x i) - ∏ i ∈ s, y i| ≤ ∑ i ∈ s, |x i-y i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hx0 := (hx i (Finset.mem_insert_self _ _)).1
      have hx1 := (hx i (Finset.mem_insert_self _ _)).2
      have hys0 : 0 ≤ ∏ j ∈ s, y j :=
        Finset.prod_nonneg (fun j hj => (hy j (Finset.mem_insert_of_mem hj)).1)
      have hys1 : (∏ j ∈ s, y j) ≤ 1 :=
        Finset.prod_le_one (fun j hj => (hy j (Finset.mem_insert_of_mem hj)).1)
          (fun j hj => (hy j (Finset.mem_insert_of_mem hj)).2)
      have ht := ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
        (fun j hj => hy j (Finset.mem_insert_of_mem hj))
      rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.sum_insert hi]
      have he : x i * (∏ j ∈ s, x j) - y i * (∏ j ∈ s, y j) =
          x i * ((∏ j ∈ s, x j) - ∏ j ∈ s, y j) +
          (x i-y i)*(∏ j ∈ s, y j) := by ring
      rw [he]
      calc
        _ ≤ |x i * ((∏ j ∈ s, x j) - ∏ j ∈ s, y j)| +
            |(x i-y i)*(∏ j ∈ s, y j)| := abs_add_le _ _
        _ = x i * |(∏ j ∈ s, x j) - ∏ j ∈ s, y j| +
            |x i-y i| *(∏ j ∈ s, y j) := by
              rw [abs_mul,abs_mul,abs_of_nonneg hx0,abs_of_nonneg hys0]
        _ ≤ |(∏ j ∈ s, x j) - ∏ j ∈ s, y j| + |x i-y i| := by
          have hl := mul_le_mul_of_nonneg_right hx1 (abs_nonneg ((∏ j ∈ s, x j) - ∏ j ∈ s, y j))
          have hr := mul_le_mul_of_nonneg_left hys1 (abs_nonneg (x i-y i))
          simpa only [one_mul,mul_one] using add_le_add hl hr
        _ ≤ (∑ j ∈ s, |x j-y j|) + |x i-y i| := add_le_add ht (le_refl _)
        _ = _ := add_comm _ _

lemma unit_monomial_difference {I : Type*} [Fintype I]
    (d : I →₀ ℕ) (x y : I → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (epsilon : ℝ) (he : ∀ i, |x i-y i| ≤ epsilon) :
    |(∏ i, x i ^ d i) - ∏ i, y i ^ d i| ≤ (∑ i, (d i : ℝ)) * epsilon := by
  have hprod := unit_product_difference Finset.univ (fun i => x i ^ d i) (fun i => y i ^ d i)
    (fun i _ => ⟨pow_nonneg (hx i).1 _,pow_le_one₀ (hx i).1 (hx i).2⟩)
    (fun i _ => ⟨pow_nonneg (hy i).1 _,pow_le_one₀ (hy i).1 (hy i).2⟩)
  calc
    _ ≤ ∑ i, |x i ^ d i-y i ^ d i| := hprod
    _ ≤ ∑ i, (d i : ℝ)*epsilon := by
      apply Finset.sum_le_sum
      intro i _
      exact (unit_power_lipschitz (x i) (y i) (hx i).1 (hx i).2 (hy i).1 (hy i).2 (d i)).trans
        (mul_le_mul_of_nonneg_left (he i) (Nat.cast_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Explicit rational coefficient mass weighted by monomial total degree.
Unused variables have exponent zero, so the finite slot convention is harmless. -/
noncomputable def coefficientSlope {I : Type*} [Fintype I]
    (P : MvPolynomial I ℚ) : ℚ :=
  ∑ d ∈ P.support, |P.coeff d| * (∑ i : I, (d i : ℚ))

lemma coefficientSlope_nonneg {I : Type*} [Fintype I] (P : MvPolynomial I ℚ) :
    0 ≤ coefficientSlope P := by
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))

/-- Standard multivariate polynomial Lipschitz bound on the unit cube. The
unit-power estimate is reused from the accepted actual source-epoch modulus. -/
theorem polynomial_cube_lipschitz {I : Type*} [Fintype I]
    (P : MvPolynomial I ℚ) (x y : I → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (epsilon : ℝ) (he : ∀ i, |x i-y i| ≤ epsilon) :
    |MvPolynomial.eval₂ (Rat.castHom ℝ) x P - MvPolynomial.eval₂ (Rat.castHom ℝ) y P| ≤
      (coefficientSlope P : ℝ) * epsilon := by
  rw [MvPolynomial.eval₂_eq',MvPolynomial.eval₂_eq',←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ P.support,
        |(Rat.castHom ℝ) (P.coeff d) * (∏ i, x i ^ d i) -
          (Rat.castHom ℝ) (P.coeff d) * (∏ i, y i ^ d i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.support, |((P.coeff d : ℚ) : ℝ)| * (∑ i, (d i : ℝ)) * epsilon := by
      apply Finset.sum_le_sum
      intro d _
      rw [←mul_sub,abs_mul]
      exact (mul_le_mul_of_nonneg_left (unit_monomial_difference d x y hx hy epsilon he)
        (abs_nonneg ((P.coeff d : ℚ) : ℝ))).trans_eq (by ring)
    _ = _ := by
      simp only [coefficientSlope,Rat.cast_sum,Rat.cast_mul,Rat.cast_abs,Rat.cast_natCast,
        Finset.sum_mul]

/-- Our TV is half the full L1 distance, so the table constant includes 1/2. -/
noncomputable def tableTVSlope {I O : Type*} [Fintype I] [Fintype O]
    (Q : O → MvPolynomial I ℚ) : ℚ := (∑ o, coefficientSlope (Q o)) / 2

lemma tableTVSlope_nonneg {I O : Type*} [Fintype I] [Fintype O]
    (Q : O → MvPolynomial I ℚ) : 0 ≤ tableTVSlope Q :=
  div_nonneg (Finset.sum_nonneg (fun o _ => coefficientSlope_nonneg (Q o))) (by norm_num)

theorem polynomial_law_tv {I O : Type*} [Fintype I] [Fintype O]
    (Q : O → MvPolynomial I ℚ) (p q : PMF O) (x y : I → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hp : ∀ o, MvPolynomial.eval₂ (Rat.castHom ℝ) x (Q o) = (p o).toReal)
    (hq : ∀ o, MvPolynomial.eval₂ (Rat.castHom ℝ) y (Q o) = (q o).toReal)
    (epsilon : ℝ) (he : ∀ i, |x i-y i| ≤ epsilon) :
    pmfTV p q ≤ (tableTVSlope Q : ℝ) * epsilon := by
  have hsum := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) =>
    polynomial_cube_lipschitz (Q o) x y hx hy epsilon he)
  simp_rw [hp,hq] at hsum
  unfold pmfTV tv
  calc
    _ ≤ (∑ o, (coefficientSlope (Q o) : ℝ)*epsilon) / 2 :=
      div_le_div_of_nonneg_right hsum (by norm_num)
    _ = _ := by
      simp only [tableTVSlope,Rat.cast_div,Rat.cast_sum,Rat.cast_ofNat]
      rw [← Finset.sum_mul]
      ring

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]

lemma actual_word_variables_unit {J : Type*} (N : RootedBinary V E X)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0) :
    ∀ z, 0 ≤ wordVariables N r gamma dur z ∧ wordVariables N r gamma dur z ≤ 1 := by
  intro z
  cases z with
  | inl a =>
      rcases a with ⟨j,i⟩
      exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr
        (by nlinarith [pairRate_pos r i,(dur j).coe_nonneg])⟩
  | inr h => exact (gamma h).property

/-- Sum of differences of the ACTUAL physical coordinates. All occurrences
inside each bank use its same positive rates and same original hybrid gamma. -/
noncomputable def physicalBankDistance {J : Type*} [Fintype J] (N : RootedBinary V E X)
    (r r' : PositivePairRates E) (p p' : HybridProbabilities N)
    (dur dur' : J → ℝ≥0) : ℝ :=
  ∑ z : WordVariable N J,
    |wordVariables N r (originalGamma p) dur z - wordVariables N r' (originalGamma p') dur' z|

/-- Full shared-bank, multi-population, naturally initialized completed
observed-law bound throughout one full original date/cut cell. No independence
of physical variables or hidden coordinates is an admission hypothesis. The
same finite observed alphabet and reader are fixed throughout the comparison. -/
theorem actual_cell_completed_observed_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j)) (sig : Signature V (j+1))
    (hc : Realizes (completedCutBank cuts ks) sig C.age)
    (readout : (Finset (UnrankedTree Copy) ×
      (Copy → Copy → Fin ((values cuts ks).length+1))) → O) :
    ∃ (w : List (Step V E × Fin ((values cuts ks).length+1))) (K : ℚ), 0 ≤ K ∧
      ∀ (D D' : Calendar N.graph),
      Realizes (completedCutBank cuts ks) sig D.age →
      Realizes (completedCutBank cuts ks) sig D'.age →
      ∀ (p p' : HybridProbabilities N) (r r' : PositivePairRates E),
        pmfTV
          ((naturalCompletedJoint N D sample p r (rankBin (values cuts ks))
            (rank_bin_measurable (values cuts ks))
            (compiledCalendarProgram N D H (originalGamma p) common)).map
              (fun q => readout (sourceUnrankedForest (state q.1) Finset.univ,q.2)))
          ((naturalCompletedJoint N D' sample p' r' (rankBin (values cuts ks))
            (rank_bin_measurable (values cuts ks))
            (compiledCalendarProgram N D' H (originalGamma p') common)).map
              (fun q => readout (sourceUnrankedForest (state q.1) Finset.univ,q.2))) ≤
        (K : ℝ) * physicalBankDistance N r r' p p' (taggedDuration N D w) (taggedDuration N D' w) := by
  obtain ⟨w,Q,hQ⟩ := actual_cell_observed_bin_polynomial N C sample H common cuts ks sig hc readout
  refine ⟨w,tableTVSlope Q,tableTVSlope_nonneg Q,?_⟩
  intro D D' hd hd' p p' r r'
  apply polynomial_law_tv Q _ _
    (wordVariables N r (originalGamma p) (taggedDuration N D w))
    (wordVariables N r' (originalGamma p') (taggedDuration N D' w))
    (actual_word_variables_unit N r (originalGamma p) _)
    (actual_word_variables_unit N r' (originalGamma p') _)
    (hQ D hd p r) (hQ D' hd' p' r')
  intro z
  unfold physicalBankDistance
  exact Finset.single_le_sum (fun i _ => abs_nonneg
    (wordVariables N r (originalGamma p) (taggedDuration N D w) i -
      wordVariables N r' (originalGamma p') (taggedDuration N D' w) i)) (Finset.mem_univ z)

#print axioms polynomial_cube_lipschitz
#print axioms polynomial_law_tv
#print axioms actual_cell_completed_observed_tv
end UnifiedLean.G6.ActualCellObservedTV
