import G7NodeActions
import G7BoundaryExitCommutation
import G7SinglePopulationPolynomialKernel
import UnifiedLean.Source.SourceEpochSemigroup
import Mathlib.Probability.Distributions.Uniform

/-!
Internal implementation of the complete original-edge gathering development.
The local operators act on the literal inherited source state, including every
nonbridge and parallel edge occurrence. No commuting-kernel field is supplied.
Contributor: dot, 2026-10-10; formalization of the attributed prior G7 frontier
argument. This candidate is not yet compiled and is not the gathering endpoint.
-/
namespace GProgram.G7.OriginalEdgeOperators
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourceBoundaryKernels
open GProgram.G7.NodeActions GProgram.G7.SinglePopulationPolynomialKernel
open Matrix NormedSpace
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- A fixed original-copy pair is executable precisely at its current actual
population. Invalid trials hold; no new biological event is inserted. -/
def PairAt (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) : Prop :=
  p ∈ (populationRoots (state s) (originalPlace N i)).offDiag

lemma pairAt_iff (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) :
    PairAt N i p s ↔
      p.1 ∈ (state s).live ∧ (state s).location p.1 = originalPlace N i ∧
      p.2 ∈ (state s).live ∧ (state s).location p.2 = originalPlace N i ∧ p.1 ≠ p.2 := by
  simp only [PairAt,Finset.mem_offDiag,populationRoots,Finset.mem_filter]
  tauto

noncomputable def mergeAt (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) : Code N sample :=
  if hp : PairAt N i p s then stepDestination N s (some ⟨i,⟨p,hp⟩⟩) else s

lemma mergeAt_of_mem (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) (hp : PairAt N i p s) :
    mergeAt N i p s = stepDestination N s (some ⟨i,⟨p,hp⟩⟩) := by
  simp [mergeAt,hp]

lemma mergeAt_of_not_mem (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) (hp : ¬ PairAt N i p s) :
    mergeAt N i p s = s := by simp [mergeAt,hp]

lemma merged_live (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) (hp : PairAt N i p s) :
    (state (mergeAt N i p s)).live = (state s).live.erase p.2 := by
  rw [mergeAt_of_mem N i p s hp]
  rfl

lemma merged_ancestor (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) (hp : PairAt N i p s) (x : Copy) :
    (state (mergeAt N i p s)).ancestor x =
      if (state s).ancestor x = p.2 then p.1 else (state s).ancestor x := by
  rw [mergeAt_of_mem N i p s hp]
  rfl

lemma merged_genealogy (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) (hp : PairAt N i p s) (x : Copy) :
    (state (mergeAt N i p s)).genealogy x =
      if x ∈ (state s).live.erase p.2 then
        if x = p.1 then .graft ((state s).genealogy p.1) ((state s).genealogy p.2)
        else (state s).genealogy x
      else .leaf x := by
  rw [mergeAt_of_mem N i p s hp]
  simp [state,stepDestination,admittedCode,encodeSnapshot,decodeSnapshot,merge]

lemma merged_location (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) (hp : PairAt N i p s) (x : Copy) :
    (state (mergeAt N i p s)).location x =
      if x ∈ (state s).live.erase p.2 then (state s).location x else .node N.root := by
  rw [mergeAt_of_mem N i p s hp]
  simp [state,stepDestination,admittedCode,encodeSnapshot,decodeSnapshot,merge]

lemma merged_register (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) :
    (state (mergeAt N i p s)).register = (state s).register := by
  unfold mergeAt
  split <;> rfl

lemma merged_canonical (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (s : Code N sample) (hp : PairAt N i p s) :
    Canonical (mergeAt N i p s) := by
  rw [mergeAt_of_mem N i p s hp]
  exact admitted_canonical N sample _ _

/-- An actual merger at i cannot create or destroy a legal pair at j != i.
This derives disjoint live-owner action from source locations, not graph
bridge ownership, nor an assumption that the current copy cohorts are fixed. -/
theorem other_pair_preserved (N : RootedBinary V E X) {sample : Copy → X}
    (i j : Option E) (hij : i ≠ j) (p q : Copy × Copy) (s : Code N sample) :
    PairAt N j q (mergeAt N i p s) ↔ PairAt N j q s := by
  by_cases hp : PairAt N i p s
  · have pp := (pairAt_iff N i p s).mp hp
    rw [pairAt_iff,pairAt_iff,merged_live N i p s hp,
      merged_location N i p s hp,merged_location N i p s hp]
    constructor
    · rintro ⟨ha,hla,hb,hlb,hab⟩
      exact ⟨(Finset.mem_erase.mp ha).2,by simpa [ha] using hla,
        (Finset.mem_erase.mp hb).2,by simpa [hb] using hlb,hab⟩
    · rintro ⟨ha,hla,hb,hlb,hab⟩
      have hqa : q.1 ≠ p.2 := by
        intro he
        have hh : originalPlace N i = originalPlace N j := pp.2.2.2.1.symm.trans (he ▸ hla)
        exact hij (originalPlace_injective N hh)
      have hqb : q.2 ≠ p.2 := by
        intro he
        have hh : originalPlace N i = originalPlace N j := pp.2.2.2.1.symm.trans (he ▸ hlb)
        exact hij (originalPlace_injective N hh)
      have ha' := Finset.mem_erase.mpr ⟨hqa,ha⟩
      have hb' := Finset.mem_erase.mpr ⟨hqb,hb⟩
      exact ⟨ha',by simpa [ha'] using hla,hb',by simpa [hb'] using hlb,hab⟩
  · rw [mergeAt_of_not_mem N i p s hp]

lemma different_population_roots (N : RootedBinary V E X) {sample : Copy → X}
    (i j : Option E) (hij : i ≠ j) (s : Code N sample) {a b : Copy}
    (ha : (state s).location a = originalPlace N i)
    (hb : (state s).location b = originalPlace N j) : a ≠ b := by
  intro h
  subst b
  exact hij (originalPlace_injective N (ha.symm.trans hb))

/-- Literal admitted-source merger trials at distinct original populations
commute, including nonbridge and parallel edge occurrences. -/
theorem mergeAt_commute (N : RootedBinary V E X) {sample : Copy → X}
    (i j : Option E) (hij : i ≠ j) (p q : Copy × Copy) (s : Code N sample) :
    mergeAt N j q (mergeAt N i p s) = mergeAt N i p (mergeAt N j q s) := by
  by_cases hp : PairAt N i p s
  · by_cases hq : PairAt N j q s
    · have hp' : PairAt N i p (mergeAt N j q s) :=
        (other_pair_preserved N j i hij.symm q p s).mpr hp
      have hq' : PairAt N j q (mergeAt N i p s) :=
        (other_pair_preserved N i j hij p q s).mpr hq
      have pp := (pairAt_iff N i p s).mp hp
      have qq := (pairAt_iff N j q s).mp hq
      have hac := different_population_roots N i j hij s pp.2.1 qq.2.1
      have had := different_population_roots N i j hij s pp.2.1 qq.2.2.2.1
      have hbc := different_population_roots N i j hij s pp.2.2.2.1 qq.2.1
      have hbd := different_population_roots N i j hij s pp.2.2.2.1 qq.2.2.2.1
      apply canonical_ext _ _ (merged_canonical N j q _ hq') (merged_canonical N i p _ hp')
      apply state_ext
      · simp only [merged_live N j q _ hq',merged_live N i p _ hp',
          merged_live N i p s hp,merged_live N j q s hq]
        exact Finset.erase_comm _ _ _
      · funext x
        simp only [merged_ancestor N j q _ hq',merged_ancestor N i p _ hp',
          merged_ancestor N i p s hp,merged_ancestor N j q s hq]
        split_ifs <;> simp_all
      · funext x
        simp only [merged_genealogy N j q _ hq',merged_genealogy N i p _ hp',
          merged_genealogy N i p s hp,merged_genealogy N j q s hq,
          merged_live N i p s hp,merged_live N j q s hq]
        by_cases hxa : x = p.1
        · subst x
          simp [pp.1,pp.2.2.1,qq.1,qq.2.2.1,pp.2.2.2.2,qq.2.2.2.2,
            hac,had,hbc,hbd,Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd]
        · by_cases hxc : x = q.1
          · subst x
            simp [pp.1,pp.2.2.1,qq.1,qq.2.2.1,pp.2.2.2.2,qq.2.2.2.2,
              hac,had,hbc,hbd,Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd]
          · simp [hxa,hxc,Finset.mem_erase,and_left_comm,and_comm,and_assoc]
      · funext x
        simp only [merged_location N j q _ hq',merged_location N i p _ hp',
          merged_location N i p s hp,merged_location N j q s hq,
          merged_live N i p s hp,merged_live N j q s hq]
        simp [Finset.mem_erase,and_left_comm,and_comm,and_assoc]
      · simp only [merged_register]
      · rfl
    · have hq' : ¬ PairAt N j q (mergeAt N i p s) :=
        fun h => hq ((other_pair_preserved N i j hij p q s).mp h)
      rw [mergeAt_of_not_mem N j q _ hq',mergeAt_of_not_mem N j q s hq]
  · have hp' : ¬ PairAt N i p (mergeAt N j q s) :=
      fun h => hp ((other_pair_preserved N j i hij.symm q p s).mp h)
    rw [mergeAt_of_not_mem N i p s hp,mergeAt_of_not_mem N i p _ hp']

/-- A deterministic actual trial as a row-stochastic matrix. -/
noncomputable def pairMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) : Matrix (Code N sample) (Code N sample) ℝ :=
  fun s d => if mergeAt N i p s = d then 1 else 0

/-- Half the sum of ordered pair increments. Illegal pairs contribute zero,
so this is exactly the original unit pair-rate population generator. -/
noncomputable def populationGenerator (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) : Matrix (Code N sample) (Code N sample) ℝ :=
  (1/2:ℝ) • ∑ p : Copy × Copy, (pairMatrix N i p - 1)

lemma pairMatrix_mul (N : RootedBinary V E X) {sample : Copy → X}
    (i j : Option E) (p q : Copy × Copy) (s d : Code N sample) :
    (pairMatrix N i p * pairMatrix N j q) s d =
      if mergeAt N j q (mergeAt N i p s) = d then 1 else 0 := by
  simp [Matrix.mul_apply,pairMatrix]

theorem population_generators_commute (N : RootedBinary V E X) {sample : Copy → X}
    (i j : Option E) :
    Commute (populationGenerator N (sample := sample) i) (populationGenerator N j) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · have hpair (p q : Copy × Copy) :
        Commute (pairMatrix N (sample := sample) i p - 1) (pairMatrix N j q - 1) := by
      have h : Commute (pairMatrix N (sample := sample) i p) (pairMatrix N j q) := by
        apply Matrix.ext
        intro s d
        rw [pairMatrix_mul,pairMatrix_mul,mergeAt_commute N i j hij p q s]
      exact (h.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)
    unfold populationGenerator
    exact ((Commute.sum_left _ _ _ fun p _ =>
      Commute.sum_right _ _ _ fun q _ => hpair p q).smul_left (1/2:ℝ)).smul_right (1/2:ℝ)

open UnifiedLean.Source.SourceStepGeneratorBinding

lemma populationGenerator_apply (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (s d : Code N sample) :
    populationGenerator N i s d = (1/2:ℝ) *
      ∑ p : {p : Copy × Copy // PairAt N i p s},
        ((if stepDestination N s (some ⟨i,⟨p.val,p.property⟩⟩) = d then 1 else 0) -
          if s = d then 1 else 0) := by
  let f : Copy × Copy → ℝ := fun p =>
    (if mergeAt N i p s = d then 1 else 0) - if s = d then 1 else 0
  have hs := Fintype.sum_subtype_add_sum_subtype (PairAt N i · s) f
  have hz : (∑ p : {p : Copy × Copy // ¬ PairAt N i p s}, f p.val) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    simp [f,mergeAt_of_not_mem N i p.val s p.property]
  rw [hz,add_zero] at hs
  unfold populationGenerator
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,Matrix.sub_apply,
    Matrix.one_apply,pairMatrix]
  change (1/2:ℝ) * (∑ p : Copy × Copy, f p) = _
  rw [←hs]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  simp only [f,mergeAt_of_mem N i p.val s p.property]

/-- The old source generator is bound entry by entry to its literal merger
choices before introducing any all-edge operator factorization. -/
lemma actual_generator_choice_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) :
    sourceGeneratorMatrix N r s d =
      ∑ p : Choice N s, choiceRate N r s p *
        ((if stepDestination N s (some p) = d then 1 else 0) -
          if s = d then 1 else 0) := by
  have ht := sourceStep_expectation N r s (fun z => if z = d then 1 else 0)
  have hl : (∑ z : Code N sample, (sourceStep N r s z).toReal *
      (if z = d then 1 else 0)) = (sourceStep N r s d).toReal := by simp
  rw [hl,Fintype.sum_option] at ht
  change (sourceStep N r s d).toReal =
    (1-totalRate N r s/globalRateBound (Copy:=Copy) r) * (if s=d then 1 else 0) +
      ∑ p : Choice N s, choiceRate N r s p/globalRateBound (Copy:=Copy) r *
        (if stepDestination N s (some p) = d then 1 else 0) at ht
  have hm : (∑ p : Choice N s, choiceRate N r s p/globalRateBound (Copy:=Copy) r *
      (if stepDestination N s (some p) = d then 1 else 0)) =
      (∑ p : Choice N s, choiceRate N r s p *
        (if stepDestination N s (some p) = d then 1 else 0)) /
          globalRateBound (Copy:=Copy) r := by
    simp only [div_mul_eq_mul_div,Finset.sum_div]
  rw [hm] at ht
  simp only [sourceGeneratorMatrix,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,
    sourceTransition,Matrix.one_apply,ht]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,←Finset.sum_mul]
  change _ = _ - totalRate N r s * (if s=d then 1 else 0)
  have hne : globalRateBound (Copy:=Copy) r ≠ 0 :=
    ne_of_gt (globalRateBound_positive (Copy:=Copy) r)
  field_simp [hne]
  <;> ring

/-- Every original edge/root population occurs in the source generator. The
coefficient is its original physical pair rate; nonbridge edges are included. -/
theorem actual_generator_all_populations (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) :
    sourceGeneratorMatrix N (sample:=sample) r =
      ∑ i : Option E, pairRate r i • populationGenerator N i := by
  ext s d
  rw [actual_generator_choice_row,Fintype.sum_sigma]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [populationGenerator_apply]
  simp only [choiceRate]
  rw [←Finset.mul_sum]
  ring

/-- Literal all-population exponential factors. This is a matrix built from
actual merger trials, not a probability table supplied by the caller. -/
noncomputable def populationExponential (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (a : ℝ) : Matrix (Code N sample) (Code N sample) ℝ :=
  exp (a • populationGenerator N i)

/-- The complete actual epoch generator is a sum of mutually commuting
original-population generators. This is the required nonbridge-aware source
binding for gathering each population's clock separately. -/
theorem actual_source_epoch_exponential_sum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample) :
    (sourceTimeKernel N r t s d).toReal =
      (exp (∑ i : Option E, ((t:ℝ)*pairRate r i) • populationGenerator N i)) s d := by
  rw [source_time_kernel_eq_exponential,actual_generator_all_populations,
    Finset.smul_sum]
  simp only [smul_smul]

lemma populationExponential_add (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (a b : ℝ) :
    populationExponential N (sample:=sample) i (a+b) =
      populationExponential N i a * populationExponential N i b := by
  unfold populationExponential
  rw [add_smul,exp_add_of_commute
    (((Commute.refl (populationGenerator N (sample:=sample) i)).smul_left a).smul_right b)]

end GProgram.G7.OriginalEdgeOperators
