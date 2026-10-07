import UnifiedLean.G6.Conditioning
import UnifiedLean.Source.SourcePoissonExponential

/-!
Actual source Poisson-prefix approximation, derived from the existing
countPMF.bind sourceIteration. Uses PMF.filter's verified normalization.
No rational evaluation algorithm, Taylor tail certificate, positive biological
replacement or timed-bin observation compiler is supplied by conditioning.
The residual-lumped Python backend has a different count law.
-/
namespace UnifiedLean.G6.SourcePrefix
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.G6.Conditioning UnifiedLean.G6.FiniteProbability
open scoped Classical BigOperators NNReal

noncomputable def taylorTerm (a : ℝ) (k : ℕ) : ℝ := a ^ k / k.factorial
noncomputable def taylorPrefix (a : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), taylorTerm a k

lemma count_zero_ne_zero (a : ℝ≥0) : countPMF a 0 ≠ 0 := by
  intro h
  have hc := countPMF_real a 0
  have he : Real.exp (-(a : ℝ)) = 0 := by simpa [h] using hc.symm
  exact (ne_of_gt (Real.exp_pos _)) he

lemma prefix_has_support (a : ℝ≥0) (K : ℕ) :
    ∃ k ∈ (Finset.range (K + 1) : Set ℕ), k ∈ (countPMF a).support :=
  ⟨0, Finset.mem_range.mpr (Nat.succ_pos K), count_zero_ne_zero a⟩

noncomputable def prefixCount (a : ℝ≥0) (K : ℕ) : PMF ℕ :=
  (countPMF a).filter (Finset.range (K + 1) : Set ℕ) (prefix_has_support a K)

noncomputable def prefixMass (a : ℝ≥0) (K : ℕ) : ℝ :=
  (retainedMass (countPMF a) (Finset.range (K + 1) : Set ℕ)).toReal

lemma prefixCount_support (a : ℝ≥0) (K : ℕ) :
    (prefixCount a K).support ⊆ (Finset.range (K + 1) : Set ℕ) := by
  intro k hk
  exact (PMF.mem_support_filter_iff (prefix_has_support a K)).mp hk |>.1

lemma prefixMass_bounds (a : ℝ≥0) (K : ℕ) : 0 < prefixMass a K ∧ prefixMass a K ≤ 1 := by
  constructor
  · exact ENNReal.toReal_pos (retainedMass_ne_zero _ _ (prefix_has_support a K))
      (retainedMass_ne_top _ _)
  · exact (retainedMass_real_bounds _ _).2

lemma prefixMass_taylor (a : ℝ≥0) (K : ℕ) :
    prefixMass a K = Real.exp (-(a : ℝ)) * taylorPrefix (a : ℝ) K := by
  unfold prefixMass
  rw [retainedMass_finset, ENNReal.toReal_sum (fun k _ => (countPMF a).apply_ne_top k)]
  simp_rw [countPMF_real, mul_div_assoc]
  rw [← Finset.mul_sum]
  rfl

lemma taylorPrefix_pos (a : ℝ≥0) (K : ℕ) : 0 < taylorPrefix (a : ℝ) K := by
  have h := (prefixMass_bounds a K).1
  rw [prefixMass_taylor] at h
  exact (mul_pos_iff.mp h).resolve_right (by
    intro hn
    exact (not_lt_of_ge (Real.exp_pos _).le) hn.1)
    |>.2

lemma prefixCount_real (a : ℝ≥0) (K k : ℕ) :
    (prefixCount a K k).toReal =
      if k ≤ K then taylorTerm (a : ℝ) k / taylorPrefix (a : ℝ) K else 0 := by
  have hs := filter_scaled (countPMF a) (Finset.range (K + 1) : Set ℕ)
    (prefix_has_support a K) k
  have hr := congrArg ENNReal.toReal hs
  rw [ENNReal.toReal_mul] at hr
  change prefixMass a K * (prefixCount a K k).toReal = _ at hr
  by_cases hk : k ≤ K
  · have hmem : k ∈ (Finset.range (K + 1) : Set ℕ) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
    rw [Set.indicator_of_mem hmem, countPMF_real, prefixMass_taylor] at hr
    rw [if_pos hk]
    apply (eq_div_iff (ne_of_gt (taylorPrefix_pos a K))).mpr
    have he := Real.exp_pos (-(a : ℝ))
    unfold taylorTerm
    nlinarith [hr]
  · have hmem : k ∉ (Finset.range (K + 1) : Set ℕ) := by
      simpa only [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff] using hk
    rw [if_neg hk]
    exact congrArg ENNReal.toReal (PMF.filter_apply_eq_zero_of_notMem (prefix_has_support a K) hmem)

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def finiteSourcePrefix (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (K : ℕ) (s : Code N sample) : PMF (Code N sample) :=
  (prefixCount (globalClockRate (Copy := Copy) r * t) K).bind
    (fun k => sourceIteration N r k s)

theorem actual_source_prefix_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (K : ℕ) (s d : Code N sample) :
    prefixMass (globalClockRate (Copy := Copy) r * t) K *
      (finiteSourcePrefix N r t K s d).toReal ≤ (sourceTimeKernel N r t s d).toReal :=
  filtered_bind_domination_real _ _ (prefix_has_support _ K) (fun k => sourceIteration N r k s) d

theorem actual_source_prefix_tv (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (K : ℕ) (s : Code N sample) :
    pmfTV (sourceTimeKernel N r t s) (finiteSourcePrefix N r t K s) ≤
      1 - prefixMass (globalClockRate (Copy := Copy) r * t) K :=
  conditioned_mixture_tv _ _ (prefix_has_support _ K) (fun k => sourceIteration N r k s)

theorem actual_source_joint_readout_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (K : ℕ) (s : Code N sample) (readout : Code N sample → O) :
    pmfTV ((sourceTimeKernel N r t s).map readout) ((finiteSourcePrefix N r t K s).map readout) ≤
      1 - prefixMass (globalClockRate (Copy := Copy) r * t) K :=
  conditioned_joint_observation_tv _ _ (prefix_has_support _ K)
    (fun k => sourceIteration N r k s) readout

theorem actual_source_joint_readout_event {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (K : ℕ) (s : Code N sample)
    (readout : Code N sample → O) (event : Finset O) :
    |(∑ o ∈ event, (((sourceTimeKernel N r t s).map readout) o).toReal) -
      ∑ o ∈ event, (((finiteSourcePrefix N r t K s).map readout) o).toReal| ≤
      1 - prefixMass (globalClockRate (Copy := Copy) r * t) K :=
  conditioned_joint_observation_event _ _ (prefix_has_support _ K)
    (fun k => sourceIteration N r k s) readout event

#print axioms prefixCount
#print axioms prefixCount_support
#print axioms prefixMass_taylor
#print axioms prefixCount_real
#print axioms actual_source_prefix_domination
#print axioms actual_source_prefix_tv
#print axioms actual_source_joint_readout_tv
#print axioms actual_source_joint_readout_event
end UnifiedLean.G6.SourcePrefix
