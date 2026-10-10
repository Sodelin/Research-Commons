import UnifiedLean.Source.SourceAncestralDrift
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative absorption of the actual original ancestral source

Contributor: dot, 2026-10-02. Derives finite-step and physical-time transient
bounds from the actual root catalogue, original positive ancestral rate and
constructed source PMFs. This is the connected eventual-completion gate, with
no uniform unknown-rival rate or effective hidden graph budget assumed.
-/
namespace UnifiedLean.Source.SourceAncestralAbsorption
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceAncestralDrift
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma finite_bind_expectation {A B : Type*} [Fintype A] [Fintype B]
    (p : PMF A) (f : A → PMF B) (F : B → ℝ) :
    (∑ b : B, ((p.bind f) b).toReal * F b) =
      ∑ a : A, (p a).toReal * (∑ b : B, (f a b).toReal * F b) := by
  simp_rw [bind_probability_real,tsum_fintype,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

noncomputable def contractionRatio (r : PositivePairRates E) : ℝ :=
  1-(r.ancestral/2)/globalRateBound (Copy := Copy) r

lemma contractionRatio_bounds (r : PositivePairRates E) :
    0 ≤ contractionRatio (Copy := Copy) r ∧ contractionRatio (Copy := Copy) r < 1 := by
  have hr : r.ancestral ≤ ∑ i : Option E, pairRate r i := by
    exact Finset.single_le_sum (fun i _ => (pairRate_pos r i).le) (Finset.mem_univ none)
  have hsum : 0 ≤ ∑ i : Option E, pairRate r i :=
    Finset.sum_nonneg (fun i _ => (pairRate_pos r i).le)
  have hν : r.ancestral/2 ≤ globalRateBound (Copy := Copy) r := by
    unfold globalRateBound
    nlinarith [sq_nonneg (Fintype.card Copy : ℝ),r.ancestral_pos]
  have hdiv := (div_le_one (globalRateBound_positive (Copy := Copy) r)).mpr hν
  have hpos := div_pos (show 0 < r.ancestral/2 by linarith [r.ancestral_pos])
    (globalRateBound_positive (Copy := Copy) r)
  unfold contractionRatio
  constructor <;> linarith

lemma ancestral_step_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s)
    {d : Code N sample} (hd : d ∈ (sourceStep N r s).support) : AncestralRoot N d := by
  obtain ⟨q,_,hq⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  rw [← hq]
  cases q with
  | none => exact hs
  | some p => exact ancestral_merger_preserved N s hs p

/-- Actual source iterations preserve original ancestral locations. -/
lemma ancestral_iteration_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s : Code N sample) (hs : AncestralRoot N s)
    {d : Code N sample} (hd : d ∈ (sourceIteration N r k s).support) : AncestralRoot N d := by
  induction k generalizing s with
  | zero =>
      have h : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      simpa [h] using hs
  | succ k ih =>
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih m (ancestral_step_support N r s hs hm) hdm

/-- Source-derived geometric drift, for every original root state and number
of genuine uniformization trials. Holds are included with their actual mass. -/
theorem actual_ancestral_iteration_rank_bound [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (k : Nat) (s : Code N sample)
    (hs : AncestralRoot N s) :
    (∑ d : Code N sample, (sourceIteration N r k s d).toReal * excessRank d) ≤
      contractionRatio (Copy := Copy) r ^ k * excessRank s := by
  have hq := (contractionRatio_bounds (Copy := Copy) r).1
  induction k generalizing s with
  | zero => simp [sourceIteration,PMF.pure_apply,apply_ite]
  | succ k ih =>
      rw [sourceIteration,finite_bind_expectation]
      calc
        _ ≤ ∑ m : Code N sample, (sourceStep N r s m).toReal *
            (contractionRatio (Copy := Copy) r ^ k * excessRank m) := by
          apply Finset.sum_le_sum
          intro m _
          by_cases hm : m ∈ (sourceStep N r s).support
          · exact mul_le_mul_of_nonneg_left (ih m (ancestral_step_support N r s hs hm))
              ENNReal.toReal_nonneg
          · have hz : sourceStep N r s m = 0 := by simpa only [PMF.mem_support_iff,not_not] using hm
            simp [hz]
        _ = contractionRatio (Copy := Copy) r ^ k *
            (∑ m : Code N sample, (sourceStep N r s m).toReal * excessRank m) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          ring
        _ ≤ contractionRatio (Copy := Copy) r ^ k *
            (contractionRatio (Copy := Copy) r * excessRank s) :=
          mul_le_mul_of_nonneg_left (actual_ancestral_excessRank_contraction N r s hs)
            (pow_nonneg hq k)
        _ = _ := by rw [pow_succ]; ring

/-- Any still-uncoalesced original source state has probability bounded by
actual expected excess rank, hence by the source-derived geometric factor. -/
theorem actual_ancestral_iteration_transient_bound [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (k : Nat) (s d : Code N sample)
    (hs : AncestralRoot N s) (hd : 1 < liveCard d) :
    (sourceIteration N r k s d).toReal ≤ contractionRatio (Copy := Copy) r ^ k * excessRank s := by
  have hr : (1 : ℝ) ≤ excessRank d := by
    unfold excessRank
    have hh : (2 : ℝ) ≤ (liveCard d : ℝ) := by exact_mod_cast hd
    linarith
  calc
    _ ≤ (sourceIteration N r k s d).toReal * excessRank d := by
      nlinarith [show 0 ≤ (sourceIteration N r k s d).toReal from ENNReal.toReal_nonneg]
    _ ≤ ∑ z : Code N sample, (sourceIteration N r k s z).toReal * excessRank z :=
      Finset.single_le_sum (fun z _ => mul_nonneg ENNReal.toReal_nonneg (excessRank_nonnegative N z))
        (Finset.mem_univ d)
    _ ≤ _ := actual_ancestral_iteration_rank_bound N r k s hs

/-- The actual Poisson/source epoch has exponentially vanishing transient
mass. The rate is the ORIGINAL positive ancestral rate, not an asserted
absorption law or a rate uniform over unknown graphs. -/
theorem actual_ancestral_time_transient_bound [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample)
    (hs : AncestralRoot N s) (hd : 1 < liveCard d) :
    (sourceTimeKernel N r t s d).toReal ≤ excessRank s * Real.exp (-(r.ancestral/2*(t : ℝ))) := by
  let a : ℝ := globalRateBound (Copy := Copy) r * (t : ℝ)
  let q := contractionRatio (Copy := Copy) r
  have hsum : HasSum (fun k : Nat =>
      (Real.exp (-a) * a^k / k.factorial) * (q^k * excessRank s))
      (Real.exp (-a) * Real.exp (a*q) * excessRank s) := by
    simpa only [mul_pow,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,← Real.exp_eq_exp_ℝ]
      using ((NormedSpace.expSeries_div_hasSum_exp (a*q)).mul_left (Real.exp (-a))).mul_right (excessRank s)
  have hnon : ∀ k : Nat, 0 ≤ (countPMF (globalClockRate (Copy := Copy) r*t) k).toReal *
      (sourceIteration N r k s d).toReal := fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hle : ∀ k : Nat, (countPMF (globalClockRate (Copy := Copy) r*t) k).toReal *
      (sourceIteration N r k s d).toReal ≤
      (Real.exp (-a)*a^k/k.factorial)*(q^k*excessRank s) := by
    intro k
    have hh := mul_le_mul_of_nonneg_left (actual_ancestral_iteration_transient_bound N r k s d hs hd)
      (show 0 ≤ (countPMF (globalClockRate (Copy := Copy) r*t) k).toReal from ENNReal.toReal_nonneg)
    rw [countPMF_real] at hh
    change (Real.exp (-a)*a^k/k.factorial)*(sourceIteration N r k s d).toReal ≤
      (Real.exp (-a)*a^k/k.factorial)*(q^k*excessRank s) at hh
    rw [countPMF_real]
    exact hh
  rw [sourceTimeKernel,bind_probability_real]
  calc
    _ ≤ ∑' k : Nat, (Real.exp (-a)*a^k/k.factorial)*(q^k*excessRank s) :=
      (hsum.summable.of_nonneg_of_le hnon hle).tsum_le_tsum hle hsum.summable
    _ = Real.exp (-a) * Real.exp (a*q) * excessRank s := hsum.tsum_eq
    _ = _ := by
      rw [← Real.exp_add,mul_comm _ (excessRank s)]
      congr 2
      dsimp [a,q,contractionRatio]
      have hν := (globalRateBound_positive (Copy := Copy) r).ne'
      field_simp [hν]
      ring

#print axioms actual_ancestral_iteration_rank_bound
#print axioms actual_ancestral_iteration_transient_bound
#print axioms actual_ancestral_time_transient_bound
end UnifiedLean.Source.SourceAncestralAbsorption
