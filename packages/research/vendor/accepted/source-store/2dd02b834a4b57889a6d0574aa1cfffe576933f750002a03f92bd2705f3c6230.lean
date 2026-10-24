import ActualBigonRate

/-! Actual source no-loss probability for an original two-parent pulse/epoch.
Contributor: dot (OpenAI), 9 October 2026. Implements inherited private-bigon
first-merger mathematics; no scalar arm-independence premise is supplied. -/
namespace DotG34.ActualBigonSurvival
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest MeasureTheory ProbabilityTheory
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceActualHoldingClocks
open DotG34.ActualBigonRate DotG34.ActualPulseSurvival
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The exact real product weights of the actual current-owner PMF. -/
theorem actual_coin_mass (Site : Type*) [Fintype Site] (gamma : unitInterval)
    (coin : Site → Bool) :
    (currentCoinPMF Site gamma coin).toReal =
      ∏ i : Site, if coin i then (gamma : ℝ) else 1-(gamma : ℝ) := by
  rw [currentCoinPMF, Measure.toPMF_apply, independentCoinMeasure, Measure.pi_singleton,
    ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases hc : coin i <;>
    simp [bitMeasure, hc, ← measureReal_def, bernoulliMeasure_real_apply]

/-- The actual source total-rate exponential splits into the two original
arm powers by the DERIVED original-population pair counts. -/
theorem actual_bigon_holding (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (H : GProgram.G2.OriginalHybridParents N)
    (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid)
    (coin : AtNode (state s) H.hybrid → Bool) (t : ℝ≥0) :
    Real.exp (-(totalRate N r (pulseCode H s coin)*(t:ℝ))) =
      (Real.exp (-(pairRate r (some H.parent0)*(t:ℝ))))^((coinCount coin false).choose 2) *
      (Real.exp (-(pairRate r (some H.parent1)*(t:ℝ))))^((coinCount coin true).choose 2) := by
  rw [actual_bigon_rate N r H s hall coin]
  have he : -((pairRate r (some H.parent0)*((coinCount coin false).choose 2 : ℝ) +
      pairRate r (some H.parent1)*((coinCount coin true).choose 2 : ℝ))*(t:ℝ)) =
      ((coinCount coin false).choose 2 : ℝ)*(-(pairRate r (some H.parent0)*(t:ℝ))) +
      ((coinCount coin true).choose 2 : ℝ)*(-(pairRate r (some H.parent1)*(t:ℝ))) := by ring
  rw [he, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]

/-- Exact original pulse/epoch probability, for all finite live-root counts
and arbitrary old subtrees. gamma is true/parent1 probability. -/
theorem actual_bigon_survival (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (H : GProgram.G2.OriginalHybridParents N)
    (gamma : unitInterval) (t : ℝ≥0) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid) :
    (((sourceProgram N r [.boundary (.independent H gamma), .interval t] s).map
      liveCard) (liveCard s)).toReal =
    ∑ coin : AtNode (state s) H.hybrid → Bool,
      (∏ i : AtNode (state s) H.hybrid, if coin i then (gamma : ℝ) else 1-(gamma : ℝ)) *
      (Real.exp (-(pairRate r (some H.parent0)*(t:ℝ))))^((coinCount coin false).choose 2) *
      (Real.exp (-(pairRate r (some H.parent1)*(t:ℝ))))^((coinCount coin true).choose 2) := by
  rw [actual_independent_epoch_survival]
  rw [ENNReal.toReal_sum (fun coin _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro coin _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    actual_coin_mass, actual_bigon_holding N r H s hall coin t]
  ring

#print axioms actual_coin_mass
#print axioms actual_bigon_holding
#print axioms actual_bigon_survival
end DotG34.ActualBigonSurvival
