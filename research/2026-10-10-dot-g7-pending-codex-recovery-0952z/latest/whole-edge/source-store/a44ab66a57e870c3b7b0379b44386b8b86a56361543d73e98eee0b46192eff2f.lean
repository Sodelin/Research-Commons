import ActualPulseSurvival
import Mathlib.Data.Nat.Choose.Cast

/-! Actual total merger rate grouped by original population.
Contributor: dot (OpenAI), 9 October 2026. Counts original ordered source choices;
not an assumed Kingman rate or replacement population bank. -/
namespace DotG34.ActualPopulationRate
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_rate_off_diagonal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    totalRate N r s = ∑ i : Option E,
      ((populationRoots (state s) (originalPlace N i)).offDiag.card : ℝ) * (pairRate r i/2) := by
  simp [totalRate, choiceRate, Fintype.sum_sigma]

lemma off_diagonal_real {A : Type*} [DecidableEq A] (a : Finset A) :
    (a.offDiag.card : ℝ) = (a.card : ℝ) * ((a.card : ℝ)-1) := by
  rw [Finset.offDiag_card]
  have h : a.card ≤ a.card*a.card := Nat.le_mul_self _
  rw [Nat.cast_sub h, Nat.cast_mul]
  ring

theorem actual_rate_choose_two (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    totalRate N r s = ∑ i : Option E,
      pairRate r i * ((populationRoots (state s) (originalPlace N i)).card.choose 2 : ℝ) := by
  rw [actual_rate_off_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [off_diagonal_real, Nat.cast_choose_two]
  ring

#print axioms actual_rate_choose_two
end DotG34.ActualPopulationRate
