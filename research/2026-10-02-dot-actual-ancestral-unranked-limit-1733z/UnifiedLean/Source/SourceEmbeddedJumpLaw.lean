import UnifiedLean.Source.SourceRaceWinnerSelection

/-!
# Actual ORIGINAL source embedded real-merger jump law

Contributor: dot, 2026-10-02. Constructs original current pair-rate fractions,
with absorption only when the actual legal catalogue is empty. The resulting
PMF is PROVED to be the literal independent exponential clock winner law.
This is the embedded event law used for unranked ancestral completion. Dummy
uniformization holds are not counted as mergers; no desired jump law is a
contract field. Full timed source strengthening remains a separate goal.
-/
namespace UnifiedLean.Source.SourceEmbeddedJumpLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceFirstMarkDistribution
open UnifiedLean.Source.SourceRaceWinnerSelection
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

local instance choiceOptionMeasurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : MeasurableSpace (Option (Choice N s)) := ⊤

noncomputable def jumpMass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Option (Choice N s) → ℝ
  | none => if totalRate N r s = 0 then 1 else 0
  | some p => choiceRate N r s p/totalRate N r s

lemma jumpMass_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (q : Option (Choice N s)) :
    0 ≤ jumpMass N r s q := by
  cases q with
  | none => unfold jumpMass; split_ifs <;> norm_num
  | some p =>
      exact div_nonneg (div_pos (pairRate_pos r p.1) (by norm_num)).le
        (totalRate_nonnegative N r s)

lemma jumpMass_normalized (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (∑ q : Option (Choice N s), jumpMass N r s q) = 1 := by
  rw [Fintype.sum_option]
  simp only [jumpMass]
  by_cases hz : totalRate N r s = 0
  · simp [hz]
  · rw [if_neg hz,← Finset.sum_div]
    change 0+totalRate N r s/totalRate N r s = 1
    simp [hz]

/-- This PMF uses only actual original pair rates and their actual current
catalogue; the zero-rate row absorbs because no current pair exists. -/
noncomputable def sourceJumpChoice (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : PMF (Option (Choice N s)) :=
  PMF.ofFintype (fun q => ENNReal.ofReal (jumpMass N r s q)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => jumpMass_nonnegative N r s q),jumpMass_normalized]
    simp)

lemma sourceJumpChoice_apply (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (q : Option (Choice N s)) :
    sourceJumpChoice N r s q = ENNReal.ofReal (jumpMass N r s q) := PMF.ofFintype_apply _ _

lemma choice_empty_of_zero_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hz : totalRate N r s = 0) :
    IsEmpty (Choice N s) := ⟨fun p => (current_pair_total_positive N r s p).ne' hz⟩

lemma choice_nonempty_of_nonzero_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hz : totalRate N r s ≠ 0) :
    Nonempty (Choice N s) := by
  by_contra he
  letI : IsEmpty (Choice N s) := ⟨not_nonempty_iff_imp_false.mp he⟩
  exact hz (by simp [totalRate])

set_option maxHeartbeats 600000 in
/-- The source embedded-jump choice is EXACTLY the actual independent current
exponential-clock winner, including the genuine empty-catalogue absorption.
Tie/pathological branches have zero mass in every nonempty positive catalogue. -/
theorem original_clock_winner_eq_jump_choice (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (currentPairClockMeasure N r s).map selectedWinner = (sourceJumpChoice N r s).toMeasure := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  apply Measure.ext_of_singleton
  intro q
  rw [Measure.map_apply selectedWinner_measurable (measurableSet_singleton q),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton q),sourceJumpChoice_apply]
  cases q with
  | some p =>
      have hp : (selectedWinner : (Choice N s → ℝ) → Option (Choice N s)) ⁻¹' {some p} =
          UnifiedLean.Source.SourceWinningClockReset.winningRegion p := by
        ext c
        exact selectedWinner_eq_some_iff c p
      rw [hp]
      simpa only [currentPairClockMeasure,jumpMass,totalRate] using
        (actual_winning_region_mass (I := Choice N s) (choiceRate N r s)
          (fun q => div_pos (pairRate_pos r q.1) (by norm_num)) p)
  | none =>
      by_cases hz : totalRate N r s = 0
      · letI := choice_empty_of_zero_rate N r s hz
        have hc : (selectedWinner : (Choice N s → ℝ) → Option (Choice N s)) = fun _ => none := by
          funext c
          simp [selectedWinner]
        rw [hc]
        simp [jumpMass,hz,currentPairClockMeasure]
      · obtain ⟨p0⟩ := choice_nonempty_of_nonzero_rate N r s hz
        change (Measure.pi (fun q : Choice N s => expMeasure (choiceRate N r s q)))
          (selectedWinner ⁻¹' {none}) = _
        rw [actual_no_winner_null (choiceRate N r s)
          (fun q => div_pos (pairRate_pos r q.1) (by norm_num)) p0]
        simp [jumpMass,hz]

noncomputable def sourceJumpStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : PMF (Code N sample) :=
  (sourceJumpChoice N r s).map (stepDestination N s)

#print axioms jumpMass_normalized
#print axioms original_clock_winner_eq_jump_choice
end UnifiedLean.Source.SourceEmbeddedJumpLaw
