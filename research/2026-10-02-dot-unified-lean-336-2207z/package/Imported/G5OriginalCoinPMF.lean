import G5FairOriginalCoinLaw

/-!
# Probability measure for the actual finite original-site product weights

Contributor: dot, 2026-10-02. The PMF is constructed from the existing source
product weights and their proved normalization/nonnegativity. Finite event
probabilities equal the exact rational weighted sums. Thus distinct original
fair source sites give the actual uniform selector co-occupancy PMF mass.
This does not assert a continuous-time source law, safe-past disjointness,
posterior independence or an executable stochastic refinement.
-/
namespace GProgram.G5.OriginalCoinLaw
open GProgram.SourceForest
open GProgram.G5.QuartetKernel
open scoped BigOperators ENNReal NNReal
variable {Site α : Type*} [Fintype Site] [DecidableEq Site]

theorem independentWeight_real_nonnegative {p : ℚ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (coin : Site → Bool) : 0 ≤ (independentWeight p coin : ℝ) := by
  exact_mod_cast independentWeight_nonnegative hp hp1 coin

theorem independentWeight_ennreal_normalized {p : ℚ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ coin : Site → Bool, ENNReal.ofReal (independentWeight p coin : ℝ)) = 1 := by
  have hr : (∑ coin : Site → Bool, (independentWeight p coin : ℝ)) = 1 := by
    exact_mod_cast independentWeight_normalized Site p
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun coin _ => independentWeight_real_nonnegative hp hp1 coin), hr]
  norm_num

/-- A genuine PMF constructed from the actual finite original-source weights. -/
noncomputable def independentPMF (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    PMF (Site → Bool) :=
  PMF.ofFintype (fun coin => ENNReal.ofReal (independentWeight p coin : ℝ))
    (independentWeight_ennreal_normalized hp hp1)

noncomputable def weightedEvent (p : ℚ) (event : (Site → Bool) → Prop) : ℚ := by
  classical
  exact ∑ coin : Site → Bool, independentWeight p coin * if event coin then 1 else 0

/-- No external probability is fitted: the constructed source PMF event mass
is exactly the original unconditional finite product-weight sum. -/
theorem independentPMF_event {p : ℚ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (event : (Site → Bool) → Prop) :
    (independentPMF p hp hp1).toOuterMeasure {coin | event coin} =
      ENNReal.ofReal (weightedEvent p event : ℝ) := by
  classical
  rw [independentPMF, PMF.toOuterMeasure_ofFintype_apply, tsum_fintype]
  simp only [weightedEvent, Rat.cast_sum, Rat.cast_mul, apply_ite,
    Rat.cast_one, Rat.cast_zero]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro coin hcoin
    by_cases he : event coin <;> simp [Set.indicator, he]
  · intro coin hcoin
    split_ifs
    · simpa using independentWeight_real_nonnegative hp hp1 coin
    · simp

/-- Source finite PMF co-occupancy equals the genuine fair pair selector PMF
mass, for distinct original source sites and arbitrary actual position maps. -/
theorem fair_source_meeting_probability [DecidableEq α] {u v : Site}
    (hne : u ≠ v) (p q : Bool → α) :
    (independentPMF (1 / 2) (by norm_num) (by norm_num)).toOuterMeasure
      {coin | p (coin u) = q (coin v)} =
        fairMeetingMass (binaryPositions p) (binaryPositions q) := by
  classical
  have hw : weightedEvent (1 / 2) (fun coin : Site → Bool => p (coin u) = q (coin v)) =
      (pairCount (binaryPositions p) (binaryPositions q) : ℚ) / 4 := by
    rw [weightedEvent]
    trans ∑ coin : Site → Bool, independentWeight (1 / 2) coin *
      (if p (coin u) = q (coin v) then 1 else 0)
    · apply Finset.sum_congr rfl
      intro coin hcoin
      by_cases hc : p (coin u) = q (coin v) <;> simp [hc]
    · exact fair_source_meeting_weight hne p q
  rw [independentPMF_event, hw, fairMeetingMass_eq_count]
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

#print axioms independentWeight_ennreal_normalized
#print axioms independentPMF_event
#print axioms fair_source_meeting_probability
end GProgram.G5.OriginalCoinLaw
