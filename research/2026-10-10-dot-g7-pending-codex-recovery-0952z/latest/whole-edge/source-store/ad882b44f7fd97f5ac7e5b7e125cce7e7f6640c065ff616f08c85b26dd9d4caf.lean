import UnifiedLean.Source.SourceFiniteJumpExpansion

/-!
# Measurable actual winning-coordinate selection for the source clock path

Contributor: dot, 2026-10-02. Strict winning regions are disjoint and their
ACTUAL exponential-product masses sum to one. The measurable selector's
failure event therefore has zero mass whenever the current catalogue is
nonempty. No arbitrary tie-breaker is given positive physical probability.
This is the path-map admission component, not yet its full pushforward law.
-/
namespace UnifiedLean.Source.SourceRaceWinnerSelection
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.SourceExponentialRaceDensity
open UnifiedLean.Source.SourceWinningClockReset
open scoped Classical BigOperators NNReal ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma winning_coordinate_unique (c : I → ℝ) {p q : I}
    (hp : c ∈ winningRegion p) (hq : c ∈ winningRegion q) : p = q := by
  by_contra hne
  exact (hp.2 ⟨q,Ne.symm hne⟩).asymm (hq.2 ⟨p,hne⟩)

lemma winning_regions_disjoint : _root_.Pairwise (fun p q : I => Disjoint (winningRegion p) (winningRegion q)) := by
  intro p q hne
  apply Set.disjoint_left.mpr
  intro c hp hq
  exact hne (winning_coordinate_unique c hp hq)

noncomputable def selectedWinner (c : I → ℝ) : Option I :=
  if h : ∃ p : I, c ∈ winningRegion p then some (Classical.choose h) else none

lemma selectedWinner_eq_some_iff (c : I → ℝ) (p : I) :
    selectedWinner c = some p ↔ c ∈ winningRegion p := by
  by_cases h : ∃ q : I, c ∈ winningRegion q
  · rw [selectedWinner,dif_pos h,Option.some.injEq]
    constructor
    · intro heq
      rw [← heq]
      exact Classical.choose_spec h
    · intro hp
      exact winning_coordinate_unique c (Classical.choose_spec h) hp
  · rw [selectedWinner,dif_neg h]
    constructor
    · intro hf; cases hf
    · intro hp; exact False.elim (h ⟨p,hp⟩)

lemma selectedWinner_none_preimage :
    (selectedWinner : (I → ℝ) → Option I) ⁻¹' {none} = (⋃ p : I, winningRegion p)ᶜ := by
  ext c
  simp only [mem_preimage,mem_singleton_iff,mem_compl_iff,mem_iUnion]
  by_cases h : ∃ q : I, c ∈ winningRegion q <;> simp [selectedWinner,h]

lemma selectedWinner_measurable [MeasurableSpace (Option I)] :
    Measurable (selectedWinner : (I → ℝ) → Option I) := by
  apply measurable_to_countable'
  intro z
  cases z with
  | none =>
      rw [selectedWinner_none_preimage]
      exact (MeasurableSet.iUnion measurable_winningRegion).compl
  | some p =>
      have hh : (selectedWinner : (I → ℝ) → Option I) ⁻¹' {some p} = winningRegion p := by
        ext c
        exact selectedWinner_eq_some_iff c p
      rw [hh]
      exact measurable_winningRegion p

lemma actual_winning_region_mass (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I) :
    (Measure.pi (fun i => expMeasure (rate i))) (winningRegion p) =
      ENNReal.ofReal (rate p/(∑ i, rate i)) := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  letI := isProbabilityMeasure_expMeasure (race_total_positive rate hr p)
  have hh := congrArg (fun mu : Measure (ℝ × (Other p → ℝ)) => mu univ)
    (actual_winner_reset_measure rate hr p)
  rw [(resetClock p).map_apply,preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter] at hh
  rw [← Set.univ_prod_univ,Measure.prod_prod,Measure.smul_apply,smul_eq_mul,
    measure_univ,measure_univ,mul_one,mul_one] at hh
  exact hh

/-- Every nonempty actual strictly-positive clock catalogue has a unique
strict winning coordinate almost surely. Ties/negative/pathological records
are excluded by a DERIVED zero-mass result, not an admission premise. -/
theorem actual_no_winner_null (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p0 : I) :
    (Measure.pi (fun i => expMeasure (rate i)))
      ((selectedWinner : (I → ℝ) → Option I) ⁻¹' {none}) = 0 := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  have htotal := race_total_positive rate hr p0
  have hm := MeasurableSet.iUnion (measurable_winningRegion (I := I))
  have hmass : (Measure.pi (fun i => expMeasure (rate i))) (⋃ p : I, winningRegion p) = 1 := by
    rw [measure_iUnion winning_regions_disjoint measurable_winningRegion,tsum_fintype]
    simp_rw [actual_winning_region_mass rate hr]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => div_nonneg (hr p).le htotal.le),
      ← Finset.sum_div,div_self htotal.ne',ENNReal.ofReal_one]
  rw [selectedWinner_none_preimage,measure_compl hm (measure_ne_top _ _),hmass,measure_univ,tsub_self]

#print axioms selectedWinner_measurable
#print axioms actual_no_winner_null
end UnifiedLean.Source.SourceRaceWinnerSelection
