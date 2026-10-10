import G2LiteralMarkedClockTrace

/-!
Every active epoch age is a coordinate of the same original clock vector.
Contributor: dot (OpenAI), 6 October 2026. Fixed-boundary avoidance is then
simultaneous over all budgets and all real horizons, without an uncountable
intersection of probability-one horizon-specific events. Inactive padding
is excluded by the literal Bool flag.
-/
namespace GProgram.G2.ClockBoundaryNull
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open GProgram.G2.LiteralMarkedClockTrace
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Actual subtraction and prepend telescope to an unchanged original
coordinate. This deterministic statement includes failed-prefix outcomes. -/
theorem literal_active_time_is_coordinate (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (i : Fin n) (hi : ((literalMarkedTrace N n t s c).2 i).1 = true) :
    ∃ p : Choice N s, ((literalMarkedTrace N n t s c).2 i).2.1 = c p := by
  induction n generalizing s t with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, t < c p
      · simp [literalMarkedTrace,hstop,emptyTrace] at hi
      · rw [literalMarkedTrace,if_neg hstop] at hi ⊢
        cases hp : selectedWinner c with
        | none => simp [hp,emptyTrace] at hi
        | some p =>
            simp only [hp] at hi ⊢
            by_cases hpt : c p ≤ t
            · simp only [if_pos hpt] at hi ⊢
              revert hi
              refine Fin.cases ?_ (fun j => ?_) i
              · intro _
                exact ⟨p,rfl⟩
              · intro hj
                change ((literalMarkedTrace N n (t-c p) (stepDestination N s (some p))
                  (fun q => c (destinationClockEmbedding N s p q).val-c p)).2 j).1 = true at hj
                obtain ⟨q,hq⟩ := ih (t-c p) (stepDestination N s (some p))
                  (fun q => c (destinationClockEmbedding N s p q).val-c p) j hj
                refine ⟨(destinationClockEmbedding N s p q).val,?_⟩
                change c p + ((literalMarkedTrace N n (t-c p) (stepDestination N s (some p))
                  (fun q => c (destinationClockEmbedding N s p q).val-c p)).2 j).2.1 = _
                rw [hq]
                ring
            · simp [hpt,emptyTrace] at hi

theorem actual_clock_coordinates_avoid_fixed (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (age : ℝ) :
    ∀ᵐ c ∂currentPairClockMeasure N r s, ∀ p : Choice N s, c p ≠ age := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  letI : ∀ p : Choice N s, NullSingletonClass (expMeasure (choiceRate N r s p)) := fun p => by
    change NullSingletonClass (volume.withDensity (gammaPDF 1 (choiceRate N r s p)))
    infer_instance
  change ∀ᵐ c ∂Measure.pi (fun p : Choice N s => expMeasure (choiceRate N r s p)),
    ∀ p : Choice N s, c p ≠ age
  exact ae_all_iff.mpr (fun p => Measure.ae_eval_ne
    (fun q : Choice N s => expMeasure (choiceRate N r s q)) p age)

/-- One full-measure event works simultaneously for every actual trace
budget/horizon, including a measurable random ancestral cover. -/
theorem actual_active_times_avoid_fixed (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (age : ℝ) :
    ∀ᵐ c ∂currentPairClockMeasure N r s, ∀ (n : Nat) (t : ℝ) (i : Fin n),
      ((literalMarkedTrace N n t s c).2 i).1 = true →
        ((literalMarkedTrace N n t s c).2 i).2.1 ≠ age := by
  filter_upwards [actual_clock_coordinates_avoid_fixed N r s age] with c hc
  intro n t i hi he
  obtain ⟨p,hp⟩ := literal_active_time_is_coordinate N n t s c i hi
  exact hc p (hp.symm.trans he)

#print axioms literal_active_time_is_coordinate
#print axioms actual_clock_coordinates_avoid_fixed
#print axioms actual_active_times_avoid_fixed
end GProgram.G2.ClockBoundaryNull
