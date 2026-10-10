import UnifiedLean.Source.SourceMergerClockCatalogue
import Mathlib.Probability.Independence.Basic

/-!
# ORIGINAL actual post-merger current-clock reset law

Contributor: dot, 2026-10-02. Reuses library independence of product coordinates
to transport the already proved winning-time/residual law along the actual
same-rate post-merger catalogue embedding. All obsolete clocks are dropped;
the destination has its literal independent exponential current-pair law.
No destination/reset distribution is assumed. Successive timed source paths,
calendar composition and terminal genealogical completion remain next gates.
-/
namespace UnifiedLean.Source.SourceDestinationClockReset
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.SourceWinningClockReset
open UnifiedLean.Source.SourceMergerClockCatalogue
open scoped Classical BigOperators NNReal ENNReal

lemma actual_product_coordinate_projection {I J : Type*} [Fintype I] [Fintype J]
    (mu : I → Measure ℝ) [∀ i, IsProbabilityMeasure (mu i)] (e : J ↪ I) :
    (Measure.pi mu).map (fun c : I → ℝ => fun j => c (e j)) =
      Measure.pi (fun j => mu (e j)) := by
  have hind : iIndepFun (fun i : I => fun c : I → ℝ => c i) (Measure.pi mu) :=
    iIndepFun_pi (μ := mu) (X := fun _ : I => fun y : ℝ => y)
      (fun _ => measurable_id.aemeasurable)
  have hsub := hind.precomp (g := e) e.injective
  have hh := hsub.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  simp_rw [(measurePreserving_eval mu _).map_eq] at hh
  exact hh

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Every current destination clock is a genuine surviving coordinate with
the same original population rate. Its joint law is therefore the literal
actual clock product at that actual merged coded state. -/
theorem actual_destination_residual_product (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) :
    (Measure.pi (fun q : Other p => expMeasure (choiceRate N r s q.val))).map
      (fun c : Other p → ℝ => fun q : Choice N (stepDestination N s (some p)) =>
        c (destinationClockEmbedding N s p q)) =
      currentPairClockMeasure N r (stepDestination N s (some p)) := by
  letI : ∀ q : Other p, IsProbabilityMeasure (expMeasure (choiceRate N r s q.val)) :=
    fun q => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r q.val.1) (by norm_num))
  rw [actual_product_coordinate_projection _ (destinationClockEmbedding N s p)]
  rfl

/-- Actual source reset map retains the first winning time and exactly the
destination's CURRENT legal pair clocks. Old clocks incident to the removed
representative are discarded, including the winning/reversed orientations. -/
noncomputable def destinationResetMap (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    (Choice N s → ℝ) → ℝ × (Choice N (stepDestination N s (some p)) → ℝ) :=
  fun c => (c p,fun q => c (destinationClockEmbedding N s p q).val-c p)

/-- Coherent source endpoint: given an actual winning CURRENT original pair,
the actual merged destination's FULL clock catalogue is independently reset
at its SAME original rates and independent of the first winning time. This
is a full joint measure law, derived from literal clocks and actual mergers.
It still does not identify the entire multi-event timed/calendar path law. -/
theorem original_source_destination_clock_reset (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) :
    ((currentPairClockMeasure N r s).restrict (winningRegion p)).map (destinationResetMap N s p) =
      (ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).prod
        (currentPairClockMeasure N r (stepDestination N s (some p))) := by
  letI : IsProbabilityMeasure (expMeasure (totalRate N r s)) := isProbabilityMeasure_expMeasure
    (UnifiedLean.Source.SourceFirstMarkDistribution.current_pair_total_positive N r s p)
  letI := Measure.smul_finite (expMeasure (totalRate N r s))
    (show ENNReal.ofReal (choiceRate N r s p/totalRate N r s) ≠ ∞ from ENNReal.ofReal_ne_top)
  letI : ∀ q : Other p, IsProbabilityMeasure (expMeasure (choiceRate N r s q.val)) :=
    fun q => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r q.val.1) (by norm_num))
  let project : (Other p → ℝ) → (Choice N (stepDestination N s (some p)) → ℝ) :=
    fun c q => c (destinationClockEmbedding N s p q)
  have hh := congrArg (fun mu : Measure (ℝ × (Other p → ℝ)) => mu.map (Prod.map id project))
    (original_current_winner_reset N r s p)
  rw [Measure.map_map (by fun_prop) (resetClock p).measurable,
    ← Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id,
    actual_destination_residual_product N r s p] at hh
  exact hh

#print axioms actual_product_coordinate_projection
#print axioms actual_destination_residual_product
#print axioms original_source_destination_clock_reset
end UnifiedLean.Source.SourceDestinationClockReset
