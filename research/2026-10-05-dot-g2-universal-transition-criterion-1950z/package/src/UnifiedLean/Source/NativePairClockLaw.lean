import UnifiedLean.Source.NativeParentRouting
import G4AllRootPairClocks
import Mathlib.Data.ENNReal.BigOperators

/-!
# Original-edge stopped pair clocks

Contributor: dot, 2026-10-02. For two still-separate current roots, each ORIGINAL
edge occurrence has its own independent exponential holding clock, with the
source edge's positive rate. The ancestral population has one further clock.
Local exposure is computed from the actual graph calendar and compiled paths.
The product-measure no-first-merger probability is proved, rather than supplied
as a field of a source contract. This is the pair process up to its first merger;
it does not construct later multi-lineage merger/reset dynamics or an instrument.
-/
namespace UnifiedLean.Source.NativePairClockLaw
open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard
open UnifiedLean.Source.NativeParentRouting
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Positive constant rates of the ORIGINAL edge populations and the one
ancestral population. No probability-law identity is a structure field. -/
structure PositivePairRates (E : Type*) where
  edge : E → ℝ
  edge_pos : ∀ e, 0 < edge e
  ancestral : ℝ
  ancestral_pos : 0 < ancestral

noncomputable def pairRate (r : PositivePairRates E) : Option E → ℝ
  | none => r.ancestral
  | some e => r.edge e

lemma pairRate_pos (r : PositivePairRates E) (e : Option E) : 0 < pairRate r e := by
  cases e with
  | none => exact r.ancestral_pos
  | some e => exact r.edge_pos e

/-- The none coordinate is the ordinary ancestral population above the root;
some e retains the actual original edge ID, including parallel occurrences. -/
noncomputable def occupiedDuration (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (t : ℝ) : Option E → ℝ
  | none => max 0 (t - C.age N.root)
  | some e => if e ∈ R.edges x ∧ e ∈ R.edges y then exposure N.graph C t e else 0

lemma occupiedDuration_nonnegative (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (t : ℝ) (e : Option E) :
    0 ≤ occupiedDuration N C R x y t e := by
  cases e with
  | none => exact le_max_left _ _
  | some e =>
      simp only [occupiedDuration]
      split_ifs
      · exact le_max_left _ _
      · exact le_refl _

noncomputable def originalClockMeasure (r : PositivePairRates E) :
    Measure (Option E → ℝ) := Measure.pi (fun e => expMeasure (pairRate r e))

/-- Survival of all local holding clocks. A first merger makes the observer
absorbing; this event does not use coins of any post-merger descendant copies. -/
def noFirstMerger (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (t : ℝ) : Set (Option E → ℝ) :=
  Set.univ.pi (fun e => Set.Ioi (occupiedDuration N C R x y t e))

theorem noFirstMerger_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (t : ℝ) (clock : Option E → ℝ) :
    clock ∈ noFirstMerger N C R x y t ↔
      ∀ e, occupiedDuration N C R x y t e < clock e := by
  simp [noFirstMerger, Set.mem_pi]

lemma positive_exp_clock_tail {rate duration : ℝ}
    (hr : 0 < rate) (hd : 0 ≤ duration) :
    (expMeasure rate).real (Set.Ioi duration) = Real.exp (-(rate * duration)) := by
  letI : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hr
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
    ← cdf_eq_real, cdf_expMeasure_eq hr, if_pos hd]
  ring

/-- The pair survival is computed from independent original holding-time
measures. The exponential hazard is a conclusion of the product calculation. -/
theorem original_clock_no_merger_probability (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (R : RouteFamily N)
    (x y : X) (t : ℝ) :
    (originalClockMeasure r (noFirstMerger N C R x y t)).toReal =
      Real.exp (-(∑ e : Option E, pairRate r e * occupiedDuration N C R x y t e)) := by
  letI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  rw [originalClockMeasure, noFirstMerger, Measure.pi_pi, ENNReal.toReal_prod]
  change (∏ e : Option E, (expMeasure (pairRate r e)).real
    (Set.Ioi (occupiedDuration N C R x y t e))) = _
  simp only [positive_exp_clock_tail (pairRate_pos r _)
    (occupiedDuration_nonnegative N C R x y t _)]
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- Finite graph overlap plus the correctly timed ancestral-population clock. -/
theorem native_hazard_decomposition (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (R : RouteFamily N) (x y : X) (t : ℝ) :
    (∑ e : Option E, pairRate r e * occupiedDuration N C R x y t e) =
      accumulatedHazard N C r.edge R x y t + r.ancestral * max 0 (t-C.age N.root) := by
  rw [Fintype.sum_option]
  simp only [pairRate, occupiedDuration]
  rw [add_comm]
  congr 1
  unfold accumulatedHazard
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp

/-- Actual stopped pair law, including the ancestral population. -/
theorem original_clock_survival_eq_routeSurvival (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (R : RouteFamily N)
    (x y : X) (t : ℝ) :
    (originalClockMeasure r (noFirstMerger N C R x y t)).toReal =
      routeSurvival N C r.edge R x y t *
        Real.exp (-(r.ancestral * max 0 (t-C.age N.root))) := by
  rw [original_clock_no_merger_probability, native_hazard_decomposition,
    neg_add, Real.exp_add, routeSurvival]

/-- Below the actual original root, the earlier exponential route functional
is exactly this source pair probability. No ancestral exposure is missing. -/
theorem below_root_original_clock_law (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (R : RouteFamily N)
    (x y : X) {t : ℝ} (ht : t ≤ C.age N.root) :
    (originalClockMeasure r (noFirstMerger N C R x y t)).toReal =
      routeSurvival N C r.edge R x y t := by
  rw [original_clock_survival_eq_routeSurvival, max_eq_left (sub_nonpos.mpr ht)]
  simp

/-- Graph+local original-parent choices supply the routes in the probability
law. A desired survival identity was not passed to the compiler. -/
theorem compiled_original_pair_probability (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (H : OriginalParentRegistry N)
    (coin : X → Hybrid N → Bool) (x y : X) {t : ℝ} (ht : t ≤ C.age N.root) :
    (originalClockMeasure r (noFirstMerger N C (compiledRouteFamily N C H coin) x y t)).toReal =
      routeSurvival N C r.edge (compiledRouteFamily N C H coin) x y t :=
  below_root_original_clock_law N C r (compiledRouteFamily N C H coin) x y ht

#print axioms pairRate_pos
#print axioms noFirstMerger_iff
#print axioms positive_exp_clock_tail
#print axioms original_clock_no_merger_probability
#print axioms native_hazard_decomposition
#print axioms original_clock_survival_eq_routeSurvival
#print axioms below_root_original_clock_law
#print axioms compiled_original_pair_probability
end UnifiedLean.Source.NativePairClockLaw
