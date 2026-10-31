import ResearchCommons.MSCI.JC69CompleteClockComposition
import ResearchCommons.MSCI.JC69WeightedTrace
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Actual weighted ancestral completion from the SAME original clock vector.
UNCOMPILED candidate, dot (OpenAI), 31 October 2026. This proves bounds and
weighted completion passage, not a resolvent formula or finite-window theorem. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69RootWeightLimit
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceRaceWinnerSelection UnifiedLean.Source.SourceMergerClockCatalogue
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.FiniteAncestralTrace
open GProgram.G2.ActualDecorationFold
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open ResearchCommons.MSCI.JC69TraceOccupation ResearchCommons.MSCI.JC69WeightedTrace
open ResearchCommons.MSCI.JC69Source
open scoped Classical BigOperators NNReal ENNReal Topology
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

lemma code_charge_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (s : Code N sample) : 0 ≤ codeCharge N q s := by
  unfold codeCharge
  positivity

/-- An actual regular clock vector gives nonnegative waiting occupation at
nonnegative horizons, including finite fuel and the total prefix convention. -/
theorem literal_occupation_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (n : ℕ) (s : Code N sample) (t : ℝ) (ht : 0 ≤ t)
    (c : Choice N s → ℝ) (hc : ClockRegular c) : 0 ≤ literalOccupation N q n t s c := by
  induction n generalizing s t with
  | zero => exact mul_nonneg (code_charge_nonnegative N q s) ht
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, t < c p
      · simp only [literalOccupation,if_pos hstop]
        exact mul_nonneg (code_charge_nonnegative N q s) ht
      · simp only [literalOccupation,if_neg hstop]
        cases hw : selectedWinner c with
        | none => exact mul_nonneg (code_charge_nonnegative N q s) ht
        | some p =>
            by_cases hp : c p ≤ t
            · simp only [if_pos hp]
              exact add_nonneg (mul_nonneg (code_charge_nonnegative N q s) (hc.1 p))
                (ih (stepDestination N s (some p)) (t-c p) (sub_nonneg.mpr hp)
                  (fun u => c (destinationClockEmbedding N s p u).val-c p)
                  (destination_residual_regular N s c p hc hw))
            · simp only [if_neg hp]
              exact mul_nonneg (code_charge_nonnegative N q s) ht

/-- The actual failure-zeroed shared-locus readout is bounded by1 on regular
nonnegative clocks. Failure is not silently converted into success. -/
theorem actual_clock_weight_le_one (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (n : ℕ) (s : Code N sample)
    (t : ℝ) (ht : 0 ≤ t) (c : Choice N s → ℝ) (hc : ClockRegular c) :
    locusTraceWeight N L q n s t (literalMarkedTrace N n t s c) ≤ 1 := by
  by_cases hg : (literalMarkedTrace N n t s c).1 = true
  · simp only [locusTraceWeight,hg,if_true]
    have hcost : 0 ≤ ∑ j, occupationAt N (q j) n s 0 t (literalMarkedTrace N n t s c).2 := by
      apply Finset.sum_nonneg
      intro j _
      rw [actual_trace_occupation]
      exact literal_occupation_nonnegative N (q j) n s t ht c hc
    have he : Real.exp (-((4/3:ℝ) * ∑ j,
        occupationAt N (q j) n s 0 t (literalMarkedTrace N n t s c).2)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    calc
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal he
      _ = 1 := by simp
  · simp [locusTraceWeight,hg]

section Nonempty
variable [Nonempty Copy]

/-- Root occupation stabilizes exactly once the original clockCover is
passed: the actual trace is unchanged and the balanced terminal root carries
zero pending charge. No independent resampled cover is used. -/
theorem balanced_root_occupation_stable (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (hbal : ∑ x, q x = 0) (s : Code N sample)
    (hs : AncestralRoot N s) (c : Choice N s → ℝ) (hc : ClockRegular c)
    (t : ℝ) (ht : (clockCover N s c : ℝ) ≤ t) :
    literalOccupation N q (Fintype.card Copy) t s c =
      literalOccupation N q (Fintype.card Copy) (clockCover N s c : ℝ) s c := by
  let n := Fintype.card Copy
  let z := completeAncestralTrace N s c
  let out := traceEndpoint N n s z.2
  have htrace := complete_ancestral_trace_stable N s c t ht
  obtain ⟨e,he,_,hcard⟩ := complete_ancestral_trace_terminal N s c hs hc
  have hg := marked_trace_success_on_regular N n s (clockCover N s c : ℝ) c
    (Finset.card_le_univ s.val.live) hc
  dsimp only [n] at hg
  have hout : out = e := by
    simpa only [out,z,n,decodedEndpoint,completeAncestralTrace,hg,if_true,Option.some.injEq] using he
  have hcard' : (state out).live.card ≤ 1 := by
    change liveCard out ≤ 1
    rw [hout]
    exact hcard
  let M : Copy → Copy → ℝ := fun _ _ => 0
  let leafAge : Copy → ℝ := fun _ => 0
  let folded := foldMatrix N n s 0 M z.2
  have hT := actual_literal_occupation_identity N q leafAge n s t 0 c M
  rw [htrace] at hT
  have hC := actual_literal_occupation_identity N q leafAge n s (clockCover N s c : ℝ) 0 c M
  have hpT := balanced_complete_potential q leafAge (state out) out.property.forest
    hcard' (selectedRoot N out) (selected_root_live N out) hbal folded t
  have hpC := balanced_complete_potential q leafAge (state out) out.property.forest
    hcard' (selectedRoot N out) (selected_root_live N out) hbal folded (clockCover N s c : ℝ)
  have hp : forestPotential q leafAge (state out) folded t =
      forestPotential q leafAge (state out) folded (clockCover N s c : ℝ) := hpT.trans hpC.symm
  change forestPotential q leafAge (state out) folded (0+t) = _ at hT
  change forestPotential q leafAge (state out) folded (0+(clockCover N s c : ℝ)) = _ at hC
  simp only [zero_add] at hT hC
  linarith

/-- The root functional occurring in the original complete-clock integral. -/
def completeRootWeight (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (s : Code N sample) (c : Choice N s → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j,
    literalOccupation N (q j) (Fintype.card Copy) (clockCover N s c : ℝ) s c)))

theorem actual_root_weight_stable (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (hbal : ∀ j, ∑ x, q j x = 0)
    (s : Code N sample) (hs : AncestralRoot N s) (c : Choice N s → ℝ)
    (hc : ClockRegular c) (t : ℝ) (ht : (clockCover N s c : ℝ) ≤ t) :
    locusTraceWeight N L q (Fintype.card Copy) s t
      (literalMarkedTrace N (Fintype.card Copy) t s c) = completeRootWeight N L q s c := by
  have hg := marked_trace_success_on_regular N (Fintype.card Copy) s t c
    (Finset.card_le_univ s.val.live) hc
  simp only [locusTraceWeight,hg,if_true]
  have hsum : (∑ j, occupationAt N (q j) (Fintype.card Copy) s 0 t
        (literalMarkedTrace N (Fintype.card Copy) t s c).2) =
      ∑ j, literalOccupation N (q j) (Fintype.card Copy) (clockCover N s c : ℝ) s c := by
    apply Finset.sum_congr rfl
    intro j _
    rw [actual_trace_occupation]
    exact balanced_root_occupation_stable N (q j) (hbal j) s hs c hc t ht
  rw [hsum]
  rfl

/-- Weighted completion is a theorem about the actual original clock measure,
not just plain absorption. The source law is unchanged, finite-horizon success
flags remain in every approximant, and the dominating constant is integrable. -/
theorem actual_root_weight_limit (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (s : Code N sample) (hs : AncestralRoot N s) :
    Filter.Tendsto (fun m : ℕ => actualLocusWeight N r L q (Fintype.card Copy) s (m:ℝ))
      Filter.atTop (𝓝 (∫⁻ c, completeRootWeight N L q s c ∂currentPairClockMeasure N r s)) := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r s) := by
    unfold currentPairClockMeasure
    infer_instance
  simp_rw [actual_locus_weight_clock_integral]
  apply tendsto_lintegral_of_dominated_convergence (fun _ => (1:ℝ≥0∞))
  · intro m
    exact (locus_trace_weight_measurable N L q (Fintype.card Copy) s (m:ℝ)).comp
      (marked_trace_measurable N (Fintype.card Copy) s (m:ℝ))
  · intro m
    filter_upwards [actual_current_clock_regular_ae N r s] with c hc
    exact actual_clock_weight_le_one N L q (Fintype.card Copy) s (m:ℝ)
      (Nat.cast_nonneg m) c hc
  · simp
  · filter_upwards [actual_current_clock_regular_ae N r s] with c hc
    have hevent : ∀ᶠ m : ℕ in Filter.atTop,
        locusTraceWeight N L q (Fintype.card Copy) s (m:ℝ)
          (literalMarkedTrace N (Fintype.card Copy) (m:ℝ) s c) = completeRootWeight N L q s c := by
      obtain ⟨m,hm⟩ := exists_nat_ge (clockCover N s c : ℝ)
      filter_upwards [Filter.eventually_ge_atTop m] with k hk
      exact actual_root_weight_stable N L q hbal s hs c hc (k:ℝ)
        (hm.trans (by exact_mod_cast hk))
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hevent)

end Nonempty
#print axioms literal_occupation_nonnegative
#print axioms actual_clock_weight_le_one
#print axioms balanced_root_occupation_stable
#print axioms actual_root_weight_stable
#print axioms actual_root_weight_limit
end ResearchCommons.MSCI.JC69RootWeightLimit
