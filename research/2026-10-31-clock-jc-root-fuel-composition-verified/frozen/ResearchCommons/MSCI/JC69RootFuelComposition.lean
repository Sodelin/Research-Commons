import ResearchCommons.MSCI.JC69RootWeightLimit

/-! Actual adequate-fuel equality and shifted-horizon root completion.
UNCOMPILED, dot (OpenAI), 31 October 2026. Uses accepted d6614c43 root bound
and stability; does not assume pending density or a root resolvent. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69RootFuelComposition
open MeasureTheory ProbabilityTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceRaceWinnerSelection UnifiedLean.Source.SourceMergerClockCatalogue
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.FiniteAncestralTrace
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open ResearchCommons.MSCI.JC69TraceOccupation ResearchCommons.MSCI.JC69WeightedTrace
open ResearchCommons.MSCI.JC69RootWeightLimit
open scoped Classical BigOperators NNReal ENNReal Topology
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Scalar readout equality, not an equality of differently padded trace
vectors. Actual merger-card descent makes both remaining budgets adequate.
This deterministic identity needs neither regular clocks nor t≥0. -/
theorem literal_occupation_fuel_irrel (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (n m : ℕ) (s : Code N sample) (t : ℝ)
    (c : Choice N s → ℝ) (hn : liveCard s ≤ n) (hm : liveCard s ≤ m) :
    literalOccupation N q n t s c = literalOccupation N q m t s c := by
  induction n generalizing m s t with
  | zero =>
      have hstop : ∀ p : Choice N s, t < c p := by
        intro p
        have hd := merger_destination_card N s p
        omega
      cases m <;> simp only [literalOccupation,if_pos hstop]
  | succ n ih =>
      cases m with
      | zero =>
          have hstop : ∀ p : Choice N s, t < c p := by
            intro p
            have hd := merger_destination_card N s p
            omega
          simp only [literalOccupation,if_pos hstop]
      | succ m =>
          by_cases hstop : ∀ p : Choice N s, t < c p
          · simp only [literalOccupation,if_pos hstop]
          · simp only [literalOccupation,if_neg hstop]
            cases hw : selectedWinner c with
            | none => rfl
            | some p =>
                by_cases hp : c p ≤ t
                · simp only [if_pos hp]
                  have hd := merger_destination_card N s p
                  have hn' : liveCard (stepDestination N s (some p)) ≤ n := by omega
                  have hm' : liveCard (stepDestination N s (some p)) ≤ m := by omega
                  rw [ih m (stepDestination N s (some p)) (t-c p)
                    (fun v => c (destinationClockEmbedding N s p v).val-c p) hn' hm']
                · simp only [if_neg hp]

/-- Success is supplied on the actual regular-clock event at BOTH budgets;
no arbitrary failure flag is discarded. -/
theorem actual_clock_weight_fuel_irrel (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (n m : ℕ) (s : Code N sample) (t : ℝ)
    (c : Choice N s → ℝ) (hn : liveCard s ≤ n) (hm : liveCard s ≤ m)
    (hc : ClockRegular c) :
    locusTraceWeight N L q n s t (literalMarkedTrace N n t s c) =
      locusTraceWeight N L q m s t (literalMarkedTrace N m t s c) := by
  have hsn := marked_trace_success_on_regular N n s t c hn hc
  have hsm := marked_trace_success_on_regular N m s t c hm hc
  simp only [locusTraceWeight,hsn,hsm,if_true]
  have hsum : (∑ j, occupationAt N (q j) n s 0 t (literalMarkedTrace N n t s c).2) =
      ∑ j, occupationAt N (q j) m s 0 t (literalMarkedTrace N m t s c).2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [actual_trace_occupation,actual_trace_occupation]
    exact literal_occupation_fuel_irrel N (q j) n m s t c hn hm
  rw [hsum]

/-- Equality under the SAME original clock measure and actual trace laws. -/
theorem actual_weight_fuel_irrel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n m : ℕ) (s : Code N sample) (t : ℝ)
    (hn : liveCard s ≤ n) (hm : liveCard s ≤ m) :
    actualLocusWeight N r L q n s t = actualLocusWeight N r L q m s t := by
  rw [actual_locus_weight_clock_integral,actual_locus_weight_clock_integral]
  apply lintegral_congr_ae
  filter_upwards [actual_current_clock_regular_ae N r s] with c hc
  exact actual_clock_weight_fuel_irrel N L q n m s t c hn hm hc

section Nonempty
variable [Nonempty Copy]

/-- Actual completion at shifted horizons and any adequate remaining fuel.
Negative early horizons are handled by eventual equality, NOT by asserting a
≤1 bound there. DCT is applied to max 0 (m-u), retaining the genuine bound. -/
theorem actual_root_weight_shifted_limit (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (n : ℕ) (s : Code N sample)
    (hn : liveCard s ≤ n) (hs : AncestralRoot N s) (u : ℝ) :
    Filter.Tendsto (fun m : ℕ => actualLocusWeight N r L q n s ((m:ℝ)-u))
      Filter.atTop (𝓝 (∫⁻ c, completeRootWeight N L q s c ∂currentPairClockMeasure N r s)) := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r s) := by
    unfold currentPairClockMeasure
    infer_instance
  have hfull : liveCard s ≤ Fintype.card Copy := Finset.card_le_univ s.val.live
  have hmax : Filter.Tendsto
      (fun m : ℕ => actualLocusWeight N r L q n s (max 0 ((m:ℝ)-u)))
      Filter.atTop (𝓝 (∫⁻ c, completeRootWeight N L q s c ∂currentPairClockMeasure N r s)) := by
    simp_rw [actual_locus_weight_clock_integral]
    apply tendsto_lintegral_of_dominated_convergence (fun _ => (1:ℝ≥0∞))
    · intro m
      exact (locus_trace_weight_measurable N L q n s _).comp
        (marked_trace_measurable N n s _)
    · intro m
      filter_upwards [actual_current_clock_regular_ae N r s] with c hc
      exact actual_clock_weight_le_one N L q n s _ (le_max_left _ _) c hc
    · simp
    · filter_upwards [actual_current_clock_regular_ae N r s] with c hc
      have hevent : ∀ᶠ m : ℕ in Filter.atTop,
          locusTraceWeight N L q n s (max 0 ((m:ℝ)-u))
            (literalMarkedTrace N n (max 0 ((m:ℝ)-u)) s c) = completeRootWeight N L q s c := by
        obtain ⟨m,hm⟩ := exists_nat_ge ((clockCover N s c : ℝ)+u)
        filter_upwards [Filter.eventually_ge_atTop m] with k hk
        have hmk : (m:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        have ht : (clockCover N s c : ℝ) ≤ max 0 ((k:ℝ)-u) :=
          le_trans (by linarith) (le_max_right _ _)
        rw [actual_clock_weight_fuel_irrel N L q n (Fintype.card Copy) s _ c hn hfull hc]
        exact actual_root_weight_stable N L q hbal s hs c hc _ ht
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hevent)
  apply hmax.congr'
  obtain ⟨m,hm⟩ := exists_nat_ge u
  filter_upwards [Filter.eventually_ge_atTop m] with k hk
  have hmk : (m:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  rw [max_eq_right (by linarith : 0 ≤ (k:ℝ)-u)]

end Nonempty
#print axioms literal_occupation_fuel_irrel
#print axioms actual_clock_weight_fuel_irrel
#print axioms actual_weight_fuel_irrel
#print axioms actual_root_weight_shifted_limit
end ResearchCommons.MSCI.JC69RootFuelComposition
