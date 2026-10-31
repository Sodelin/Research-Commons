import ResearchCommons.MSCI.JC69RootFuelComposition
import ResearchCommons.MSCI.JC69ActualDensity

/-! The original weighted-root resolvent from actual source renewal.
UNCOMPILED, dot (OpenAI), 31 October 2026. No assumed likelihood expansion:
the SAME actual continuation is integrated under an exactly reweighted
exponential holding measure. The horizon indicator is retained through DCT. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69RootResolvent
open MeasureTheory ProbabilityTheory Set Nanuq.Source Filter
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceRaceWinnerSelection UnifiedLean.Source.SourceMergerClockCatalogue
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.FiniteAncestralTrace
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open ResearchCommons.MSCI.JC69TraceOccupation ResearchCommons.MSCI.JC69WeightedTrace
open ResearchCommons.MSCI.JC69RootWeightLimit ResearchCommons.MSCI.JC69RootFuelComposition
open ResearchCommons.MSCI.JC69ActualDensity
open scoped Classical BigOperators NNReal ENNReal Topology
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Parameter measurability is derived from actual joint compiler/readout
measurability, not assumed of a replacement killed kernel. -/
theorem actual_weight_measurable_time (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) : Measurable (actualLocusWeight N r L q n s) := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r s) := by
    unfold currentPairClockMeasure
    infer_instance
  have htrace := marked_trace_joint_measurable N n s
  have ho : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
      ∑ j, occupationAt N (q j) n s 0 z.1 (literalMarkedTrace N n z.1 s z.2).2) := by
    apply Finset.measurable_sum
    intro j _
    exact (occupation_joint_measurable N (q j) n s).comp
      (measurable_const.prodMk (measurable_fst.prodMk htrace.snd))
  have hw : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
      locusTraceWeight N L q n s z.1 (literalMarkedTrace N n z.1 s z.2)) := by
    unfold locusTraceWeight
    apply Measurable.ite
    · exact measurableSet_eq_fun htrace.fst measurable_const
    · exact (Real.measurable_exp.comp (measurable_const.mul ho).neg).ennreal_ofReal
    · exact measurable_const
  have hi := hw.lintegral_prod_right' (ν := currentPairClockMeasure N r s)
  have heq := funext (actual_locus_weight_clock_integral N r L q n s)
  rw [heq]
  exact hi

/-- Genuine actual finite-fuel bound, only at nonnegative horizon. -/
theorem actual_weight_le_one (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ) (ht : 0 ≤ t) :
    actualLocusWeight N r L q n s t ≤ 1 := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r s) := by
    unfold currentPairClockMeasure
    infer_instance
  rw [actual_locus_weight_clock_integral]
  calc
    _ ≤ ∫⁻ _c, (1:ℝ≥0∞) ∂currentPairClockMeasure N r s := by
      apply lintegral_mono_ae
      filter_upwards [actual_current_clock_regular_ae N r s] with c hc
      exact actual_clock_weight_le_one N L q n s t ht c hc
    _ = 1 := by simp

lemma locus_kill_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (s : Code N sample) :
    0 ≤ locusKill N L q s := by
  unfold locusKill
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun j _ => code_charge_nonnegative N (q j) s))

lemma actual_choice_killed_positive (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (s : Code N sample) (p : Choice N s) :
    0 < totalRate N r s + locusKill N L q s := by
  have hp := actual_choiceRate_positive N r s p
  have hC : 0 < totalRate N r s :=
    hp.trans_le (Finset.single_le_sum
      (fun i _ => (actual_choiceRate_positive N r s i).le) (Finset.mem_univ p))
  exact add_pos_of_pos_of_nonneg hC (locus_kill_nonnegative N L q s)

/-- Exact reweighting of the already-proved ORIGINAL density renewal.
The continuation still is actualLocusWeight, not a new Markov process. -/
theorem actual_killed_measure_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) :
    actualLocusWeight N r L q (n+1) s t =
      ENNReal.ofReal (Real.exp (-((totalRate N r s+locusKill N L q s)*(t:ℝ)))) +
      ∑ p : Choice N s, ∫⁻ u in Iic (t:ℝ),
        actualLocusWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u)
        ∂(ENNReal.ofReal (choiceRate N r s p/(totalRate N r s+locusKill N L q s)) •
          expMeasure (totalRate N r s+locusKill N L q s)) := by
  rw [actual_weighted_density_renewal]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact (winner_density _ _ _ (actual_choice_killed_positive N r L q s p)
    (actual_choiceRate_positive N r s p).le t.property
    (fun u => actualLocusWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u))).symm

/-- Merely a name for the ORIGINAL completed-root clock integral. -/
def rootWeight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base) (s : Code N sample) : ℝ≥0∞ :=
  ∫⁻ c, completeRootWeight N L q s c ∂currentPairClockMeasure N r s

section Nonempty
variable [Nonempty Copy]

/-- Actual outer waiting-time limit. The moving Iic horizon is an explicit
indicator; all domination applies only where the future horizon is ≥0. -/
theorem actual_root_waiting_limit (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (s : Code N sample) (hs : AncestralRoot N s)
    (p : Choice N s) (n : ℕ) (hn : liveCard (stepDestination N s (some p)) ≤ n) :
    Tendsto (fun m : ℕ => ∫⁻ u in Iic (m:ℝ),
        actualLocusWeight N r L q n (stepDestination N s (some p)) ((m:ℝ)-u)
        ∂(ENNReal.ofReal (choiceRate N r s p/(totalRate N r s+locusKill N L q s)) •
          expMeasure (totalRate N r s+locusKill N L q s))) atTop
      (𝓝 (ENNReal.ofReal (choiceRate N r s p/(totalRate N r s+locusKill N L q s)) *
        rootWeight N r L q (stepDestination N s (some p)))) := by
  let d := totalRate N r s+locusKill N L q s
  let a := ENNReal.ofReal (choiceRate N r s p/d)
  let μ := a • expMeasure d
  have hd : 0 < d := actual_choice_killed_positive N r L q s p
  letI : IsProbabilityMeasure (expMeasure d) := isProbabilityMeasure_expMeasure hd
  have hmass : μ univ = a := by simp [μ]
  have hf : Measurable (actualLocusWeight N r L q n (stepDestination N s (some p))) :=
    actual_weight_measurable_time N r L q n (stepDestination N s (some p))
  have hconv : Tendsto (fun m : ℕ => ∫⁻ u,
      (Iic (m:ℝ)).indicator
        (fun u => actualLocusWeight N r L q n (stepDestination N s (some p)) ((m:ℝ)-u)) u ∂μ)
      atTop (𝓝 (∫⁻ _u, rootWeight N r L q (stepDestination N s (some p)) ∂μ)) := by
    apply tendsto_lintegral_of_dominated_convergence (fun _ => (1:ℝ≥0∞))
    · intro m
      exact (hf.comp (measurable_const.sub measurable_id)).indicator measurableSet_Iic
    · intro m
      apply Filter.Eventually.of_forall
      intro u
      by_cases hu : u ≤ (m:ℝ)
      · rw [Set.indicator_of_mem (show u ∈ Iic (m:ℝ) from hu)]
        exact actual_weight_le_one N r L q n (stepDestination N s (some p)) _ (sub_nonneg.mpr hu)
      · rw [Set.indicator_of_notMem (show u ∉ Iic (m:ℝ) from hu)]
        exact bot_le
    · simp only [lintegral_const,one_mul,hmass]
      exact ne_of_lt ENNReal.ofReal_lt_top
    · apply Filter.Eventually.of_forall
      intro u
      have h := actual_root_weight_shifted_limit N r L q hbal n
        (stepDestination N s (some p)) hn (ancestral_merger_preserved N s hs p) u
      apply h.congr'
      obtain ⟨m,hm⟩ := exists_nat_ge u
      filter_upwards [Filter.eventually_ge_atTop m] with k hk
      have hmk : (m:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      exact (Set.indicator_of_mem (show u ∈ Iic (k:ℝ) from le_trans hm hmk)
        (fun v => actualLocusWeight N r L q n (stepDestination N s (some p)) ((k:ℝ)-v))).symm
  simpa only [lintegral_indicator measurableSet_Iic,lintegral_const,hmass,
    mul_comm,μ,a,d] using hconv

/-- Actual nonterminal balanced ancestral root equation. No formula is
assumed; equality follows by unique limits of the actual finite-horizon
renewal. Terminal states are handled separately, never through 0/0. -/
theorem actual_root_resolvent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (s : Code N sample)
    (hs : AncestralRoot N s) (hcard : 1 < liveCard s) :
    rootWeight N r L q s =
      ∑ p : Choice N s,
        ENNReal.ofReal (choiceRate N r s p/(totalRate N r s+locusKill N L q s)) *
          rootWeight N r L q (stepDestination N s (some p)) := by
  let B := Fintype.card Copy
  have hB : liveCard s ≤ B := Finset.card_le_univ s.val.live
  letI := ancestral_choice_exists N s hs hcard
  let p0 : Choice N s := Classical.choice inferInstance
  have hd := actual_choice_killed_positive N r L q s p0
  have hleft : Tendsto (fun m : ℕ => actualLocusWeight N r L q (B+1) s (m:ℝ))
      atTop (𝓝 (rootWeight N r L q s)) := by
    simpa only [sub_zero,rootWeight] using
      actual_root_weight_shifted_limit N r L q hbal (B+1) s (by omega) hs 0
  have hzero : Tendsto (fun m : ℕ => ENNReal.ofReal
      (Real.exp (-((totalRate N r s+locusKill N L q s)*(m:ℝ))))) atTop (𝓝 0) := by
    have hlin : Tendsto (fun m : ℕ => (totalRate N r s+locusKill N L q s)*(m:ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hd tendsto_natCast_atTop_atTop
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.tendsto_ofReal (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin)
  have hsum := tendsto_finsetSum Finset.univ (fun p _ =>
    actual_root_waiting_limit N r L q hbal s hs p B
      (Finset.card_le_univ (stepDestination N s (some p)).val.live))
  have hright : Tendsto (fun m : ℕ => actualLocusWeight N r L q (B+1) s (m:ℝ))
      atTop (𝓝 (∑ p : Choice N s,
        ENNReal.ofReal (choiceRate N r s p/(totalRate N r s+locusKill N L q s)) *
          rootWeight N r L q (stepDestination N s (some p)))) := by
    have h := hzero.add hsum
    simp only [zero_add] at h
    apply h.congr'
    exact Filter.Eventually.of_forall (fun m =>
      (actual_killed_measure_renewal N r L q B s ⟨(m:ℝ),Nat.cast_nonneg m⟩).symm)
  exact tendsto_nhds_unique hleft hright

/-- The completed root has no extra stem above its terminal state. Its
future weight is1; prior forest exposure remains in the source Fourier
initial/prefix factor and is NOT erased by this statement. -/
theorem actual_terminal_root_weight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (s : Code N sample) (hcard : liveCard s ≤ 1) : rootWeight N r L q s = 1 := by
  letI := choice_empty_of_terminal_card N s hcard
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r s) := by
    unfold currentPairClockMeasure
    infer_instance
  have hf (c : Choice N s → ℝ) : completeRootWeight N L q s c = 1 := by
    have hcover : (clockCover N s c : ℝ) = 0 := by
      change (∑ p : Choice N s, |c p|) = 0
      simp
    have ho (j : Fin L) (n : ℕ) : literalOccupation N (q j) n 0 s c = 0 := by
      have hstop : ∀ p : Choice N s, (0:ℝ) < c p := fun p => isEmptyElim p
      cases n <;> simp [literalOccupation,hstop]
    simp [completeRootWeight,hcover,ho]
  simp [rootWeight,hf]

end Nonempty
#print axioms actual_weight_measurable_time
#print axioms actual_weight_le_one
#print axioms actual_killed_measure_renewal
#print axioms actual_root_waiting_limit
#print axioms actual_root_resolvent
#print axioms actual_terminal_root_weight
end ResearchCommons.MSCI.JC69RootResolvent
