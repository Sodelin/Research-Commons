import ResearchCommons.MSCI.JC69TraceOccupation

/-! Later extension, NOT in frozen occupation v1. UNCOMPILED.
Concrete shared-locus weight factorization on the original prepend operation.
No assumed killed law, likelihood expansion, success conditioning, or fresh
independent genealogy per site. Contributor: dot (OpenAI), 30 October 2026. -/
noncomputable section
namespace ResearchCommons.MSCI.JC69WeightedTrace
open MeasureTheory ProbabilityTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceRenewal
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open ResearchCommons.MSCI.JC69TraceOccupation
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

def locusKill (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (s : Code N sample) : ℝ :=
  (4/3:ℝ) * ∑ j, codeCharge N (q j) s

/-- Exact original first-event readout, with the FUTURE success flag retained. -/
theorem locus_weight_prepend (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (n : ℕ) (s d : Code N sample)
    (age t : ℝ) (z : Bool × ClockTrace N sample n) :
    locusTraceWeight N L q (n+1) s t (z.1,prependTrace N age d z.2) =
      ENNReal.ofReal (Real.exp (-(locusKill N L q s * age))) *
        locusTraceWeight N L q n d (t-age) z := by
  by_cases hz : z.1 = true
  · simp only [locusTraceWeight,hz,if_true,occupation_prepend]
    have he : -((4/3:ℝ) * ∑ j,
          (codeCharge N (q j) s*age + occupationAt N (q j) n d 0 (t-age) z.2)) =
        -(locusKill N L q s*age) +
          -((4/3:ℝ)* ∑ j, occupationAt N (q j) n d 0 (t-age) z.2) := by
      rw [Finset.sum_add_distrib,← Finset.sum_mul]
      unfold locusKill
      ring
    rw [he,Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
  · simp [locusTraceWeight,hz]

theorem locus_weight_empty (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (n : ℕ) (s : Code N sample) (t : ℝ) :
    locusTraceWeight N L q n s t (true,emptyTrace N n s) =
      ENNReal.ofReal (Real.exp (-(locusKill N L q s*t))) := by
  simp only [locusTraceWeight,if_true,occupation_empty,sub_zero]
  rw [← Finset.sum_mul]
  congr 2
  unfold locusKill
  ring

/-- The actual positive shared-locus occupation expectation. This definition
integrates the ORIGINAL marked-trace law; no replacement process is supplied. -/
def actualLocusWeight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, locusTraceWeight N L q n s t z ∂actualMarkedTraceLaw N r n s t

/-- Integrating the PROVED actual marked-trace decomposition gives the
concrete weighted first-jump branches. Future clocks remain the original
reset product measure, and its success flag is unchanged. This stops before
Tonelli/density evaluation or a finite-path exponential-polynomial formula. -/
theorem actual_weighted_trace_first_jump_branches (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) :
    actualLocusWeight N r L q (n+1) s t =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) *
        ENNReal.ofReal (Real.exp (-(locusKill N L q s*(t : ℝ)))) +
      ∑ p : Choice N s,
        ∫⁻ z : ℝ × (Choice N (stepDestination N s (some p)) → ℝ),
          ENNReal.ofReal (Real.exp (-(locusKill N L q s*z.1))) *
            locusTraceWeight N L q n (stepDestination N s (some p)) ((t : ℝ)-z.1)
              (literalMarkedTrace N n ((t : ℝ)-z.1) (stepDestination N s (some p)) z.2)
          ∂(((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) •
              expMeasure (totalRate N r s)).restrict (Iic (t : ℝ))).prod
                (currentPairClockMeasure N r (stepDestination N s (some p)))) := by
  have hw := locus_trace_weight_measurable N L q (n+1) s (t : ℝ)
  rw [actualLocusWeight,actual_marked_trace_first_jump_renewal,
    lintegral_add_measure,lintegral_smul_measure,lintegral_dirac' _ hw,
    locus_weight_empty,lintegral_finsetSum_measure]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [lintegral_map hw (first_jump_future_measurable N n s p t)]
  apply lintegral_congr
  intro z
  exact locus_weight_prepend N L q n s (stepDestination N s (some p)) z.1 t
    (literalMarkedTrace N n ((t : ℝ)-z.1) (stepDestination N s (some p)) z.2)

lemma actual_locus_weight_clock_integral (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ) :
    actualLocusWeight N r L q n s t =
      ∫⁻ c, locusTraceWeight N L q n s t (literalMarkedTrace N n t s c)
        ∂currentPairClockMeasure N r s := by
  rw [actualLocusWeight,actualMarkedTraceLaw,
    lintegral_map (locus_trace_weight_measurable N L q n s t) (marked_trace_measurable N n s t)]

/-- Genuine closed renewal for the ACTUAL shared-locus weight. Tonelli and
the exact clock pushforward discharge the future integral. No killed-law
formula is supplied as a premise. Density evaluation and finite path/count
identities remain subsequent obligations. -/
theorem actual_weighted_trace_renewal (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) :
    actualLocusWeight N r L q (n+1) s t =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) *
        ENNReal.ofReal (Real.exp (-(locusKill N L q s*(t : ℝ)))) +
      ∑ p : Choice N s,
        ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (-(locusKill N L q s*u))) *
          actualLocusWeight N r L q n (stepDestination N s (some p)) ((t : ℝ)-u)
          ∂((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) •
            expMeasure (totalRate N r s)).restrict (Iic (t : ℝ))) := by
  rw [actual_weighted_trace_first_jump_branches]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  letI : ∀ v : Choice N (stepDestination N s (some p)),
      IsProbabilityMeasure (expMeasure (choiceRate N r (stepDestination N s (some p)) v)) :=
    fun v => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r v.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r (stepDestination N s (some p))) := by
    unfold currentPairClockMeasure
    infer_instance
  have hf : Measurable (fun z : ℝ × (Choice N (stepDestination N s (some p)) → ℝ) =>
      ENNReal.ofReal (Real.exp (-(locusKill N L q s*z.1))) *
        locusTraceWeight N L q n (stepDestination N s (some p)) ((t : ℝ)-z.1)
          (literalMarkedTrace N n ((t : ℝ)-z.1) (stepDestination N s (some p)) z.2)) := by
    have h := (locus_trace_weight_measurable N L q (n+1) s (t : ℝ)).comp
      (first_jump_future_measurable N n s p t)
    convert h using 1
    funext z
    exact (locus_weight_prepend N L q n s (stepDestination N s (some p)) z.1 t
      (literalMarkedTrace N n ((t : ℝ)-z.1) (stepDestination N s (some p)) z.2)).symm
  rw [lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro u
  dsimp only [Prod.fst, Prod.snd]
  have hc := lintegral_const_mul
    (μ := currentPairClockMeasure N r (stepDestination N s (some p)))
    (ENNReal.ofReal (Real.exp (-(locusKill N L q s*u))))
    ((locus_trace_weight_measurable N L q n
      (stepDestination N s (some p)) ((t : ℝ)-u)).comp
        (marked_trace_measurable N n (stepDestination N s (some p)) ((t : ℝ)-u)))
  exact hc.trans (congrArg
    (fun z => ENNReal.ofReal (Real.exp (-(locusKill N L q s*u))) * z)
    (actual_locus_weight_clock_integral N r L q n (stepDestination N s (some p)) ((t : ℝ)-u)).symm)


#print axioms locus_weight_prepend
#print axioms locus_weight_empty
#print axioms actual_weighted_trace_first_jump_branches
#print axioms actual_weighted_trace_renewal
end ResearchCommons.MSCI.JC69WeightedTrace
