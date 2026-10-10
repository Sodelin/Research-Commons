import G2MarkedTraceRenewal

/-!
New literal endpoint-law construction for timed-G2 restoration.
Contributor: dot (OpenAI), 6 October 2026. Uncompiled development source.
This retains the actual clock pushforward and does not assume its equality
with the source PMF; that equality remains the next analytic obligation.
-/
namespace GProgram.G2.LiteralEpochLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceLiteralClockEndpoint
open GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.MarkedTraceRenewal
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

theorem decoded_endpoint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) : Measurable (decodedEndpoint N n s) := by
  cases n with
  | zero =>
      have h : Measurable (fun b : Bool => if b then some s else none) :=
        measurable_of_countable _
      exact h.comp measurable_fst
  | succ n =>
      have hs : Measurable (fun d : Code N sample => (some d : Option (Code N sample))) := by
        intro a _
        trivial
      have hd : Measurable (fun z : Bool × ClockTrace N sample (n+1) =>
          some ((z.2 (Fin.last n)).2.2)) :=
        hs.comp (((measurable_pi_apply (Fin.last n)).comp measurable_snd).snd.snd)
      have hb : MeasurableSet {z : Bool × ClockTrace N sample (n+1) | z.1 = true} :=
        measurableSet_eq_fun measurable_fst measurable_const
      exact Measurable.ite hb hd measurable_const

noncomputable def actualEndpointLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ) :
    Measure (Option (Code N sample)) :=
  (actualMarkedTraceLaw N r n s t).map (decodedEndpoint N n s)

theorem actual_endpoint_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ) :
    IsProbabilityMeasure (actualEndpointLaw N r n s t) := by
  letI := actual_marked_trace_probability N r n s t
  exact Measure.isProbabilityMeasure_map (decoded_endpoint_measurable N n s).aemeasurable

/-- Exact identity on all clock vectors, including failure outcomes. -/
theorem actual_endpoint_eq_literal_clock_pushforward (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ) :
    actualEndpointLaw N r n s t =
      (currentPairClockMeasure N r s).map (literalClockEndpoint N n t s) := by
  rw [actualEndpointLaw,actualMarkedTraceLaw,
    Measure.map_map (decoded_endpoint_measurable N n s) (marked_trace_measurable N n s t)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall (fun c => marked_trace_endpoint_eq N n s t c)

theorem decoded_first_jump_future (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (p : Choice N s) (t : ℝ)
    (z : ℝ × (Choice N (stepDestination N s (some p)) → ℝ)) :
    decodedEndpoint N (n+1) s (firstJumpFuture N n s p t z) =
      literalClockEndpoint N n (t-z.1) (stepDestination N s (some p)) z.2 := by
  simp only [firstJumpFuture,decodedEndpoint,prepend_trace_endpoint]
  exact marked_trace_endpoint_eq N n (stepDestination N s (some p)) (t-z.1) z.2

/-- The full endpoint renewal is inherited from the derived actual marked
trace renewal, retaining the remaining-time dependence inside the map. -/
theorem actual_endpoint_first_jump_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0) :
    actualEndpointLaw N r (n+1) s (t : ℝ) =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) • Measure.dirac (some s) +
      ∑ p : Choice N s,
        (((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).restrict
          (Iic (t : ℝ))).prod (currentPairClockMeasure N r (stepDestination N s (some p)))).map
            (fun z => literalClockEndpoint N n ((t : ℝ)-z.1) (stepDestination N s (some p)) z.2) := by
  rw [actualEndpointLaw,actual_marked_trace_first_jump_renewal,
    Measure.map_add _ _ (decoded_endpoint_measurable N (n+1) s),Measure.map_smul,
    Measure.map_dirac' (decoded_endpoint_measurable N (n+1) s),
    Measure.map_finset_sum' (decoded_endpoint_measurable N (n+1) s).aemeasurable]
  simp only [decodedEndpoint,empty_trace_endpoint,if_true]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [Measure.map_map (decoded_endpoint_measurable N (n+1) s) (first_jump_future_measurable N n s p t)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall (fun z => decoded_first_jump_future N n s p t z)

#print axioms decoded_endpoint_measurable
#print axioms actual_endpoint_probability
#print axioms actual_endpoint_eq_literal_clock_pushforward
#print axioms decoded_first_jump_future
#print axioms actual_endpoint_first_jump_renewal

/-- Fubini for one actual first-winner endpoint branch. No future transition
law is substituted: its literal clock pushforward remains under the integral. -/
theorem actual_endpoint_branch_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s d : Code N sample) (p : Choice N s) (t : ℝ) :
    ((((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).restrict
        (Iic t)).prod (currentPairClockMeasure N r (stepDestination N s (some p)))).map
          (fun z => literalClockEndpoint N n (t-z.1) (stepDestination N s (some p)) z.2)) {some d} =
      ∫⁻ u in Iic t, actualEndpointLaw N r n (stepDestination N s (some p)) (t-u) {some d}
        ∂(ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)) := by
  letI : ∀ q : Choice N (stepDestination N s (some p)),
      IsProbabilityMeasure (expMeasure (choiceRate N r (stepDestination N s (some p)) q)) :=
    fun q => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r q.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r (stepDestination N s (some p))) := by
    unfold currentPairClockMeasure
    infer_instance
  have hd : MeasurableSet ({some d} : Set (Option (Code N sample))) := by trivial
  have hm : Measurable (fun z : ℝ × (Choice N (stepDestination N s (some p)) → ℝ) =>
      literalClockEndpoint N n (t-z.1) (stepDestination N s (some p)) z.2) :=
    (literal_endpoint_joint_measurable N n (stepDestination N s (some p))).comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd)
  rw [Measure.map_apply hm hd,Measure.prod_apply (hm hd)]
  apply lintegral_congr
  intro u
  rw [actual_endpoint_eq_literal_clock_pushforward,
    Measure.map_apply (literal_endpoint_measurable N n (stepDestination N s (some p)) (t-u)) hd]
  rfl

/-- Exact singleton-mass renewal, retaining every actual original choice and
its remaining-time-dependent endpoint law. -/
theorem actual_endpoint_mass_first_jump (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s d : Code N sample) (t : ℝ≥0) :
    actualEndpointLaw N r (n+1) s (t : ℝ) {some d} =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) * (if s=d then 1 else 0) +
      ∑ p : Choice N s,
        ∫⁻ u in Iic (t : ℝ), actualEndpointLaw N r n (stepDestination N s (some p)) ((t : ℝ)-u) {some d}
          ∂(ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)) := by
  rw [actual_endpoint_first_jump_renewal,Measure.add_apply,Measure.smul_apply,Measure.finsetSum_apply]
  simp only [smul_eq_mul]
  have hd : MeasurableSet ({some d} : Set (Option (Code N sample))) := by trivial
  rw [Measure.dirac_apply' _ hd]
  have hdiag : ({some d} : Set (Option (Code N sample))).indicator 1 (some s) =
      (if s=d then 1 else 0 : ℝ≥0∞) := by
    by_cases h : s=d <;> simp [h]
  rw [hdiag]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact actual_endpoint_branch_mass N r n s d p t

/-- The original winning-time measure gives the original pair-rate density
on the physical nonnegative interval. This is a density calculation, not an
assumed endpoint or source-kernel identity. -/
theorem weighted_exponential_interval_integral (a b t : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ht : 0 ≤ t) (f : ℝ → ℝ) (hf : Continuous f)
    (hfn : ∀ x ∈ Icc 0 t, 0 ≤ f x) :
    (∫⁻ x in Iic t, ENNReal.ofReal (f x) ∂(ENNReal.ofReal (b/a) • expMeasure a)) =
      ENNReal.ofReal (∫ x in 0..t, b * Real.exp (-(a*x)) * f x) := by
  rw [Measure.restrict_smul,lintegral_smul_measure]
  change ENNReal.ofReal (b/a) *
    (∫⁻ x in Iic t, ENNReal.ofReal (f x) ∂volume.withDensity (exponentialPDF a)) = _
  have hpdf : Measurable (exponentialPDF a) := (measurable_exponentialPDFReal a).ennreal_ofReal
  rw [setLIntegral_withDensity_eq_setLIntegral_mul volume
    hpdf hf.measurable.ennreal_ofReal measurableSet_Iic]
  rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ ht]
  have hz : (∫⁻ x in Iio (0 : ℝ), (exponentialPDF a * fun x => ENNReal.ofReal (f x)) x) = 0 := by
    apply setLIntegral_eq_zero measurableSet_Iio
    intro x hx
    simp [exponentialPDF_of_neg hx]
  rw [hz,zero_add]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hc : Continuous (fun x => b * Real.exp (-(a*x)) * f x) := by fun_prop
  have he : ∀ x ∈ Icc 0 t,
      ENNReal.ofReal (b/a) * ((exponentialPDF a * fun x => ENNReal.ofReal (f x)) x) =
        ENNReal.ofReal (b * Real.exp (-(a*x)) * f x) := by
    intro x hx
    rw [Pi.mul_apply,exponentialPDF_of_nonneg hx.1,← mul_assoc,← ENNReal.ofReal_mul (div_nonneg hb ha.le),
      ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg hb ha.le) (mul_nonneg ha.le (Real.exp_pos _).le))]
    congr 1
    field_simp [ha.ne'] <;> ring
  rw [setLIntegral_congr_fun measurableSet_Icc he,
    ← ofReal_integral_eq_lintegral_ofReal hc.continuousOn.integrableOn_Icc]
  · rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact mul_nonneg (mul_nonneg hb (Real.exp_pos _).le) (hfn x hx)

#print axioms actual_endpoint_branch_mass
#print axioms actual_endpoint_mass_first_jump
#print axioms weighted_exponential_interval_integral


/-- The actual endpoint's failure value has zero mass as soon as the budget
covers live original copies. Option-valued probability alone is insufficient. -/
theorem actual_endpoint_failure_null (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ)
    (hn : liveCard s ≤ n) : actualEndpointLaw N r n s t {none} = 0 := by
  have hd : MeasurableSet ({none} : Set (Option (Code N sample))) := by trivial
  rw [actualEndpointLaw,Measure.map_apply (decoded_endpoint_measurable N n s) hd]
  have h := actual_marked_trace_success_ae N r n s t hn
  rw [ae_iff] at h
  have he : (decodedEndpoint N n s) ⁻¹' {none} = {z : Bool × ClockTrace N sample n | ¬ z.1 = true} := by
    ext z
    cases hz : z.1 <;> simp [decodedEndpoint,hz]
  rw [he]
  exact h

#print axioms actual_endpoint_failure_null

open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourceEpochRenewal
open UnifiedLean.Source.SourceFiniteJumpExpansion
open scoped Matrix.Norms.Operator

/-- Exact equality to the original epoch PMF once real-merger descent makes
the supplied finite budget sufficient. The proof uses the actual-clock
renewal, original exponential density and the derived source renewal. -/
theorem actual_endpoint_mass_eq_source_kernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s d : Code N sample) (t : ℝ≥0)
    (hn : liveCard s ≤ n) :
    actualEndpointLaw N r n s (t : ℝ) {some d} = sourceTimeKernel N r t s d := by
  induction n generalizing s t with
  | zero =>
      letI := choice_empty_of_zero_live N s (by omega)
      letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
        fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
      letI : IsProbabilityMeasure (currentPairClockMeasure N r s) := by
        unfold currentPairClockMeasure
        infer_instance
      have hsrc : (sourceTimeKernel N r t s d).toReal = if s=d then 1 else 0 := by
        rw [← finite_jump_mass_eq_source_kernel N r 0 t s d hn]
        simp [finiteJumpMass,totalRate]
      rw [← ENNReal.ofReal_toReal ((sourceTimeKernel N r t s).apply_ne_top d),hsrc,
        actual_endpoint_eq_literal_clock_pushforward]
      have hf : literalClockEndpoint N 0 (t : ℝ) s = fun _ => some s := by
        funext c
        simp [literalClockEndpoint]
      rw [hf,Measure.map_const]
      have hd : MeasurableSet ({some d} : Set (Option (Code N sample))) := by trivial
      by_cases h : s=d
      · subst d
        simp [Measure.dirac_apply' _ hd]
      · simp [Measure.dirac_apply' _ hd,Pi.single_apply,h,Ne.symm h]
  | succ n ih =>
      let F (p : Choice N s) (u : ℝ) : ℝ :=
        (NormedSpace.exp (((t : ℝ)-u) • sourceGeneratorMatrix N (sample := sample) r))
          (stepDestination N s (some p)) d
      have hF (p : Choice N s) : Continuous (F p) :=
        continuous_iff_continuousAt.mpr (fun u =>
          (actual_exponential_entry_derivative N r (stepDestination N s (some p)) d t u).continuousAt)
      have hFsrc (p : Choice N s) (u : ℝ) (hu : u ≤ (t : ℝ)) :
          (sourceTimeKernel N r (Real.toNNReal ((t : ℝ)-u))
            (stepDestination N s (some p)) d).toReal = F p u := by
        rw [source_time_kernel_eq_exponential,Real.coe_toNNReal _ (sub_nonneg.mpr hu)]
      have hFnonneg (p : Choice N s) (u : ℝ) (hu : u ∈ Icc 0 (t : ℝ)) : 0 ≤ F p u := by
        rw [← hFsrc p u hu.2]
        exact ENNReal.toReal_nonneg
      let J (p : Choice N s) : ℝ :=
        ∫ u in 0..(t : ℝ), choiceRate N r s p * Real.exp (-(totalRate N r s*u)) * F p u
      have hJnonneg (p : Choice N s) : 0 ≤ J p :=
        intervalIntegral.integral_nonneg t.property (fun u hu =>
          mul_nonneg (mul_nonneg (div_pos (pairRate_pos r p.1) (by norm_num)).le
            (Real.exp_pos _).le) (hFnonneg p u hu))
      have hbranch (p : Choice N s) :
          (∫⁻ u in Iic (t : ℝ), actualEndpointLaw N r n (stepDestination N s (some p))
              ((t : ℝ)-u) {some d}
            ∂(ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s))) =
            ENNReal.ofReal (J p) := by
        have hb : liveCard (stepDestination N s (some p)) ≤ n := by
          have hcard := merger_destination_card N s p
          omega
        calc
          _ = ∫⁻ u in Iic (t : ℝ), ENNReal.ofReal (F p u)
              ∂(ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)) := by
            apply setLIntegral_congr_fun measurableSet_Iic
            intro u hu
            dsimp only
            have htime : ((Real.toNNReal ((t : ℝ)-u) : ℝ≥0) : ℝ) = (t : ℝ)-u :=
              Real.coe_toNNReal _ (sub_nonneg.mpr hu)
            have hh := ih (stepDestination N s (some p)) (Real.toNNReal ((t : ℝ)-u)) hb
            rw [htime] at hh
            rw [hh,← ENNReal.ofReal_toReal
              ((sourceTimeKernel N r (Real.toNNReal ((t : ℝ)-u)) (stepDestination N s (some p))).apply_ne_top d),
              hFsrc p u hu]
          _ = _ := weighted_exponential_interval_integral _ _ _
            (UnifiedLean.Source.SourceFirstMarkDistribution.current_pair_total_positive N r s p)
            (div_pos (pairRate_pos r p.1) (by norm_num)).le t.property (F p) (hF p) (hFnonneg p)
      rw [actual_endpoint_mass_first_jump]
      simp_rw [hbranch]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => hJnonneg p)]
      have hdiag : ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) *
          (if s=d then 1 else 0) =
          ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ))) * (if s=d then 1 else 0)) := by
        split_ifs <;> simp
      rw [hdiag,← ENNReal.ofReal_add
        (mul_nonneg (Real.exp_pos _).le (by split_ifs <;> norm_num))
        (Finset.sum_nonneg (fun p _ => hJnonneg p)),
        ← ENNReal.ofReal_toReal ((sourceTimeKernel N r t s).apply_ne_top d)]
      apply congrArg ENNReal.ofReal
      rw [source_time_kernel_eq_exponential,actual_source_exponential_renewal]
      congr 1
      have hJint (p : Choice N s) : IntervalIntegrable
          (fun u => choiceRate N r s p * Real.exp (-(totalRate N r s*u)) * F p u) volume 0 t :=
        (continuous_const.mul (by fun_prop) |>.mul (hF p)).intervalIntegrable _ _
      change (∑ p : Choice N s, ∫ u in 0..(t : ℝ),
          choiceRate N r s p * Real.exp (-(totalRate N r s*u)) * F p u) = _
      rw [← intervalIntegral.integral_finsetSum (fun p _ => hJint p)]
      apply intervalIntegral.integral_congr
      intro u _
      change (∑ p : Choice N s, choiceRate N r s p * Real.exp (-(totalRate N r s*u)) * F p u) =
        Real.exp (-(totalRate N r s*u)) * ∑ p : Choice N s, choiceRate N r s p * F p u
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      dsimp [F]
      ring

#print axioms actual_endpoint_mass_eq_source_kernel

/-- Complete Option-valued law: every genuine source state has its original
PMF mass, and the failure value has the separately proved zero mass. -/
theorem actual_endpoint_law_eq_source_kernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0)
    (hn : liveCard s ≤ n) :
    actualEndpointLaw N r n s (t : ℝ) = (sourceTimeKernel N r t s).toMeasure.map some := by
  letI : MeasurableSingletonClass (Option (Code N sample)) := ⟨fun _ => by trivial⟩
  have hm : Measurable (some : Code N sample → Option (Code N sample)) := by
    intro a _
    trivial
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply hm (measurableSet_singleton z)]
  cases z with
  | none =>
      rw [actual_endpoint_failure_null N r n s t hn]
      simp
  | some d =>
      rw [actual_endpoint_mass_eq_source_kernel N r n s d t hn]
      have he : (some : Code N sample → Option (Code N sample)) ⁻¹' {some d} = {d} := by
        ext x
        simp
      rw [he,PMF.toMeasure_apply_singleton _ _ (by trivial)]

/-- The same literal original clock compiler, at the actual supplied copy
carrier cap, realizes the complete original epoch PMF. No conditioning,
replacement clocks or rowwise endpoint fitting occurs. -/
theorem original_copy_cap_literal_epoch_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) :
    (currentPairClockMeasure N r s).map (literalClockEndpoint N (Fintype.card Copy) t s) =
      (sourceTimeKernel N r t s).toMeasure.map some := by
  rw [← actual_endpoint_eq_literal_clock_pushforward]
  exact actual_endpoint_law_eq_source_kernel N r _ s t (Finset.card_le_univ s.val.live)

#print axioms actual_endpoint_law_eq_source_kernel
#print axioms original_copy_cap_literal_epoch_law

end GProgram.G2.LiteralEpochLaw
