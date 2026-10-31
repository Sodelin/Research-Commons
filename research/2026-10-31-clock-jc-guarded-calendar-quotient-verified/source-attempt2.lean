import ResearchCommons.MSCI.JC69CalendarObservationKernel

/-! Guarded-root full calendar observation quotient. UNCOMPILED candidate.
Dot (OpenAI), 31 October 2026. The guard is only an extension off actual
terminal support. The original initialized law and initial potential remain.
No finite-S encoding, boundary-position count or denominator is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69GuardedCalendarQuotient
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.NativeParentRouting
open GProgram.G2.ActualCalendarTrace GProgram.G2.LiteralMarkedClockTrace
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69EndpointWeight
open ResearchCommons.MSCI.JC69RootResolvent ResearchCommons.MSCI.JC69UnorderedContinuation
open ResearchCommons.MSCI.JC69WeightedCalendar ResearchCommons.MSCI.JC69FixedBankBoundary
open ResearchCommons.MSCI.JC69CalendarObservationKernel ResearchCommons.MSCI.JC69ObservedFourier
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Only the coded interface to unchanged original holding/merger register
retention. No erased bank or fresh routing draw is introduced. -/
lemma destination_register (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Option (Choice N s)) :
    (state (stepDestination N s p)).register = (state s).register := by
  cases p <;> rfl

lemma step_register_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (sourceStep N r s).map (fun d => (state d).register) = PMF.pure ((state s).register) := by
  rw [sourceStep,PMF.map_comp]
  have he : (fun d : Code N sample => (state d).register) ∘ stepDestination N s =
      Function.const (Option (Choice N s)) ((state s).register) := by
    funext p
    exact destination_register N s p
  rw [he,PMF.map_const]

lemma iteration_register_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : ℕ) (s : Code N sample) :
    (sourceIteration N r k s).map (fun d => (state d).register) =
      PMF.pure ((state s).register) := by
  induction k generalizing s with
  | zero => simp [sourceIteration,PMF.pure_map]
  | succ k ih =>
      rw [sourceIteration,PMF.map_bind]
      simp_rw [ih]
      change (sourceStep N r s).bind (PMF.pure ∘ (fun d => (state d).register)) = _
      rw [PMF.bind_pure_comp,step_register_law]

/-- Original Poisson/source-step interval kernel, with the original rate bank. -/
theorem actual_interval_register_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (h : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r h s).map (fun d => (state d).register) =
      PMF.pure ((state s).register) := by
  simp only [sourceTimeKernel,PMF.map_bind,iteration_register_law,PMF.bind_const]

lemma program_step_register_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) :
    (sourceProgramStep N r op s).map (fun d => (state d).register) =
      PMF.pure ((state s).register) := by
  cases op with
  | interval h => exact actual_interval_register_law N r h s
  | boundary b => exact actual_boundary_register_law N b s

lemma program_step_support_register (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s d : Code N sample)
    (hd : d ∈ (sourceProgramStep N r op s).support) :
    (state d).register = (state s).register := by
  have hm : (state d).register ∈
      ((sourceProgramStep N r op s).map (fun z => (state z).register)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨d,hd,rfl⟩
  rw [program_step_register_law] at hm
  simpa using hm

/-- Auxiliary extension off physical terminal support, NOT a replacement
of the original observable. On actual ancestral endpoints it is rootWeight. -/
def guardedRoot (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base) (s : Code N sample) : ℝ≥0∞ :=
  if AncestralRoot N s then rootWeight N r L q s else 0

/-- Reuses the accepted ancestry transfer and actual complete-root quotient. -/
theorem guarded_root_observation [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (s t : Code N sample)
    (hobs : observeCode N s = observeCode N t) :
    guardedRoot N r L q s = guardedRoot N r L q t := by
  by_cases hs : AncestralRoot N s
  · have ht := observation_ancestralRoot N s t hobs hs
    simp only [guardedRoot,if_pos hs,if_pos ht]
    exact actual_root_weight_observation N r L q hbal s t hobs hs
  · have ht : ¬ AncestralRoot N t := fun ht =>
        hs (observation_ancestralRoot N t s hobs.symm ht)
    simp [guardedRoot,hs,ht]

/-- Choose only from nonempty admitted observation fibres. The re-banked
representative need not be reachable; the equality assumption is the induction
hypothesis on the actual auxiliary future, not a postulated source quotient. -/
lemma exists_bank_readout (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → ℝ≥0∞)
    (hf : ∀ s t, observeCode N s = observeCode N t →
      (state s).register = (state t).register → f s = f t) (sigma : V → Bool) :
    ∃ F : BlockPopulationObservation Copy V E → ℝ≥0∞,
      ∀ d : Code N sample, (state d).register = sigma → f d = F (observeCode N d) := by
  let F : BlockPopulationObservation Copy V E → ℝ≥0∞ := fun o =>
    if h : ∃ d : Code N sample, observeCode N d = o then
      f (reBank N (Classical.choose h) sigma) else 0
  refine ⟨F,?_⟩
  intro d hd
  have h : ∃ e : Code N sample, observeCode N e = observeCode N d := ⟨d,rfl⟩
  dsimp only [F]
  rw [dif_pos h]
  have hr := actual_reBank_observation N (Classical.choose h) sigma
  apply hf
  · exact (Classical.choose_spec h).symm.trans hr.1.symm
  · exact hd.trans hr.2.symm

/-- Full finite-calendar auxiliary future factors through the SAME current
observation and SAME bank, derived by actual weighted backward induction. -/
theorem actual_guarded_calendar_quotient [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (ops : List (ProgramStep N))
    (s t : Code N sample) (hobs : observeCode N s = observeCode N t)
    (hreg : (state s).register = (state t).register) :
    calendarValue N r L q (guardedRoot N r L q) ops s =
      calendarValue N r L q (guardedRoot N r L q) ops t := by
  induction ops generalizing s t with
  | nil => exact guarded_root_observation N r L q hbal s t hobs
  | cons op ops ih =>
      let f : Code N sample → ℝ≥0∞ := calendarValue N r L q (guardedRoot N r L q) ops
      obtain ⟨F,hF⟩ := exists_bank_readout N f (fun u v ho hr => ih u v ho hr) ((state s).register)
      have hu (u : Code N sample) (hbank : (state u).register = (state s).register) :
          calendarValue N r L q (guardedRoot N r L q) (op::ops) u =
            ∑ target : BlockPopulationObservation Copy V E,
              segmentObservedWeight N r L q op u target * F target := by
        rw [calendarValue,← actual_observation_readout_sum]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hz : sourceProgramStep N r op u d = 0
        · rw [actual_fibre_zero_of_source_zero N r L q op u d hz,zero_mul,zero_mul]
        · have hd := program_step_support_register N r op u d ((PMF.mem_support_iff _ _).mpr hz)
          exact congrArg (segmentFibreWeight N r L q op u d * ·) (hF d (hd.trans hbank))
      rw [hu s rfl,hu t hreg.symm]
      apply Finset.sum_congr rfl
      intro target _
      rw [actual_segment_observation_quotient N r L q op s t hobs hreg target]

/-- Existing original endpoint law and initialized ancestry support make the
auxiliary guard true almost everywhere; no new terminal support is assumed. -/
theorem actual_initialized_ancestry_ae (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    let ops := compiledCalendarProgram N C H gamma common
    let s := initialCode N sample register
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s, AncestralRoot N (calendarEnd N ops s past) := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  let p := sourceProgram N r ops s
  have hs : ∀ᵐ d ∂p.toMeasure, d ∈ p.support := by
    rw [← p.restrict_toMeasure_support]
    exact ae_restrict_mem p.support_countable.measurableSet
  have ha : ∀ᵐ d ∂p.toMeasure, AncestralRoot N d := by
    filter_upwards [hs] with d hd
    exact initialized_original_calendar_ancestral_support N C sample register H gamma common r hd
  change ∀ᵐ d ∂(sourceProgram N r ops s).toMeasure, AncestralRoot N d at ha
  rw [← actual_calendar_endpoint_law N r ops s] at ha
  exact ae_of_ae_map (calendar_end_measurable N ops s).aemeasurable ha

/-- The auxiliary guarded value equals the ORIGINAL value only where its
physical source support supplies the guard. Initialization is not modified. -/
theorem actual_initialized_guarded_value (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) :
    let ops := compiledCalendarProgram N C H gamma common
    let s := initialCode N sample register
    calendarValue N r L q (rootWeight N r L q) ops s =
      calendarValue N r L q (guardedRoot N r L q) ops s := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  change calendarValue N r L q (rootWeight N r L q) ops s =
    calendarValue N r L q (guardedRoot N r L q) ops s
  rw [← actual_calendar_weighted_recursion N r L q (rootWeight N r L q) ops s,
    ← actual_calendar_weighted_recursion N r L q (guardedRoot N r L q) ops s]
  apply lintegral_congr_ae
  filter_upwards [actual_initialized_ancestry_ae N C sample register H gamma common r] with past hp
  simp only [guardedRoot,if_pos hp]

/-- Original full-labelled Fourier observable, not a guarded physical law.
The initial forest-potential factor is retained verbatim. -/
theorem actual_observed_guarded_calendar [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (hbal : ∀ j, ∑ x, q j x = 0) :
    observedFourier L N C sample register H gamma common r q =
      (initialPotentialWeight N C sample register L q *
        calendarValue N r L q (guardedRoot N r L q)
          (compiledCalendarProgram N C H gamma common)
          (initialCode N sample register)).toReal := by
  rw [actual_observed_calendar_recursion N C sample register H gamma common r L q hbal,
    actual_initialized_guarded_value N C sample register H gamma common r L q]

#print axioms actual_interval_register_law
#print axioms guarded_root_observation
#print axioms actual_guarded_calendar_quotient
#print axioms actual_initialized_ancestry_ae
#print axioms actual_initialized_guarded_value
#print axioms actual_observed_guarded_calendar
end ResearchCommons.MSCI.JC69GuardedCalendarQuotient
