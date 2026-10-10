import OriginalInheritanceRetuning

/-! dot (OpenAI), 9 October 2026. Full rate/count/inheritance proxy assembly
for the same original finite tagged calendar. Original parameters are shared
across every occurrence and initial COMMON registers are drawn only once. -/
namespace DotG6.SharedBankNaturalProxy
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source MeasureTheory GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.G6.ProgramPrefix UnifiedLean.G6.HistoryPrefix UnifiedLean.G6.FiniteProbability
open UnifiedLean.G6.ResidualProgram UnifiedLean.G6.UpperRateSourceCommon
open UnifiedLean.G6.InheritanceBankCommon
open GProgram.G2.SourceFiniteHistory
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open CloudG6.NaturalCalendarPastAdmission CloudG3.ActualCalendarEndpointHistory
open CloudG3.ActualObservationCutRefinement
open DotG6.UpperRateNaturalHistory DotG6.OriginalInheritanceRetuning
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def allBankProxyStep (N : RootedBinary V E X) {sample : Copy → X}
    (phat : HybridProbabilities N) (rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) : ProgramStep N → Code N sample → PMF (Code N sample)
  | .interval t,s => upperRateResidualSource N rhat (b t) K s
  | .boundary k,s => boundaryKernel N (tuneBoundary N phat k) s

noncomputable def allBankMass (N : RootedBinary V E X) (r : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u beta : ℝ) : ProgramStep N → ℝ≥0∞
  | .interval t => commonMass (Copy := Copy) N r b K ell u (.interval t)
  | .boundary k => inheritanceMass (Copy := Copy) N beta (.boundary k)

lemma inheritance_mass_le_one (N : RootedBinary V E X) (beta : ℝ)
    (hbeta1 : beta ≤ 1) (k : BoundaryOperation N) :
    inheritanceMass (Copy := Copy) N beta (.boundary k) ≤ 1 := by
  cases k <;> simp only [inheritanceMass, le_refl]
  exact Left.pow_le_one_of_le (by simpa using ENNReal.ofReal_le_ofReal hbeta1) _

lemma source_step_all_common (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u beta : ℝ)
    (hell1 : ell ≤ 1) (hu1 : 1 ≤ u) (hbeta1 : beta ≤ 1)
    (op : ProgramStep N) (hb : Budget (Copy := Copy) N r b K op) (s d : Code N sample) :
    allBankMass (Copy := Copy) N r b K ell u beta op * finiteProgramStep N r K op s d ≤
      sourceProgramStep N r op s d := by
  cases op with
  | interval t => exact source_step_common N r b K ell u hell1 hu1 (.interval t) hb s d
  | boundary k =>
      change inheritanceMass (Copy := Copy) N beta (.boundary k) * boundaryKernel N k s d ≤ _
      simpa only [one_mul, sourceProgramStep] using mul_le_mul' (inheritance_mass_le_one N beta hbeta1 k) (le_refl (boundaryKernel N k s d))

lemma proxy_step_all_common (N : RootedBinary V E X) {sample : Copy → X}
    (p phat : HybridProbabilities N) (r rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u beta : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (htrue : ∀ h, beta * p.gamma h ≤ phat.gamma h)
    (hfalse : ∀ h, beta * (1-p.gamma h) ≤ 1-phat.gamma h)
    (op : ProgramStep N) (hb : Budget (Copy := Copy) N r b K op)
    (ha : aligned N p op) (s d : Code N sample) :
    allBankMass (Copy := Copy) N r b K ell u beta op * finiteProgramStep N r K op s d ≤
      allBankProxyStep N phat rhat b K op s d := by
  cases op with
  | interval t => exact proxy_step_common N r rhat b K ell u hell hell1 hu1 hlo hup (.interval t) hb s d
  | boundary k => exact tuned_boundary_lower N p phat beta hbeta hbeta1 htrue hfalse k ha s d

/-- Initial state and every endpoint stay joint before a single stochastic finish. -/
noncomputable def initialHistory {S Op : Type*} (P : Op → S → PMF S)
    (ops : List Op) (initial : PMF S) :=
  initial.bind (fun s => (historyLaw P ops s).map (Prod.mk s))

theorem initial_history_finish_domination {S Op O : Type*}
    (P Q : Op → S → PMF S) (ops : List Op) (mass : Op → ℝ≥0∞)
    (hstep : ∀ op ∈ ops, ∀ s d, mass op * Q op s d ≤ P op s d)
    (initial target : PMF S) (mu : ℝ≥0∞)
    (hinit : ∀ s, mu * initial s ≤ target s)
    (finish : (S × (Fin ops.length → S)) → PMF O) (o : O) :
    (mu * (ops.map mass).prod) * (initialHistory Q ops initial |>.bind finish) o ≤
      (initialHistory P ops target |>.bind finish) o := by
  simpa only [mul_one] using bind_scaled_domination
    (initialHistory P ops target) (initialHistory Q ops initial) finish finish
    (mu * (ops.map mass).prod) 1
    (fun z => bind_scaled_domination target initial
      (fun s => (historyLaw P ops s).map (Prod.mk s))
      (fun s => (historyLaw Q ops s).map (Prod.mk s)) mu (ops.map mass).prod hinit
      (fun s z => map_scaled_domination _ _ _ (history_scaled P Q mass ops hstep s)
        (Prod.mk s) z) z)
    (fun _ _ => by simp) o

noncomputable def initialMass (N : RootedBinary V E X) (beta : ℝ) : ℝ≥0∞ :=
  ∏ _h : Hybrid N, ENNReal.ofReal beta

lemma initial_mass_le_one (N : RootedBinary V E X) (beta : ℝ) (hbeta1 : beta ≤ 1) :
    initialMass N beta ≤ 1 := by
  apply Finset.prod_le_one
  · intro h _
    exact zero_le
  · intro h _
    simpa using ENNReal.ofReal_le_ofReal hbeta1

theorem initialized_all_bank_finish_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) (sample : Copy → X)
    (p phat : HybridProbabilities N) (r rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u beta : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (htrue : ∀ h, beta * p.gamma h ≤ phat.gamma h)
    (hfalse : ∀ h, beta * (1-p.gamma h) ≤ 1-phat.gamma h)
    (ops : List (ProgramStep N))
    (hb : ∀ op ∈ ops, Budget (Copy := Copy) N r b K op)
    (ha : ∀ op ∈ ops, aligned N p op)
    (finish : (Code N sample × (Fin ops.length → Code N sample)) → PMF O) :
    pmfTV ((initializedEndpointLaw N r ops (naturalInitialCodeLaw N sample p)).bind finish)
      ((initialHistory (allBankProxyStep N phat rhat b K) ops
        (naturalInitialCodeLaw N sample phat)).bind finish) ≤
      1 - (initialMass N beta * (ops.map (allBankMass (Copy := Copy) N r b K ell u beta)).prod).toReal := by
  apply common_pmf_tv _ _
    ((initialHistory (finiteProgramStep N r K) ops (naturalInitialCodeLaw N sample p)).bind finish)
  · exact initial_history_finish_domination _ _ ops _
      (fun op hop s d => source_step_all_common N r b K ell u beta hell1 hu1 hbeta1 op (hb op hop) s d)
      _ _ (initialMass N beta)
      (fun s => by simpa only [one_mul] using
        mul_le_mul' (initial_mass_le_one N beta hbeta1) (le_refl ((naturalInitialCodeLaw N sample p) s))) finish
  · exact initial_history_finish_domination _ _ ops _
      (fun op hop s d => proxy_step_all_common N p phat r rhat b K ell u beta
        hell hell1 hu1 hlo hup hbeta hbeta1 htrue hfalse op (hb op hop) (ha op hop) s d)
      _ _ (initialMass N beta)
      (actual_natural_initial_code_bank_lower N sample p phat (fun _ => beta)
        (fun _ => hbeta) htrue hfalse) finish

open CloudG3.ActualCutJointLaw

/-- Rate, count and inheritance errors now concern the actual natural finite
clock/bin record. Alignment is derived from the original compiled calendar
and legal cut refinement, not supplied as a desired kernel/law assumption. -/
theorem actual_natural_all_bank_proxy_tv {Tag : Type*}
    [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p phat : HybridProbabilities N)
    (common : Hybrid N → Bool) (r rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u beta : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (htrue : ∀ h, beta * p.gamma h ≤ phat.gamma h)
    (hfalse : ∀ h, beta * (1-p.gamma h) ≤ 1-phat.gamma h)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = ops)
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C))
    (hb : ∀ op ∈ physicalOps N word, Budget (Copy := Copy) N r b K op) :
    pmfTV (naturalPastJoint N C sample p r bin hbin ops)
      ((initialHistory (allBankProxyStep N phat rhat b K) (physicalOps N word)
        (naturalInitialCodeLaw N sample phat)).map (fun a =>
          endpointHistoryReadout N word a.1
            (fun x y => bin (leafAgeMatrix N C sample x y)) a.2)) ≤
      1 - (initialMass N beta * ((physicalOps N word).map
        (allBankMass (Copy := Copy) N r b K ell u beta)).prod).toReal := by
  have ha : ∀ op ∈ physicalOps N word, aligned N p op :=
    refinement_aligned N p href (by rw [← hwhole]; exact compiled_calendar_aligned N C H p common)
  rw [actual_natural_past_endpoint_history N C sample p r bin hbin ops word href hword]
  simpa only [PMF.map, Function.comp_def] using
    initialized_all_bank_finish_tv N sample p phat r rhat b K ell u beta
      hell hell1 hu1 hlo hup hbeta hbeta1 htrue hfalse (physicalOps N word) hb ha
      (fun a => PMF.pure (endpointHistoryReadout N word a.1
        (fun x y => bin (leafAgeMatrix N C sample x y)) a.2))

#print axioms initialized_all_bank_finish_tv
#print axioms actual_natural_all_bank_proxy_tv
end DotG6.SharedBankNaturalProxy
