import UnifiedLean.G6.UpperRateSourceCommon
import NaturalCalendarPastAdmission

/-!
Contributor: dot (OpenAI), 9 October 2026.
Candidate source-bound assembly, not yet compiled or independently reviewed.
One original rate bank and one comparison bank are used across the entire
history. Original boundary kernels and once-drawn initialization are retained.
The approximation is a normalized count/rate proxy, not a new biological source.
-/
namespace DotG6.UpperRateNaturalHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source MeasureTheory
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.G6.ProgramPrefix UnifiedLean.G6.HistoryPrefix
open UnifiedLean.G6.UpperRateSourceCommon UnifiedLean.G6.UpperMeanCommon
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.ResidualProgram
open GProgram.G2.SourceFiniteHistory
open CloudG3.ActualCalendarEndpointHistory CloudG6.NaturalCalendarPastAdmission
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open scoped Classical NNReal ENNReal

/-- General product domination of the SAME complete endpoint history. -/
theorem history_scaled {S Op : Type*} (P Q : Op → S → PMF S)
    (mass : Op → ℝ≥0∞) (ops : List Op)
    (hstep : ∀ op ∈ ops, ∀ s d, mass op * Q op s d ≤ P op s d)
    (s : S) (h : Fin ops.length → S) :
    (ops.map mass).prod * historyLaw Q ops s h ≤ historyLaw P ops s h := by
  induction ops generalizing s with
  | nil => simp only [List.map_nil, List.prod_nil, one_mul, historyLaw, le_refl]
  | cons op ops ih =>
      change (mass op * (ops.map mass).prod) *
        ((Q op s).bind (fun d => (historyLaw Q ops d).map (Fin.cons d))) h ≤
        ((P op s).bind (fun d => (historyLaw P ops d).map (Fin.cons d))) h
      apply bind_scaled_domination _ _ _ _ _ _ (hstep op (by simp) s)
      intro d z
      exact map_scaled_domination _ _ _
        (fun t => ih (fun q hq => hstep q (List.mem_cons_of_mem op hq)) d t)
        (fun t : Fin ops.length → S =>
          (Fin.cons d t : Fin (ops.length+1) → S)) z

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def proxyStep (N : RootedBinary V E X) {sample : Copy → X}
    (rhat : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ) :
    ProgramStep N → Code N sample → PMF (Code N sample)
  | .interval t, s => upperRateResidualSource N rhat (b t) K s
  | .boundary k, s => sourceProgramStep N rhat (.boundary k) s

noncomputable def commonMass (N : RootedBinary V E X)
    (r : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u : ℝ) :
    ProgramStep N → ℝ≥0∞
  | .interval t => ENNReal.ofReal
      (upperCommonMass (globalClockRate (Copy := Copy) r * t) (b t) K) *
      (ENNReal.ofReal (ell/u))^K
  | .boundary _ => 1

noncomputable def Budget (N : RootedBinary V E X) (r : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) : ProgramStep N → Prop
  | .interval t => globalClockRate (Copy := Copy) r * t ≤ b t ∧
      2 * (b t : ℝ) ≤ (K : ℝ)+2
  | .boundary _ => True

theorem source_step_common (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u : ℝ)
    (hell1 : ell ≤ 1) (hu1 : 1 ≤ u) (op : ProgramStep N)
    (hb : Budget (Copy := Copy) N r b K op) (s d : Code N sample) :
    commonMass (Copy := Copy) N r b K ell u op * finiteProgramStep N r K op s d ≤
      sourceProgramStep N r op s d := by
  cases op with
  | interval t => exact actual_interval_common_domination N r t (b t) hb.1 K s d hb.2 ell u hell1 hu1
  | boundary k => simp only [commonMass, one_mul]; exact le_rfl

theorem proxy_step_common (N : RootedBinary V E X) {sample : Copy → X}
    (r rhat : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (op : ProgramStep N) (hb : Budget (Copy := Copy) N r b K op)
    (s d : Code N sample) :
    commonMass (Copy := Copy) N r b K ell u op * finiteProgramStep N r K op s d ≤
      proxyStep N rhat b K op s d := by
  cases op with
  | interval t =>
      exact numerical_interval_common_domination N r rhat t (b t) hb.1 K s d
        ell u hell hell1 hu1 hlo hup
  | boundary k => simp only [commonMass, one_mul]; exact le_rfl

/-- Preserve the initial state as well as every subsequent endpoint. -/
noncomputable def initializedProxy (N : RootedBinary V E X) {sample : Copy → X}
    (rhat : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ)
    (ops : List (ProgramStep N)) (initial : PMF (Code N sample)) :=
  initial.bind (fun s => (historyLaw (proxyStep N rhat b K) ops s).map (Prod.mk s))

/-- Derived full joint-readout bound. No desired history/source-law premise. -/
theorem initialized_history_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r rhat : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (ops : List (ProgramStep N))
    (hb : ∀ op ∈ ops, Budget (Copy := Copy) N r b K op)
    (initial : PMF (Code N sample))
    (readout : (Code N sample × (Fin ops.length → Code N sample)) → O) :
    pmfTV ((initializedEndpointLaw N r ops initial).map readout)
      ((initializedProxy N rhat b K ops initial).map readout) ≤
      1 - ((ops.map (commonMass (Copy := Copy) N r b K ell u)).prod).toReal := by
  let mass := (ops.map (commonMass (Copy := Copy) N r b K ell u)).prod
  let reference := initial.bind (fun s =>
    (historyLaw (finiteProgramStep N r K) ops s).map (Prod.mk s))
  apply common_pmf_tv _ _ (reference.map readout) mass
  · apply map_scaled_domination
    intro z
    simpa only [one_mul, reference, initializedEndpointLaw, initializedProxy] using bind_scaled_domination initial initial
      (fun s => (sourceHistoryLaw N r ops s).map (Prod.mk s))
      (fun s => (historyLaw (finiteProgramStep N r K) ops s).map (Prod.mk s)) 1 mass
      (fun _ => by simp)
      (fun s z => map_scaled_domination _ _ _
        (history_scaled _ _ _ ops (fun op hop s d =>
          source_step_common N r b K ell u hell1 hu1 op (hb op hop) s d) s)
        (Prod.mk s) z) z
  · apply map_scaled_domination
    intro z
    simpa only [one_mul, reference, initializedEndpointLaw, initializedProxy] using bind_scaled_domination initial initial
      (fun s => (historyLaw (proxyStep N rhat b K) ops s).map (Prod.mk s))
      (fun s => (historyLaw (finiteProgramStep N r K) ops s).map (Prod.mk s)) 1 mass
      (fun _ => by simp)
      (fun s z => map_scaled_domination _ _ _
        (history_scaled _ _ _ ops (fun op hop s d =>
          proxy_step_common N r rhat b K ell u hell hell1 hu1 hlo hup op (hb op hop) s d) s)
        (Prod.mk s) z) z

open GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler
open CloudG3.ActualObservationCutRefinement
open UnifiedLean.G6.BinHistory

/-- Same original initialized clock past, including all old bins and the
once-drawn register, compared with ONE shared-bank finite count proxy.
Chronology/refinement are explicit physical contracts, not a target-law oracle. -/
theorem actual_natural_past_proxy_tv {Tag : Type*}
    [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (p : HybridProbabilities N) (r rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C))
    (hb : ∀ op ∈ physicalOps N word, Budget (Copy := Copy) N r b K op) :
    pmfTV (naturalPastJoint N C sample p r bin hbin ops)
      ((initializedProxy N rhat b K (physicalOps N word)
        (naturalInitialCodeLaw N sample p)).map (fun a =>
          endpointHistoryReadout N word a.1
            (fun x y => bin (leafAgeMatrix N C sample x y)) a.2)) ≤
      1 - (((physicalOps N word).map
        (commonMass (Copy := Copy) N r b K ell u)).prod).toReal := by
  rw [actual_natural_past_endpoint_history N C sample p r bin hbin ops word href hword]
  exact initialized_history_tv N r rhat b K ell u hell hell1 hu1 hlo hup
    (physicalOps N word) hb (naturalInitialCodeLaw N sample p) _

#print axioms history_scaled
#print axioms initialized_history_tv
#print axioms actual_natural_past_proxy_tv
end DotG6.UpperRateNaturalHistory
