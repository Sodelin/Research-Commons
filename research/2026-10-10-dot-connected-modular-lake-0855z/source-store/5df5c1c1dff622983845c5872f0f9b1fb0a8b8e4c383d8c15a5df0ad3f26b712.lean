import UpperRateNaturalHistory
import NaturalPastCompleteObservation

/-! dot (OpenAI), 9 October 2026. Candidate source-bound completion assembly.
The same actual ancestral completion is applied to both finite-calendar laws.
No time cutoff or independent replacement of an old tag/register is made. -/
namespace DotG6.UpperRateCompleteObservation
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source MeasureTheory GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.G6.ProgramPrefix UnifiedLean.G6.HistoryPrefix
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.ResidualProgram
open UnifiedLean.G6.BinHistory
open GProgram.G2.SourceFiniteHistory
open CloudG3.ActualCalendarEndpointHistory CloudG6.NaturalCalendarPastAdmission
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open CloudG6.NaturalPastCompleteObservation CloudG3.ActualObservationCutRefinement
open CloudG3.ActualCutJointLaw
open CloudG3.CompleteCalendarJointLaw
open GProgram.G2.ActualCalendarTrace
open GProgram.G2.ChronologicalPathReadout
open UnifiedLean.Source.SourceNaturalInitialization
open DotG6.UpperRateNaturalHistory
open scoped Classical NNReal ENNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- History domination survives an arbitrary SAME stochastic continuation. -/
theorem initialized_common_finish {O : Type*}
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (mass : ProgramStep N → ℝ≥0∞)
    (target : ProgramStep N → Code N sample → PMF (Code N sample))
    (hstep : ∀ op ∈ ops, ∀ s d, mass op * finiteProgramStep N r K op s d ≤ target op s d)
    (initial : PMF (Code N sample))
    (finish : (Code N sample × (Fin ops.length → Code N sample)) → PMF O) (o : O) :
    (ops.map mass).prod *
      ((initial.bind (fun s =>
        (historyLaw (finiteProgramStep N r K) ops s).map (Prod.mk s))).bind finish) o ≤
      ((initial.bind (fun s =>
        (historyLaw target ops s).map (Prod.mk s))).bind finish) o := by
  apply (show (ops.map mass).prod * _ ≤ _ from ?_)
  simpa only [mul_one] using bind_scaled_domination
    (initial.bind (fun s => (historyLaw target ops s).map (Prod.mk s)))
    (initial.bind (fun s => (historyLaw (finiteProgramStep N r K) ops s).map (Prod.mk s)))
    finish finish (ops.map mass).prod 1
    (fun z => by
      simpa only [one_mul] using bind_scaled_domination initial initial
        (fun s => (historyLaw target ops s).map (Prod.mk s))
        (fun s => (historyLaw (finiteProgramStep N r K) ops s).map (Prod.mk s))
        1 (ops.map mass).prod (fun _ => by simp)
        (fun s z => map_scaled_domination _ _ _ (history_scaled _ _ _ ops hstep s)
          (Prod.mk s) z) z)
    (fun _ _ => by simp) o

theorem initialized_finish_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r rhat : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (ops : List (ProgramStep N)) (hb : ∀ op ∈ ops, Budget (Copy := Copy) N r b K op)
    (initial : PMF (Code N sample))
    (finish : (Code N sample × (Fin ops.length → Code N sample)) → PMF O) :
    pmfTV ((initializedEndpointLaw N r ops initial).bind finish)
      ((initializedProxy N rhat b K ops initial).bind finish) ≤
      1 - ((ops.map (commonMass (Copy := Copy) N r b K ell u)).prod).toReal := by
  apply common_pmf_tv _ _
    ((initial.bind (fun s => (historyLaw (finiteProgramStep N r K) ops s).map (Prod.mk s))).bind finish)
  · exact initialized_common_finish N r K ops _ _
      (fun op hop s d => source_step_common N r b K ell u hell1 hu1 op (hb op hop) s d)
      initial finish
  · exact initialized_common_finish N r K ops _ _
      (fun op hop s d => proxy_step_common N r rhat b K ell u hell hell1 hu1 hlo hup
        op (hb op hop) s d) initial finish

open CloudG3.ActualCalendarCutContext

/-- Full actual completed-calendar observation. Its tail is the existing
actual ancestral kernel; only the finite-calendar count/rate bank is approximated.
The input must be the original compiled calendar, with legal fixed-bin cuts. -/
theorem actual_natural_complete_proxy_tv {Tag O : Type*}
    [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag] [Fintype O]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (ell u : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = ops)
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C))
    (hb : ∀ op ∈ physicalOps N word, Budget (Copy := Copy) N r b K op)
    (cut : ℝ) (tailTag : Tag)
    (hoff : cut ≤ firstOriginalDate N C + (programDuration N ops : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag)
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) :
    pmfTV ((naturalCompletedJoint N C sample p r bin hbin ops).map readout)
      ((((initializedProxy N rhat b K (physicalOps N word)
        (naturalInitialCodeLaw N sample p)).map (fun a =>
          endpointHistoryReadout N word a.1
            (fun x y => bin (leafAgeMatrix N C sample x y)) a.2)).bind
              (jointTailKernel N r tailTag)).map readout) ≤
      1 - (((physicalOps N word).map
        (commonMass (Copy := Copy) N r b K ell u)).prod).toReal := by
  have hcomplete : naturalCompletedJoint N C sample p r bin hbin ops =
      (naturalPastJoint N C sample p r bin hbin ops).bind (jointTailKernel N r tailTag) := by
    simpa only [List.append_nil, calendar_joint_nil, PMF.pure_bind] using
      actual_natural_completed_eq_past_suffix N C sample H p common r bin hbin
        ops [] (by simpa using hwhole) cut tailTag (by simpa using hoff) htail
  rw [hcomplete, actual_natural_past_endpoint_history N C sample p r bin hbin ops word href hword]
  simpa only [PMF.bind_map, PMF.map_bind, Function.comp_def] using
    initialized_finish_tv N r rhat b K ell u hell hell1 hu1 hlo hup
      (physicalOps N word) hb (naturalInitialCodeLaw N sample p)
      (fun a => (jointTailKernel N r tailTag
        (endpointHistoryReadout N word a.1
          (fun x y => bin (leafAgeMatrix N C sample x y)) a.2)).map readout)

#print axioms initialized_common_finish
#print axioms initialized_finish_tv
#print axioms actual_natural_complete_proxy_tv
end DotG6.UpperRateCompleteObservation
