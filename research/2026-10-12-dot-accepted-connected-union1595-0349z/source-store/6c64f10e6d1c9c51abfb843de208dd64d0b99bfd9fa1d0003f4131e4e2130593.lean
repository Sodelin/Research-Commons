import SharedBankCompleteProxy
import NaturalAncestralCutExtension

/-! dot (OpenAI), 9 October 2026. Original-source finite-bin proxy through an arbitrary finite last cut.
The original completed law is preserved by exposing its same ancestral process. -/
namespace DotG6.ArbitraryCutSharedBankProxy
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source MeasureTheory GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceEpochSemigroup
open UnifiedLean.Source.SourceCalendarPhysicalSupport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.G6.AncestralRateFree UnifiedLean.G6.FiniteProbability
open GProgram.G2.SourceFiniteHistory GProgram.G2.ChronologicalPathReadout
open CloudG3.ActualCutJointLaw CloudG3.ActualCalendarCutContext
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualObservationCutRefinement
open CloudG3.CompleteCalendarJointLaw
open CloudG6.PrivateSeedFactorization CloudG6.NaturalCalendarPastAdmission
open CloudG6.NaturalPastCompleteObservation
open DotG6.UpperRateNaturalHistory DotG6.UpperRateProxySupport
open DotG6.OriginalInheritanceRetuning DotG6.SharedBankNaturalProxy
open DotG6.SharedBankCompleteProxy
open UnifiedLean.G6.NaturalAncestralCutExtension
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

variable {Tag : Type*} [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

theorem extended_proxy_ancestral_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p phat : HybridProbabilities N) (common : Hybrid N → Bool) (rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0)
    (bin : ℝ → Tag) (ops : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = ops)
    (t : ℝ≥0) (word : List (ProgramStep N × Tag))
    (href : CutRefines N (ops ++ [(ProgramStep.interval (N := N) t)]) (physicalOps N word))
    (q : TaggedEndpoint (Tag := Tag) N sample)
    (hq : q ∈ (allBankNaturalJoint N C sample phat rhat b K bin word).support) :
    AncestralRoot N q.1 := by
  rcases (PMF.mem_support_map_iff _ _ _).mp hq with ⟨a,ha,he⟩
  rcases (PMF.mem_support_bind_iff _ _ _).mp ha with ⟨s,hs,ha⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp ha with ⟨h,hh,hea⟩
  subst a
  subst q
  rcases (PMF.mem_support_map_iff _ _ _).mp hs with ⟨register,_,hs⟩
  subst s
  have hd := proxy_reader_endpoint_support N phat rhat b K hz word
    (initialCode N sample register) (fun x y => bin (leafAgeMatrix N C sample x y)) h hh
  rw [← cut_refines_source_program N rhat (tune_cut_refines N phat href)] at hd
  have hhat : compiledCalendarProgram N C H (originalGamma phat) common ++ [(ProgramStep.interval (N := N) t)] =
      (ops ++ [(ProgramStep.interval (N := N) t)]).map (tuneStep N phat) := by
    simp only [List.map_append, List.map_cons, List.map_nil, tuneStep]
    rw [← hwhole,tune_compiled_calendar]
  rw [← hhat] at hd
  exact original_extended_ancestral_support N C sample H phat common rhat register t hd

theorem extended_proxy_tail_rate_invariant (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p phat : HybridProbabilities N) (common : Hybrid N → Bool) (rhat r rtail : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0)
    (bin : ℝ → Tag) (ops : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = ops)
    (t : ℝ≥0) (word : List (ProgramStep N × Tag))
    (href : CutRefines N (ops ++ [(ProgramStep.interval (N := N) t)]) (physicalOps N word)) (tailTag : Tag) :
    (allBankNaturalJoint N C sample phat rhat b K bin word).bind (jointTailKernel N r tailTag) =
      (allBankNaturalJoint N C sample phat rhat b K bin word).bind (jointTailKernel N rtail tailTag) := by
  apply bind_congr_on_support
  intro q hq
  unfold jointTailKernel
  rw [completion_kernel_rate_invariant N r rtail q.1
    (extended_proxy_ancestral_support N C sample H p phat common rhat b K hz
      bin ops hwhole t word href q hq)]


/-- Full actual finite tagged/bin observation with shared rate/count/inheritance
approximation and a specified positive exact-completion bank. -/
theorem actual_arbitrary_cut_all_bank_proxy_tv {Tag O : Type*}
    [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag] [Fintype O]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p phat : HybridProbabilities N)
    (common : Hybrid N → Bool) (r rhat rtail : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0) (ell u beta : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (htrue : ∀ h, beta * p.gamma h ≤ phat.gamma h)
    (hfalse : ∀ h, beta * (1-p.gamma h) ≤ 1-phat.gamma h)
    (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = ops)
    (cut : ℝ) (word : List (ProgramStep N × Tag))
    (href : CutRefines N (ops ++ [.interval (Real.toNNReal
      (cut - (firstOriginalDate N C + (programDuration N ops : ℝ))))]) (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C))
    (hb : ∀ op ∈ physicalOps N word, Budget (Copy := Copy) N r b K op)
    (tailTag : Tag)
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag)
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) :
    pmfTV ((naturalCompletedJoint N C sample p r bin hbin ops).map readout)
      (((allBankNaturalJoint N C sample phat rhat b K bin word).bind
        (jointTailKernel N rtail tailTag)).map readout) ≤
      1 - (initialMass N beta * ((physicalOps N word).map
        (allBankMass (Copy := Copy) N r b K ell u beta)).prod).toReal := by
  let t := Real.toNNReal (cut - (firstOriginalDate N C + (programDuration N ops : ℝ)))
  rw [← extended_proxy_tail_rate_invariant N C sample H p phat common rhat r rtail b K hz
    bin ops hwhole t word href tailTag]
  have halign : ∀ op ∈ ops ++ [(ProgramStep.interval (N := N) t)], aligned N p op := by
    intro op hop
    rcases List.mem_append.mp hop with hop | hop
    · have ha := compiled_calendar_aligned N C H p common
      rw [hwhole] at ha
      exact ha op hop
    · have he : op = (ProgramStep.interval (N := N) t) := List.mem_singleton.mp hop
      subst op
      trivial
  have ha : ∀ op ∈ physicalOps N word, aligned N p op :=
    refinement_aligned N p href halign
  have hcomplete : naturalCompletedJoint N C sample p r bin hbin ops =
      (naturalPastJoint N C sample p r bin hbin (ops ++ [(ProgramStep.interval (N := N) t)])).bind
        (jointTailKernel N r tailTag) := by
    simpa only [hwhole] using
      actual_natural_arbitrary_last_cut N C sample H p common r bin hbin cut tailTag htail
  rw [hcomplete, actual_natural_past_endpoint_history N C sample p r bin hbin
    (ops ++ [(ProgramStep.interval (N := N) t)]) word href hword]
  simpa only [allBankNaturalJoint, PMF.bind_map, PMF.map_bind, Function.comp_def] using
    initialized_all_bank_finish_tv N sample p phat r rhat b K ell u beta
      hell hell1 hu1 hlo hup hbeta hbeta1 htrue hfalse (physicalOps N word) hb ha
      (fun a => (jointTailKernel N r tailTag
        (endpointHistoryReadout N word a.1
          (fun x y => bin (leafAgeMatrix N C sample x y)) a.2)).map readout)

#print axioms extended_proxy_ancestral_support
#print axioms extended_proxy_tail_rate_invariant
#print axioms actual_arbitrary_cut_all_bank_proxy_tv

end DotG6.ArbitraryCutSharedBankProxy
