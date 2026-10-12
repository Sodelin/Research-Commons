import SharedBankNaturalProxy
import UnifiedLean.Source.SourceEpochSemigroup

/-! dot (OpenAI), 9 October 2026. Candidate full shared-bank finite-bin
completion assembly. All-source support is derived before replacing the tail bank. -/
namespace DotG6.SharedBankCompleteProxy
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
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem cut_refines_source_program (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) {a b : List (ProgramStep N)} (href : CutRefines N a b)
    (s : Code N sample) : sourceProgram N r a s = sourceProgram N r b s := by
  induction href generalizing s with
  | refl ops => rfl
  | split pre suf t v =>
      rw [sourceProgram_append,sourceProgram_append]
      apply congrArg (PMF.bind (sourceProgram N r pre s))
      funext d
      change (sourceTimeKernel N r (t+v) d).bind (sourceProgram N r suf) =
        (sourceTimeKernel N r t d).bind (fun e =>
          (sourceTimeKernel N r v e).bind (sourceProgram N r suf))
      rw [actual_source_time_add, PMF.bind_bind]
  | trans h1 h2 ih1 ih2 => exact (ih1 s).trans (ih2 s)

lemma all_bank_step_support (N : RootedBinary V E X) {sample : Copy → X}
    (phat : HybridProbabilities N) (rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0)
    (op : ProgramStep N) (s : Code N sample) :
    (allBankProxyStep N phat rhat b K op s).support ⊆
      (sourceProgramStep N rhat (tuneStep N phat op) s).support := by
  intro d hd
  cases op with
  | interval t =>
      exact proxy_interval_support N rhat t (b t) K (fun ht => by simpa [ht] using hz) s d hd
  | boundary k => exact hd

/-- A support path is followed directly; no Fin-length cast or endpoint-law
identity is assumed for a differently parameterized operation list. -/
theorem proxy_reader_endpoint_support {Tag : Type*}
    (N : RootedBinary V E X) {sample : Copy → X}
    (phat : HybridProbabilities N) (rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0)
    (word : List (ProgramStep N × Tag)) (s : Code N sample) (B : Copy → Copy → Tag)
    (h : Fin (physicalOps N word).length → Code N sample)
    (hh : h ∈ (historyLaw (allBankProxyStep N phat rhat b K) (physicalOps N word) s).support) :
    (endpointHistoryReadout N word s B h).1 ∈
      (sourceProgram N rhat ((physicalOps N word).map (tuneStep N phat)) s).support := by
  induction word generalizing s B with
  | nil => simp [physicalOps,endpointHistoryReadout,sourceProgram]
  | cons op word ih =>
      rcases (PMF.mem_support_bind_iff _ _ _).mp hh with ⟨d,hd,hh⟩
      rcases (PMF.mem_support_map_iff _ _ _).mp hh with ⟨tail,ht,he⟩
      subst h
      apply (PMF.mem_support_bind_iff _ _ _).mpr
      refine ⟨d,all_bank_step_support N phat rhat b K hz op.1 s hd,?_⟩
      exact ih d (endpointStepTags N op.1 op.2 s d B) tail ht

variable {Tag : Type*} [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

noncomputable def allBankNaturalJoint (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (phat : HybridProbabilities N)
    (rhat : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ)
    (bin : ℝ → Tag) (word : List (ProgramStep N × Tag)) :=
  (initialHistory (allBankProxyStep N phat rhat b K) (physicalOps N word)
    (naturalInitialCodeLaw N sample phat)).map (fun a =>
      endpointHistoryReadout N word a.1
        (fun x y => bin (leafAgeMatrix N C sample x y)) a.2)

theorem all_bank_proxy_ancestral_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p phat : HybridProbabilities N) (common : Hybrid N → Bool) (rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0)
    (bin : ℝ → Tag) (ops : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = ops)
    (word : List (ProgramStep N × Tag)) (href : CutRefines N ops (physicalOps N word))
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
  have hhat : compiledCalendarProgram N C H (originalGamma phat) common =
      ops.map (tuneStep N phat) := by
    rw [← hwhole,tune_compiled_calendar]
  rw [← hhat] at hd
  exact initialized_original_calendar_ancestral_support N C sample register H
    (originalGamma phat) common rhat hd

theorem all_bank_proxy_tail_rate_invariant (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p phat : HybridProbabilities N) (common : Hybrid N → Bool) (rhat r rtail : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0)
    (bin : ℝ → Tag) (ops : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = ops)
    (word : List (ProgramStep N × Tag)) (href : CutRefines N ops (physicalOps N word)) (tailTag : Tag) :
    (allBankNaturalJoint N C sample phat rhat b K bin word).bind (jointTailKernel N r tailTag) =
      (allBankNaturalJoint N C sample phat rhat b K bin word).bind (jointTailKernel N rtail tailTag) := by
  apply bind_congr_on_support
  intro q hq
  unfold jointTailKernel
  rw [completion_kernel_rate_invariant N r rtail q.1
    (all_bank_proxy_ancestral_support N C sample H p phat common rhat b K hz
      bin ops hwhole word href q hq)]

/-- Full actual finite tagged/bin observation with shared rate/count/inheritance
approximation and a specified positive exact-completion bank. -/
theorem actual_complete_all_bank_proxy_tv {Tag O : Type*}
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
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C))
    (hb : ∀ op ∈ physicalOps N word, Budget (Copy := Copy) N r b K op)
    (cut : ℝ) (tailTag : Tag)
    (hoff : cut ≤ firstOriginalDate N C + (programDuration N ops : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tailTag)
    (readout : TaggedEndpoint (Tag := Tag) N sample → O) :
    pmfTV ((naturalCompletedJoint N C sample p r bin hbin ops).map readout)
      (((allBankNaturalJoint N C sample phat rhat b K bin word).bind
        (jointTailKernel N rtail tailTag)).map readout) ≤
      1 - (initialMass N beta * ((physicalOps N word).map
        (allBankMass (Copy := Copy) N r b K ell u beta)).prod).toReal := by
  rw [← all_bank_proxy_tail_rate_invariant N C sample H p phat common rhat r rtail b K hz
    bin ops hwhole word href tailTag]
  have ha : ∀ op ∈ physicalOps N word, aligned N p op :=
    refinement_aligned N p href (by rw [← hwhole]; exact compiled_calendar_aligned N C H p common)
  have hcomplete : naturalCompletedJoint N C sample p r bin hbin ops =
      (naturalPastJoint N C sample p r bin hbin ops).bind (jointTailKernel N r tailTag) := by
    simpa only [List.append_nil, calendar_joint_nil, PMF.pure_bind] using
      actual_natural_completed_eq_past_suffix N C sample H p common r bin hbin
        ops [] (by simpa using hwhole) cut tailTag (by simpa using hoff) htail
  rw [hcomplete, actual_natural_past_endpoint_history N C sample p r bin hbin ops word href hword]
  simpa only [allBankNaturalJoint, PMF.bind_map, PMF.map_bind, Function.comp_def] using
    initialized_all_bank_finish_tv N sample p phat r rhat b K ell u beta
      hell hell1 hu1 hlo hup hbeta hbeta1 htrue hfalse (physicalOps N word) hb ha
      (fun a => (jointTailKernel N r tailTag
        (endpointHistoryReadout N word a.1
          (fun x y => bin (leafAgeMatrix N C sample x y)) a.2)).map readout)

#print axioms cut_refines_source_program
#print axioms proxy_reader_endpoint_support
#print axioms all_bank_proxy_ancestral_support
#print axioms all_bank_proxy_tail_rate_invariant
#print axioms actual_complete_all_bank_proxy_tv
end DotG6.SharedBankCompleteProxy
