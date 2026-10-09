import UpperRateCompleteObservation
import UnifiedLean.G6.AncestralRateFree

/-! dot (OpenAI), 9 October 2026. Candidate support adapter.
Explicitly require zero upper mean at a zero-duration interval. -/
namespace DotG6.UpperRateProxySupport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.G6.SourcePrefix UnifiedLean.G6.ResidualProgram UnifiedLean.G6.ResidualPrefix
open UnifiedLean.G6.UpperRateSourceCommon
open UnifiedLean.G6.FiniteProbability
open DotG6.UpperRateNaturalHistory
open scoped Classical NNReal ENNReal

lemma residual_support {A : Type*} [Fintype A]
    (q z : PMF A) (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1)
    (a : A) (ha : a ∈ (residualPMF q z rho h0 h1).support) :
    a ∈ q.support ∨ a ∈ z.support := by
  by_contra h
  have hq : q a = 0 := by
    by_contra hn
    exact h (Or.inl hn)
  have hz : z a = 0 := by
    by_contra hn
    exact h (Or.inr hn)
  have he : residualPMF q z rho h0 h1 a = 0 := by
    change ENNReal.ofReal (residualVector q z rho a) = 0
    simp [residualVector, hq, hz]
  exact ha he

lemma count_positive_support (a : ℝ≥0) (ha : 0 < a) (k : ℕ) : k ∈ (countPMF a).support := by
  intro hzero
  have hr : 0 < (countPMF a k).toReal := by
    rw [countPMF_real]
    positivity
  simpa [hzero] using hr

lemma zero_count_support (k : ℕ) (hk : k ∈ (countPMF 0).support) : k = 0 := by
  by_contra h
  have hr : (countPMF 0 k).toReal = 0 := by
    rw [countPMF_real]
    simp [zero_pow h]
  exact hk ((ENNReal.toReal_eq_zero_iff _).mp hr |>.resolve_right (PMF.apply_ne_top _ _))

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma holding_time_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    s ∈ (sourceTimeKernel N r t s).support := by
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  exact ⟨0, count_zero_ne_zero _, by simp [sourceIteration]⟩

/-- Every proxy endpoint is an endpoint of the SAME actual positive-bank
interval. This includes t=0 only under the explicit b=0 control. -/
theorem proxy_interval_support (N : RootedBinary V E X) {sample : Copy → X}
    (rhat : PositivePairRates E) (t b : ℝ≥0) (K : ℕ)
    (hz : t = 0 → b = 0) (s d : Code N sample)
    (hd : d ∈ (upperRateResidualSource N rhat b K s).support) :
    d ∈ (sourceTimeKernel N rhat t s).support := by
  rcases residual_support _ _ _ _ _ d hd with hd | hd
  · rcases (PMF.mem_support_bind_iff _ _ d).mp hd with ⟨k,hk,hkd⟩
    by_cases ht : t = 0
    · have hb := hz ht
      have hkc := (PMF.mem_support_filter_iff (prefix_has_support b K)).mp hk |>.2
      rw [hb] at hkc
      have hk0 := zero_count_support k hkc
      subst k
      have he : d = s := by simpa [sourceIteration] using hkd
      subst d
      exact holding_time_support N rhat t s
    · apply (PMF.mem_support_bind_iff _ _ d).mpr
      refine ⟨k, count_positive_support _ ?_ k, hkd⟩
      have hrate : 0 < globalClockRate (Copy := Copy) rhat :=
        globalRateBound_positive (Copy := Copy) rhat
      exact mul_pos hrate (lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from bot_le) (Ne.symm ht))
  · have he : d = s := by simpa using hd
    subst d
    exact holding_time_support N rhat t s

open GProgram.G2.SourceFiniteHistory
open CloudG3.ActualCalendarEndpointHistory

/-- Support inclusion composes through the full chronological history. -/
theorem history_support_subset {S Op : Type*} (P Q : Op → S → PMF S)
    (ops : List Op) (hstep : ∀ op ∈ ops, ∀ s, (Q op s).support ⊆ (P op s).support)
    (s : S) : (historyLaw Q ops s).support ⊆ (historyLaw P ops s).support := by
  intro h hh
  induction ops generalizing s with
  | nil => exact hh
  | cons op ops ih =>
      rcases (PMF.mem_support_bind_iff _ _ h).mp hh with ⟨d,hd,hh⟩
      rcases (PMF.mem_support_map_iff _ _ _).mp hh with ⟨tail,ht,he⟩
      apply (PMF.mem_support_bind_iff _ _ h).mpr
      refine ⟨d,hstep op (by simp) s hd,?_⟩
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨tail,
        ih (fun q hq => hstep q (List.mem_cons_of_mem op hq)) d ht,he⟩

theorem proxy_step_support (N : RootedBinary V E X) {sample : Copy → X}
    (rhat : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0)
    (op : ProgramStep N) (s : Code N sample) :
    (proxyStep N rhat b K op s).support ⊆ (sourceProgramStep N rhat op s).support := by
  intro d hd
  cases op with
  | interval t =>
      exact proxy_interval_support N rhat t (b t) K
        (fun ht => by simpa [ht] using hz) s d hd
  | boundary k => exact hd

/-- The entire proxy's joint initial-state/history support is contained in
the actual original comparison-bank history; no terminal support oracle. -/
theorem initialized_proxy_support (N : RootedBinary V E X) {sample : Copy → X}
    (rhat : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0)
    (ops : List (ProgramStep N)) (initial : PMF (Code N sample)) :
    (initializedProxy N rhat b K ops initial).support ⊆
      (CloudG6.PrivateSeedHistoryFactorization.initializedEndpointLaw N rhat ops initial).support := by
  intro z hzmem
  rcases (PMF.mem_support_bind_iff _ _ z).mp hzmem with ⟨s,hs,hzmem⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp hzmem with ⟨h,hh,he⟩
  apply (PMF.mem_support_bind_iff _ _ z).mpr
  refine ⟨s,hs,(PMF.mem_support_map_iff _ _ _).mpr ⟨h,?_,he⟩⟩
  exact history_support_subset _ _ ops (fun op _ s => proxy_step_support N rhat b K hz op s) s hh

open MeasureTheory GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open CloudG3.ActualCutJointLaw
open CloudG3.CompleteCalendarJointLaw CloudG3.CompleteCalendarBinReadout
open CloudG6.NaturalCalendarPastAdmission
open CloudG6.PrivateSeedFactorization
open UnifiedLean.G6.BinHistory
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

variable {Tag : Type*} [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

theorem actual_calendar_joint_code (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) :
    (calendarJointPMF N r bin hbin ops s offset M).map Prod.fst = sourceProgram N r ops s := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ measurable_fst, calendar_joint_pmf_toMeasure,
    calendarJointLaw, Measure.map_map measurable_fst
      (calendar_joint_bin_readout_measurable N bin hbin ops s offset M)]
  change (actualCalendarTraceLaw N r ops s).map (calendarEnd N ops s) = _
  exact actual_calendar_endpoint_law N r ops s

theorem natural_past_ancestral_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = ops)
    (q : TaggedEndpoint (Tag := Tag) N sample)
    (hq : q ∈ (naturalPastJoint N C sample p r bin hbin ops).support) :
    AncestralRoot N q.1 := by
  rcases (PMF.mem_support_bind_iff _ _ q).mp hq with ⟨register,_,hq⟩
  have hcode := (PMF.mem_support_map_iff Prod.fst _ q.1).mpr ⟨q,hq,rfl⟩
  rw [actual_calendar_joint_code] at hcode
  rw [← hwhole] at hcode
  exact initialized_original_calendar_ancestral_support N C sample register H
    (originalGamma p) common r hcode

open CloudG3.ActualObservationCutRefinement
open UnifiedLean.G6.AncestralRateFree
open UnifiedLean.Source.SourceCompletionHarmonic

noncomputable def naturalProxyJoint (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (p : HybridProbabilities N)
    (rhat : PositivePairRates E) (b : ℝ≥0 → ℝ≥0) (K : ℕ)
    (bin : ℝ → Tag) (word : List (ProgramStep N × Tag)) :
    PMF (TaggedEndpoint (Tag := Tag) N sample) :=
  (initializedProxy N rhat b K (physicalOps N word)
    (naturalInitialCodeLaw N sample p)).map (fun a =>
      endpointHistoryReadout N word a.1
        (fun x y => bin (leafAgeMatrix N C sample x y)) a.2)

/-- Derived ancestral support of the actual finite count proxy. Legal
refinement is retained; the entire history is compared at one rhat bank. -/
theorem natural_proxy_ancestral_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (rhat : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = ops)
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C))
    (q : TaggedEndpoint (Tag := Tag) N sample)
    (hq : q ∈ (naturalProxyJoint N C sample p rhat b K bin word).support) :
    AncestralRoot N q.1 := by
  rcases (PMF.mem_support_map_iff _ _ _).mp hq with ⟨a,ha,he⟩
  have ha' := initialized_proxy_support N rhat b K hz (physicalOps N word)
    (naturalInitialCodeLaw N sample p) ha
  have hq' : q ∈ ((CloudG6.PrivateSeedHistoryFactorization.initializedEndpointLaw N rhat
      (physicalOps N word) (naturalInitialCodeLaw N sample p)).map (fun a =>
        endpointHistoryReadout N word a.1
          (fun x y => bin (leafAgeMatrix N C sample x y)) a.2)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨a,ha',he⟩
  rw [← actual_natural_past_endpoint_history N C sample p rhat bin hbin ops word href hword] at hq'
  exact natural_past_ancestral_support N C sample H p common rhat bin hbin ops hwhole q hq'

/-- The completed proxy uses ANY positive ancestral bank without changing
its complete tagged law. This discharges the earlier proxy-support premise. -/
theorem natural_proxy_tail_rate_invariant (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (rhat r rtail : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common = ops)
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C)) (tailTag : Tag) :
    (naturalProxyJoint N C sample p rhat b K bin word).bind (jointTailKernel N r tailTag) =
      (naturalProxyJoint N C sample p rhat b K bin word).bind (jointTailKernel N rtail tailTag) := by
  apply bind_congr_on_support
  intro q hq
  unfold jointTailKernel
  rw [completion_kernel_rate_invariant N r rtail q.1
    (natural_proxy_ancestral_support N C sample H p common rhat b K hz
      bin hbin ops hwhole word href hword q hq)]

open GProgram.G2.ChronologicalPathReadout
open CloudG6.NaturalPastCompleteObservation

/-- Complete actual-source TV bound with a freely specified positive tail bank.
Choosing a rational bank is now legitimate; a table implementation is separate. -/
theorem actual_natural_complete_specified_tail_tv {Tag O : Type*}
    [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag] [Fintype O]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r rhat rtail : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0) (ell u : ℝ)
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
              (jointTailKernel N rtail tailTag)).map readout) ≤
      1 - (((physicalOps N word).map
        (commonMass (Copy := Copy) N r b K ell u)).prod).toReal := by
  change pmfTV ((CloudG6.NaturalPastCompleteObservation.naturalCompletedJoint N C sample p r bin hbin ops).map readout)
    (((naturalProxyJoint N C sample p rhat b K bin word).bind
      (jointTailKernel N rtail tailTag)).map readout) ≤ _
  rw [← natural_proxy_tail_rate_invariant N C sample H p common rhat r rtail b K hz
    bin hbin ops hwhole word href hword tailTag]
  exact DotG6.UpperRateCompleteObservation.actual_natural_complete_proxy_tv
    N C sample H p common r rhat b K ell u hell hell1 hu1 hlo hup
    bin hbin ops hwhole word href hword hb cut tailTag hoff htail readout

#print axioms actual_natural_complete_specified_tail_tv
#print axioms proxy_interval_support
#print axioms initialized_proxy_support
#print axioms natural_proxy_ancestral_support
#print axioms natural_proxy_tail_rate_invariant
end DotG6.UpperRateProxySupport
