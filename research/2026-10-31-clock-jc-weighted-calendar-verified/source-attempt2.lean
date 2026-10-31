import ResearchCommons.MSCI.JC69SourceFourierComposition
import ResearchCommons.MSCI.JC69RootResolvent

/-! Actual weighted calendar recursion. UNCOMPILED candidate.
Contributor: dot (OpenAI), 31 October 2026. The original segment record,
endpoint restriction, failure flag and shared site genealogy are retained.
No supported-state bound, exponential representation or denominator is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69WeightedCalendar
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.NativeParentRouting
open GProgram.G2.ActualCalendarTrace GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.CalendarDecoration GProgram.G2.FaithfulPairAgeDecoration
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open ResearchCommons.MSCI.JC69TraceOccupation ResearchCommons.MSCI.JC69CalendarOccupation
open ResearchCommons.MSCI.JC69RootWeightLimit ResearchCommons.MSCI.JC69RootResolvent
open ResearchCommons.MSCI.JC69SourceFourierComposition
open ResearchCommons.MSCI.JC69CompleteClockComposition ResearchCommons.MSCI.JC69ObservedFourier
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Boundary operations have no elapsed exposure; interval weights retain
exactly the original stored success flag, rather than conditioning it away. -/
def segmentWeight (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (op : ProgramStep N)
    (s : Code N sample) (z : SegmentRecord N sample) : ℝ≥0∞ :=
  match op with
  | .interval h => locusTraceWeight N L q (Fintype.card Copy) s h z.1
  | .boundary _ => 1

lemma segment_weight_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (op : ProgramStep N) (s : Code N sample) :
    Measurable (segmentWeight N L q op s) := by
  cases op with
  | interval h => exact (locus_trace_weight_measurable N L q _ s h).comp measurable_fst
  | boundary b => exact measurable_const

def calendarWeight (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) : (ops : List (ProgramStep N)) →
      Code N sample → (Fin ops.length → SegmentRecord N sample) → ℝ≥0∞
  | [],_,_ => 1
  | op::ops,s,past => segmentWeight N L q op s (past 0) *
      calendarWeight N L q ops (past 0).2 (Fin.tail past)

lemma calendar_weight_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (calendarWeight N L q ops s) := by
  induction ops generalizing s with
  | nil => exact measurable_const
  | cons op ops ih =>
      have hd : Measurable (fun z : Code N sample × (Fin ops.length → SegmentRecord N sample) =>
          calendarWeight N L q ops z.1 z.2) := measurable_from_prod_countable_right ih
      exact ((segment_weight_measurable N L q op s).comp (measurable_pi_apply 0)).mul
        (hd.comp (((measurable_pi_apply 0).snd).prodMk
          (measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ))))

lemma calendar_weight_of_success (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (ops : List (ProgramStep N))
    (s : Code N sample) (past : Fin ops.length → SegmentRecord N sample)
    (hs : ∀ i, (past i).1.1 = true) :
    calendarWeight N L q ops s past =
      ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j, calendarOccupation N (q j) ops s past))) := by
  induction ops generalizing s with
  | nil => simp [calendarWeight,calendarOccupation]
  | cons op ops ih =>
      have ht := ih (past 0).2 (Fin.tail past) (fun i => hs i.succ)
      have hh : segmentWeight N L q op s (past 0) =
          ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j,
            segmentOccupation N (q j) op s (past 0)))) := by
        cases op with
        | interval h => simp [segmentWeight,locusTraceWeight,segmentOccupation,hs 0]
        | boundary b => simp [segmentWeight,segmentOccupation]
      simp only [calendarWeight,hh,ht,calendarOccupation,Finset.sum_add_distrib]
      rw [mul_add,neg_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- Reuses the already proved finite-calendar success theorem; no new
normalization hypothesis or proof is introduced. -/
theorem actual_calendar_weight_exponential (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (ops : List (ProgramStep N)) (s : Code N sample) :
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s,
      calendarWeight N L q ops s past =
        ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j,
          calendarOccupation N (q j) ops s past))) := by
  filter_upwards [actual_calendar_success_ae N r ops s] with past hp
  exact calendar_weight_of_success N L q ops s past hp

/-- Original, UNNORMALIZED endpoint fibre integral. -/
def segmentFibreWeight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (op : ProgramStep N) (s d : Code N sample) : ℝ≥0∞ :=
  ∫⁻ z, segmentWeight N L q op s z ∂(actualSegmentLaw N r op s).restrict {z | z.2 = d}

/-- Finite backward recursion over the ACTUAL Code and endpoint fibres.
This definition does not assert the scientific S bound on the ambient type. -/
def calendarValue (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (terminal : Code N sample → ℝ≥0∞) : List (ProgramStep N) → Code N sample → ℝ≥0∞
  | [],s => terminal s
  | op::ops,s => ∑ d : Code N sample,
      segmentFibreWeight N r L q op s d * calendarValue N r L q terminal ops d

lemma weighted_readout_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (terminal : Code N sample → ℝ≥0∞)
    (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (fun past => calendarWeight N L q ops s past *
      terminal (calendarEnd N ops s past)) :=
  (calendar_weight_measurable N L q ops s).mul
    ((measurable_of_countable terminal).comp (calendar_end_measurable N ops s))

/-- Actual joint records, not a product of separately averaged epochs.
An arbitrary terminal function is allowed only as a readout of this exact
source measure; the complete-root specialization follows below. -/
theorem actual_calendar_weighted_recursion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (terminal : Code N sample → ℝ≥0∞) (ops : List (ProgramStep N)) (s : Code N sample) :
    (∫⁻ past, calendarWeight N L q ops s past * terminal (calendarEnd N ops s past)
      ∂actualCalendarTraceLaw N r ops s) = calendarValue N r L q terminal ops s := by
  induction ops generalizing s with
  | nil => simp [actualCalendarTraceLaw,calendarWeight,calendarEnd,calendarValue]
  | cons op ops ih =>
      letI := actual_segment_probability N r op s
      rw [actualCalendarTraceLaw,lintegral_finsetSum_measure,calendarValue]
      apply Finset.sum_congr rfl
      intro d _
      letI := actual_calendar_trace_probability N r ops d
      have hF := weighted_readout_measurable N L q terminal (op::ops) s
      have hm := record_cons_measurable N (sample := sample) ops.length
      rw [lintegral_map hF hm]
      rw [lintegral_prod
        (μ := (actualSegmentLaw N r op s).restrict {z | z.2 = d})
        (ν := actualCalendarTraceLaw N r ops d)
        (fun z => calendarWeight N L q (op::ops) s (recordCons N ops.length z) *
          terminal (calendarEnd N (op::ops) s (recordCons N ops.length z)))
        (hF.comp hm).aemeasurable]
      calc
        _ = ∫⁻ z, segmentWeight N L q op s z * calendarValue N r L q terminal ops d
            ∂(actualSegmentLaw N r op s).restrict {z | z.2 = d} := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem
            (measurableSet_eq_fun measurable_snd measurable_const :
              MeasurableSet {z : SegmentRecord N sample | z.2 = d})] with z hz
          simp only [recordCons,calendarWeight,calendarEnd,Fin.cons_zero,Fin.tail_cons,hz]
          simp_rw [mul_assoc]
          rw [lintegral_const_mul _ (weighted_readout_measurable N L q terminal ops d),ih d]
        _ = _ := by
          rw [lintegral_mul_const _ (segment_weight_measurable N L q op s)]
          rfl

/-- Exact root-weight readout, with no assumed root rational function. -/
theorem actual_calendar_root_recursion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (ops : List (ProgramStep N)) (s : Code N sample) :
    (∫⁻ past, calendarWeight N L q ops s past *
        rootWeight N r L q (calendarEnd N ops s past)
      ∂actualCalendarTraceLaw N r ops s) =
        calendarValue N r L q (rootWeight N r L q) ops s :=
  actual_calendar_weighted_recursion N r L q (rootWeight N r L q) ops s

/-- A zero-duration boundary keeps its exact original PMF transition weight. -/
theorem actual_boundary_fibre_weight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (b : BoundaryOperation N) (s d : Code N sample) :
    segmentFibreWeight N r L q (.boundary b) s d = boundaryKernel N b s d := by
  simp only [segmentFibreWeight,segmentWeight,lintegral_const,one_mul,
    Measure.restrict_apply MeasurableSet.univ,univ_inter]
  simpa only [sourceProgramStep] using segment_end_fibre_mass N r (.boundary b) s d

/-- Exact finite partition into endpoint fibres, without normalization. -/
lemma finite_fibre_lintegral {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] (μ : Measure A)
    (g : A → B) (hg : Measurable g) (f : A → ℝ≥0∞) :
    (∑ b : B, ∫⁻ x, f x ∂μ.restrict {x | g x = b}) = ∫⁻ x, f x ∂μ := by
  have hm (b : B) : MeasurableSet {x | g x = b} := hg (MeasurableSet.singleton b)
  have hd : Pairwise (fun b c : B => Disjoint {x : A | g x = b} {x | g x = c}) := by
    intro b c hbc
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hbc (hx.symm.trans hy)
  have hu : (⋃ b : B, {x : A | g x = b}) = Set.univ := by ext x; simp
  simpa only [hu,Measure.restrict_univ,tsum_fintype] using
    (lintegral_iUnion (μ := μ) hm hd f).symm

lemma ofReal_exp_add (a b : ℝ) :
    ENNReal.ofReal (Real.exp (a+b)) =
      ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) := by
  rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- Retained original initial potential. It need not vanish if the first
original network date precedes the contemporaneous sampled-leaf date. -/
def initialPotentialWeight (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (L : ℕ) (q : Fin L → Copy → Base) : ℝ≥0∞ :=
  let leafAge := fun x : Copy => C.age (N.leaf (sample x))
  let M := fun x (_ : Copy) => leafAge x
  ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j,
    forestPotential (q j) leafAge (state (initialCode N sample register)) M
      (firstOriginalDate N C))))

/-- The original full-labelled observed law equals the actual weighted
calendar recursion, with its original initialization factor. This does not
replace the source by a quotient, discard register dependence, or assert S. -/
theorem actual_observed_calendar_recursion [Nonempty Copy]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) :
    observedFourier L N C sample register H gamma common r q =
      (initialPotentialWeight N C sample register L q *
        calendarValue N r L q (rootWeight N r L q)
          (compiledCalendarProgram N C H gamma common)
          (initialCode N sample register)).toReal := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  let leafAge := fun x : Copy => C.age (N.leaf (sample x))
  let M := fun x (_ : Copy) => leafAge x
  let I := initialPotentialWeight N C sample register L q
  let W := fun past => ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j,
    calendarOccupation N (q j) ops s past)))
  let F := fun past => calendarWeight N L q ops s past *
    rootWeight N r L q (calendarEnd N ops s past)
  have hI : I ≠ ∞ := ENNReal.ofReal_ne_top
  have hfactor (d : Code N sample) (past : Fin ops.length → SegmentRecord N sample)
      (c : Choice N d → ℝ) :
      ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j,
        (forestPotential (q j) leafAge (state s) M (firstOriginalDate N C) +
          completeClockOccupation N (q j) ops s d past c)))) =
        (I * W past) * completeRootWeight N L q d c := by
    dsimp only [I,W,initialPotentialWeight,s,leafAge,M,completeClockOccupation,completeRootWeight]
    simp only [Finset.sum_add_distrib,mul_add,neg_add,ofReal_exp_add,mul_assoc]
  rw [actual_observed_balanced_clock_integral N C sample register H gamma common r L q hbal]
  apply congrArg ENNReal.toReal
  change (∑ d : Code N sample, ∫⁻ past, ∫⁻ c,
      ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j,
        (forestPotential (q j) leafAge (state s) M (firstOriginalDate N C) +
          completeClockOccupation N (q j) ops s d past c))))
        ∂currentPairClockMeasure N r d
        ∂(actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d}) =
    I * calendarValue N r L q (rootWeight N r L q) ops s
  calc
    _ = ∑ d : Code N sample, ∫⁻ past, I * F past
        ∂(actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d} := by
      apply Finset.sum_congr rfl
      intro d _
      apply lintegral_congr_ae
      have hm : MeasurableSet {past | calendarEnd N ops s past = d} :=
        measurableSet_eq_fun (calendar_end_measurable N ops s) measurable_const
      filter_upwards [ae_restrict_mem hm,
        ae_restrict_of_ae (actual_calendar_weight_exponential N r L q ops s)] with past hd hw
      simp_rw [hfactor d past]
      rw [lintegral_const_mul' (I * W past) _
        (ENNReal.mul_ne_top hI ENNReal.ofReal_ne_top)]
      simp only [F,rootWeight,hd,hw,mul_assoc]
    _ = ∫⁻ past, I * F past ∂actualCalendarTraceLaw N r ops s :=
      finite_fibre_lintegral _ (calendarEnd N ops s) (calendar_end_measurable N ops s) _
    _ = I * calendarValue N r L q (rootWeight N r L q) ops s := by
      rw [lintegral_const_mul' I F hI]
      exact congrArg (I * ·) (actual_calendar_root_recursion N r L q ops s)

#print axioms actual_calendar_weight_exponential
#print axioms actual_calendar_weighted_recursion
#print axioms actual_calendar_root_recursion
#print axioms actual_boundary_fibre_weight
#print axioms actual_observed_calendar_recursion
end ResearchCommons.MSCI.JC69WeightedCalendar
