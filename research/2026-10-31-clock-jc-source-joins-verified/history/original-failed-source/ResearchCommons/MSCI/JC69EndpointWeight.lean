import ResearchCommons.MSCI.JC69WeightedTrace
import ResearchCommons.MSCI.JC69CurrentPartition
import G2ActualCalendarTrace

/-! Narrow endpoint-resolved extension, 31 October 2026. UNCOMPILED.
Contributor: dot (OpenAI). This keeps the ACTUAL exit descendant blocks and
original-copy populations. It does not assume that this observation is a
Markov quotient, use its whole carrier as Bell(n)P^n, or admit hidden-bank
routing. No scalar product of epoch expectations is introduced. -/
noncomputable section
namespace ResearchCommons.MSCI.JC69EndpointWeight
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceMergerClockCatalogue UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceRenewal
open GProgram.G2.ActualCalendarTrace
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69TraceOccupation
open ResearchCommons.MSCI.JC69WeightedTrace ResearchCommons.MSCI.JC69CurrentPartition
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- A receiving observation type, NOT a claimed minimal Markov state space.
Actual values have partition blocks; arbitrary receiver values need not. -/
abbrev BlockPopulationObservation (Copy V E : Type*) :=
  Finset (Finset Copy) × (Copy → Location V E)

def observeState (s : State V E Copy) : BlockPopulationObservation Copy V E :=
  (currentBlocks s,fun x => copyLocation s x)

def observeCode (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) :
    BlockPopulationObservation Copy V E := observeState (state s)

/-- Actual per-original-copy populations are constant on every current
ancestral block. This is source coherence, not epoch-active injectivity. -/
lemma actual_block_population_constant (s : State V E Copy) (hs : Valid s)
    {B : Finset Copy} (hB : B ∈ currentBlocks s) {x y : Copy}
    (hx : x ∈ B) (hy : y ∈ B) : copyLocation s x = copyLocation s y := by
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hB
  have hxa := (hs.leaf_fiber l hl x).mp hx
  have hya := (hs.leaf_fiber l hl y).mp hy
  simp only [copyLocation,hxa,hya]

/-- Actual endpoint observation equality for two merger orientations. This
is NOT equality of their future weighted continuation, which remains open. -/
lemma actual_merge_observation_orientation (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (hm : LegalMerge s a b) :
    observeState (merge s a b) = observeState (merge s b a) := by
  apply Prod.ext
  · exact actual_merge_orientation_blocks s hs hm
  · funext x
    exact actual_merge_orientation_locations s hm x

/-- Endpoint identity is read from the original trace's stored endpoint. -/
def exitIndicator (N : RootedBinary V E X) {sample : Copy → X}
    (n : ℕ) (s : Code N sample) (target : BlockPopulationObservation Copy V E)
    (z : Bool × ClockTrace N sample n) : ℝ≥0∞ :=
  if observeCode N (traceEndpoint N n s z.2) = target then 1 else 0

def resolvedTraceWeight (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (n : ℕ) (s : Code N sample) (t : ℝ)
    (target : BlockPopulationObservation Copy V E) (z : Bool × ClockTrace N sample n) : ℝ≥0∞ :=
  locusTraceWeight N L q n s t z * exitIndicator N n s target z

lemma exit_indicator_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : ℕ) (s : Code N sample) (target : BlockPopulationObservation Copy V E) :
    Measurable (exitIndicator N n s target) := by
  have hm : Measurable (fun d : Code N sample =>
      if observeCode N d = target then (1 : ℝ≥0∞) else 0) := measurable_of_countable _
  exact hm.comp ((trace_endpoint_measurable N n s).comp measurable_snd)

lemma resolved_weight_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (n : ℕ) (s : Code N sample) (t : ℝ)
    (target : BlockPopulationObservation Copy V E) :
    Measurable (resolvedTraceWeight N L q n s t target) :=
  (locus_trace_weight_measurable N L q n s t).mul (exit_indicator_measurable N n s target)

/-- The SAME final exit target stays attached to the future trace. -/
lemma resolved_weight_prepend (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (n : ℕ) (s d : Code N sample)
    (age t : ℝ) (target : BlockPopulationObservation Copy V E)
    (z : Bool × ClockTrace N sample n) :
    resolvedTraceWeight N L q (n+1) s t target (z.1,prependTrace N age d z.2) =
      ENNReal.ofReal (Real.exp (-(locusKill N L q s*age))) *
        resolvedTraceWeight N L q n d (t-age) target z := by
  unfold resolvedTraceWeight exitIndicator
  rw [locus_weight_prepend,prepend_trace_endpoint,mul_assoc]

lemma resolved_weight_empty (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (n : ℕ) (s : Code N sample) (t : ℝ)
    (target : BlockPopulationObservation Copy V E) :
    resolvedTraceWeight N L q n s t target (true,emptyTrace N n s) =
      ENNReal.ofReal (Real.exp (-(locusKill N L q s*t))) *
        (if observeCode N s = target then 1 else 0) := by
  simp only [resolvedTraceWeight,exitIndicator,locus_weight_empty,empty_trace_endpoint]

/-- Actual weighted exit mass; not a postulated killed transition kernel. -/
def actualResolvedWeight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ) (target : BlockPopulationObservation Copy V E) : ℝ≥0∞ :=
  ∫⁻ z, resolvedTraceWeight N L q n s t target z ∂actualMarkedTraceLaw N r n s t

lemma actual_resolved_clock_integral (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ) (target : BlockPopulationObservation Copy V E) :
    actualResolvedWeight N r L q n s t target =
      ∫⁻ c, resolvedTraceWeight N L q n s t target (literalMarkedTrace N n t s c)
        ∂currentPairClockMeasure N r s := by
  rw [actualResolvedWeight,actualMarkedTraceLaw,
    lintegral_map (resolved_weight_measurable N L q n s t target) (marked_trace_measurable N n s t)]

/-- Endpoint-resolved renewal of the ORIGINAL weighted source law. No
quotient-continuation equality, boundary factorization, or final expansion
is a premise. Both ordered half-rate choices are retained at this stage. -/
theorem actual_resolved_weight_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    actualResolvedWeight N r L q (n+1) s t target =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) *
        (ENNReal.ofReal (Real.exp (-(locusKill N L q s*(t : ℝ)))) *
          (if observeCode N s = target then 1 else 0)) +
      ∑ p : Choice N s,
        ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (-(locusKill N L q s*u))) *
          actualResolvedWeight N r L q n (stepDestination N s (some p)) ((t : ℝ)-u) target
          ∂((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) •
            expMeasure (totalRate N r s)).restrict (Iic (t : ℝ))) := by
  have hw := resolved_weight_measurable N L q (n+1) s (t : ℝ) target
  rw [actualResolvedWeight,actual_marked_trace_first_jump_renewal,
    lintegral_add_measure,lintegral_smul_measure,lintegral_dirac' _ hw,
    resolved_weight_empty,lintegral_finsetSum_measure]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  letI : ∀ v : Choice N (stepDestination N s (some p)),
      IsProbabilityMeasure (expMeasure (choiceRate N r (stepDestination N s (some p)) v)) :=
    fun v => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r v.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r (stepDestination N s (some p))) := by
    unfold currentPairClockMeasure
    infer_instance
  rw [lintegral_map hw (first_jump_future_measurable N n s p t)]
  rw [lintegral_prod _ (hw.comp (first_jump_future_measurable N n s p t)).aemeasurable]
  apply lintegral_congr
  intro u
  simp_rw [firstJumpFuture,resolved_weight_prepend]
  rw [lintegral_const_mul _ ((resolved_weight_measurable N L q n
      (stepDestination N s (some p)) ((t : ℝ)-u) target).comp
        (marked_trace_measurable N n (stepDestination N s (some p)) ((t : ℝ)-u))),
    ← actual_resolved_clock_integral]

#print axioms actual_block_population_constant
#print axioms actual_merge_observation_orientation
#print axioms exit_indicator_measurable
#print axioms resolved_weight_measurable
#print axioms resolved_weight_prepend
#print axioms resolved_weight_empty
#print axioms actual_resolved_weight_renewal
end ResearchCommons.MSCI.JC69EndpointWeight
