import G2LiteralMarkedClockTrace

/-!
First actual-law branches for the new marked trace renewal assembly.
Contributor: dot (OpenAI), 6 October 2026. New uncompiled development source.
No complete epoch, full-past or projectivity law is an assumption.
-/
namespace GProgram.G2.MarkedTraceRenewal
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceMergerClockCatalogue
open GProgram.G2.LiteralMarkedClockTrace
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

def NoMarkedEvent (N : RootedBinary V E X) {sample : Copy → X} (n : Nat)
    (z : Bool × ClockTrace N sample n) : Prop :=
  z.1 = true ∧ ∀ i, (z.2 i).1 = false

/-- The successful zero-event branch is exactly literal clock survival,
even on pathological vectors and at zero budget. Inactive padding is ignored. -/
theorem no_marked_event_iff (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (t : ℝ) (c : Choice N s → ℝ) :
    NoMarkedEvent N n (literalMarkedTrace N n t s c) ↔ ∀ p : Choice N s, t < c p := by
  cases n with
  | zero => simp [NoMarkedEvent,literalMarkedTrace,emptyTrace]
  | succ n =>
      by_cases hs : ∀ p : Choice N s, t < c p
      · simp [NoMarkedEvent,literalMarkedTrace,hs,emptyTrace]
      · simp only [literalMarkedTrace,if_neg hs]
        cases hw : selectedWinner c with
        | none => simp [NoMarkedEvent,hs]
        | some p =>
            by_cases hp : c p ≤ t
            · simp only [if_pos hp]
              constructor
              · intro h
                have hf := h.2 (0 : Fin (n+1))
                simp [prependTrace] at hf
              · exact False.elim ∘ hs
            · simp [hp,NoMarkedEvent,hs]

lemma no_marked_event_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) : MeasurableSet {z : Bool × ClockTrace N sample n | NoMarkedEvent N n z} := by
  have hs : MeasurableSet {z : Bool × ClockTrace N sample n | z.1 = true} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have ha : MeasurableSet {z : Bool × ClockTrace N sample n | ∀ i, (z.2 i).1 = false} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_eq_fun
      (((measurable_pi_apply i).comp measurable_snd).fst) measurable_const)
  exact hs.inter ha

/-- The no-real-event mass of the actual trace law is the original exponential
product tail. This is one renewal branch, not the entire epoch distribution. -/
theorem actual_marked_no_event_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0) :
    (actualMarkedTraceLaw N r n s (t : ℝ) {z | NoMarkedEvent N n z}).toReal =
      Real.exp (-(totalRate N r s*(t : ℝ))) := by
  rw [actualMarkedTraceLaw,Measure.map_apply (marked_trace_measurable N n s t)
    (no_marked_event_measurable N n)]
  have he : (literalMarkedTrace N n (t : ℝ) s) ⁻¹' {z | NoMarkedEvent N n z} =
      currentNoFirstMerger N s t := by
    ext c
    simp only [mem_preimage,mem_setOf_eq,no_marked_event_iff,currentNoFirstMerger,
      mem_pi,mem_univ,mem_Ioi,true_implies]
  rw [he]
  exact actual_current_clock_no_merger N r t s

/-- The trace's successful no-event statistic agrees with the corresponding
actual source-PMF diagonal, using the existing strict live-card descent proof. -/
theorem actual_marked_no_event_source_binding (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0) :
    (actualMarkedTraceLaw N r n s (t : ℝ) {z | NoMarkedEvent N n z}).toReal =
      (UnifiedLean.Source.SourcePoissonKernel.sourceTimeKernel N r t s s).toReal := by
  rw [actual_marked_no_event_mass,actual_source_kernel_no_merger]

#print axioms no_marked_event_iff
#print axioms no_marked_event_measurable
#print axioms actual_marked_no_event_mass
#print axioms actual_marked_no_event_source_binding
end GProgram.G2.MarkedTraceRenewal
