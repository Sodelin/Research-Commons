import G2EpochHistoryReadout
import G2FiniteAncestralTrace

/-!
All-time readout of the finite actual random-cover ancestral trace.
Contributor: dot (OpenAI), 6 October 2026. The output is exactly the literal
same-clock endpoint path at every nonnegative time, not a fixed truncation.
Cross-carrier distribution transport and calendar joining remain separate.
-/
namespace GProgram.G2.CompleteAncestralPath
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.EpochHistoryReadout
open GProgram.G2.FiniteAncestralTrace
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

noncomputable def completePath (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (z : Bool × ClockTrace N sample (Fintype.card Copy)) :
    ℝ≥0 → Code N sample := fun t => cutEndpoint N (Fintype.card Copy) (t : ℝ) s z.2

lemma complete_path_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Measurable (completePath N s) := by
  apply measurable_pi_lambda
  intro t
  exact (cut_endpoint_joint_measurable N _ (t : ℝ)).comp
    (measurable_const.prodMk measurable_snd)

noncomputable def literalEpochPath (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (c : Choice N s → ℝ) : ℝ≥0 → Code N sample :=
  fun t => traceEndpoint N (Fintype.card Copy) s
    (literalMarkedTrace N (Fintype.card Copy) (t : ℝ) s c).2

lemma literal_epoch_path_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Measurable (literalEpochPath N s) := by
  apply measurable_pi_lambda
  intro t
  have hm : Measurable (fun c : Choice N s → ℝ =>
      cutEndpoint N (Fintype.card Copy) (t : ℝ) s
        (literalMarkedTrace N (Fintype.card Copy) (t : ℝ) s c).2) :=
    (cut_endpoint_joint_measurable N _ (t : ℝ)).comp
      (measurable_const.prodMk (marked_trace_measurable N _ s t).snd)
  convert hm using 1
  funext c
  exact (actual_history_cut_readout N _ t t s c le_rfl).symm

/-- Simultaneous equality at every time on each original clock vector. The
random cover is used only to store the finite trace, never as a time cutoff. -/
theorem actual_complete_path_agrees (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (c : Choice N s → ℝ) :
    completePath N s (completeAncestralTrace N s c) = literalEpochPath N s c := by
  funext t
  by_cases ht : (t : ℝ) ≤ (clockCover N s c : ℝ)
  · exact actual_history_cut_readout N (Fintype.card Copy) t (clockCover N s c) s c ht
  · have hc : (clockCover N s c : ℝ) ≤ (t : ℝ) := le_of_not_ge ht
    change cutEndpoint N (Fintype.card Copy) (t : ℝ) s (completeAncestralTrace N s c).2 = _
    rw [← complete_ancestral_trace_stable N s c t hc]
    exact actual_history_cut_readout N _ t t s c le_rfl

/-- The finite record pushforward is the actual original-clock all-time path
law. No source-PMF/projectivity/Markov law is an input to this identity. -/
theorem actual_complete_path_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (completeAncestralTraceLaw N r s).map (completePath N s) =
      (currentPairClockMeasure N r s).map (literalEpochPath N s) := by
  rw [completeAncestralTraceLaw,Measure.map_map (complete_path_measurable N s)
    (complete_ancestral_trace_measurable N s)]
  congr 1
  funext c
  exact actual_complete_path_agrees N s c

#print axioms complete_path_measurable
#print axioms literal_epoch_path_measurable
#print axioms actual_complete_path_agrees
#print axioms actual_complete_path_law
end GProgram.G2.CompleteAncestralPath
