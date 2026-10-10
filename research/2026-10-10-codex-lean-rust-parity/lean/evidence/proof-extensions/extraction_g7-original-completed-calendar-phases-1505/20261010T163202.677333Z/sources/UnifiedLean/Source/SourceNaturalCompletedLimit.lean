import UnifiedLean.Source.SourceEventualCompletionLimit

/-!
# Actual natural graph/calendar law reaches its completed unranked tree law

Contributor: dot, 2026-10-02. Composes the already graph-generated natural
prior/calendar with the actual eventual ancestral kernel, and transports the
limit to the concrete original-labelled child-swap quotient observer. No
external initialization, terminal law or observation equality is a field.
Same-original-graph independently initialized smaller-copy transport and the
stronger maximal timed-path law remain distinct connected obligations.
-/
namespace UnifiedLean.Source.SourceNaturalCompletedLimit
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Filter
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceEventualCompletionLimit
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical BigOperators NNReal Topology
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def naturalSourceAfterRoot (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (t : ℝ≥0) : PMF (Code N sample) :=
  (naturalCalendarLaw N C sample H p common r).bind (sourceTimeKernel N r t)

/-- Original graph-generated tip initialization, natural mode-correct coins
and chronological source calendar followed by the actual ancestral duration
converge to the constructed ORIGINAL completed forest law. -/
theorem natural_source_tendsto_completed [Nonempty Copy] (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (d : Code N sample) :
    Tendsto (fun t : ℝ≥0 => (naturalSourceAfterRoot N C sample H p common r t d).toReal) atTop
      (𝓝 (naturalCompletedLaw N C sample H p common r d).toReal) := by
  change Tendsto (fun t : ℝ≥0 =>
      ((naturalCalendarLaw N C sample H p common r).bind (sourceTimeKernel N r t) d).toReal) atTop
    (𝓝 ((naturalCalendarLaw N C sample H p common r).bind (completionKernel N r) d).toReal)
  simp only [bind_probability_real,tsum_fintype]
  apply tendsto_finsetSum
  intro s _
  by_cases hs : s ∈ (naturalCalendarLaw N C sample H p common r).support
  · exact (actual_ancestral_kernel_tendsto_completion N r s d
      (natural_calendar_ancestral_support N C sample H p common r hs)).const_mul _
  · have hz : naturalCalendarLaw N C sample H p common r s = 0 := by
      simpa only [PMF.mem_support_iff,not_not] using hs
    simp only [hz,ENNReal.toReal_zero,zero_mul]
    exact tendsto_const_nhds

/-- Standard finite pushforward instantiated below with the concrete original
unranked forest observer. No abstract desired observable law is assumed. -/
lemma finite_pmf_observer_limit {A B : Type*} [Fintype A]
    (law : ℝ≥0 → PMF A) (limit : PMF A) (obs : A → B)
    (h : ∀ a, Tendsto (fun t => (law t a).toReal) atTop (𝓝 (limit a).toReal)) (b : B) :
    Tendsto (fun t => ((law t).map obs b).toReal) atTop (𝓝 (limit.map obs b).toReal) := by
  simp only [PMF.map,bind_probability_real,tsum_fintype,Function.comp_apply]
  apply tendsto_finsetSum
  intro a _
  exact (h a).mul_const _

/-- End-to-end actual ORIGINAL graph/calendar/prior/source-time law converges
to the concrete complete rooted UNRANKED tree law on ALL original copy IDs.
This closes eventual-completion admission, without claiming the separately
pending smaller-copy source comparison or maximal timed-path strengthening. -/
theorem natural_source_unranked_tendsto_completed [Nonempty Copy] (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (F : Finset (UnrankedTree Copy)) :
    Tendsto (fun t : ℝ≥0 => ((naturalSourceAfterRoot N C sample H p common r t).map
      (fun s => sourceUnrankedForest (state s) Finset.univ) F).toReal) atTop
      (𝓝 (naturalCompletedUnrankedLaw N C sample H p common r F).toReal) :=
  finite_pmf_observer_limit _ _ _ (natural_source_tendsto_completed N C sample H p common r) F

#print axioms natural_source_tendsto_completed
#print axioms natural_source_unranked_tendsto_completed
end UnifiedLean.Source.SourceNaturalCompletedLimit
