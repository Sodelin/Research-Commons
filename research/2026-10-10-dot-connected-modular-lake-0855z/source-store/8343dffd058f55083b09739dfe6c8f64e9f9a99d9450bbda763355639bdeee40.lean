import G5ActualDiscreteCutEvent
import G5EnumeratedPosteriorGerm

namespace GProgram.G5.ObservedCutPosterior
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G5.OriginalProgramSurvival GProgram.G5.OriginalSelectedPosterior
open GProgram.G5.EnumeratedTripleRow GProgram.G5.EnumeratedPosteriorGerm
open GProgram.G5.ActualDiscreteCutEvent
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma filter_eq_on_support {A : Type*} (mu : PMF A) (D F : Set A)
    (hD : ∃ a ∈ D, a ∈ mu.support) (hF : ∃ a ∈ F, a ∈ mu.support)
    (h : ∀ a ∈ mu.support, a ∈ D ↔ a ∈ F) : mu.filter D hD = mu.filter F hF := by
  have he : D.indicator mu = F.indicator mu := by
    funext a
    by_cases hs : a ∈ mu.support
    · by_cases ha : a ∈ D
      · simp [ha,(h a hs).mp ha]
      · simp [ha,mt (h a hs).mpr ha]
    · have hz : mu a = 0 := by simpa only [PMF.mem_support_iff,not_not] using hs
      simp [Set.indicator,hz]
  apply PMF.ext
  intro a
  simp only [PMF.filter_apply,he]

theorem actual_discrete_event_witness (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (past : List (ProgramStep N)) (i : Fin 3 ≃ Copy) :
    ∃ d ∈ {d | indexedPartition N i d = 0},
      d ∈ (originalProgramLaw N sample p r past).support := by
  obtain ⟨d,hd,hs⟩ := actual_initialized_program_singleton_witness N sample p r Finset.univ past
  exact ⟨d,(actual_partition_zero_iff_singleton N sample p r past i d hd).mpr hs,hd⟩

/-- Conditioning on the decoded original genealogy partition gives precisely
the previously defined original source posterior, including its stored register. -/
theorem actual_observed_cut_posterior (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (past : List (ProgramStep N)) (i : Fin 3 ≃ Copy) :
    (originalProgramLaw N sample p r past).filter {d | indexedPartition N i d = 0}
      (actual_discrete_event_witness N sample p r past i) =
      originalTripleCodePosterior N sample p r past := by
  unfold originalTripleCodePosterior
  apply filter_eq_on_support
  intro d hd
  exact actual_partition_zero_iff_singleton N sample p r past i d hd

#print axioms actual_discrete_event_witness
#print axioms actual_observed_cut_posterior
end GProgram.G5.ObservedCutPosterior
