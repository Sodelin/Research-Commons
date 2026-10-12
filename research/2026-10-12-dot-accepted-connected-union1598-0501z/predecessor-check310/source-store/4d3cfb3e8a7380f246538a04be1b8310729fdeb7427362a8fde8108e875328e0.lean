import G5ActualRoutingSupport
import G5EnumeratedTripleRow

namespace GProgram.G5.ActualDiscreteCutEvent
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.NativeIndependentPairMixture
open GProgram.G5.ActualRoutingSupport GProgram.G5.ActualNoMergerReadout
open GProgram.G5.OriginalProgramSurvival GProgram.G5.EnumeratedTripleRow
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Discrete observed partition and the actual singleton posterior event
coincide on the original program's support. This allows outside-copy mergers
only after applying the inherited selected-carrier projectivity. -/
theorem actual_partition_zero_iff_singleton (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (past : List (ProgramStep N)) (i : Fin 3 ≃ Copy) (d : Code N sample)
    (hd : d ∈ (originalProgramLaw N sample p r past).support) :
    indexedPartition N i d = 0 ↔
      SingletonSelected Finset.univ (selectedView (state d) Finset.univ) := by
  rw [indexedPartition,general_partition_zero,composed_ancestor_injective]
  constructor
  · intro hinj
    apply ((actual_original_singleton_iff_route N sample p r past d).mpr ?_).2
    obtain ⟨reg,hr,hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨reg,hr,(actual_unchanged_count_iff_route N r past _ d).mp ⟨hdr,?_⟩⟩
    have hc := (actual_maximal_live_card_iff N d).mpr hinj
    have hi := (actual_maximal_live_card_iff N (initialCode N sample reg)).mpr
      (singleton_ancestor_injective N _
        (actual_initial_singleton_selected N sample Finset.univ reg))
    exact hc.trans hi.symm
  · exact singleton_ancestor_injective N d

#print axioms actual_partition_zero_iff_singleton
end GProgram.G5.ActualDiscreteCutEvent
