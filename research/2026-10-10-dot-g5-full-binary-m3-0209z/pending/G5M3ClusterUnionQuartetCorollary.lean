import G5M3NormalizedClusterSplitIdentification

/-! Optional downstream quartet consequence, restructured after the original
combined proof exhausted its800000-heartbeat elaboration budget. Pending/unverified.
The full requested M3 cluster/split theorem is in the imported source.
Contributor: dot / OpenAI,10 October2026. -/
namespace GProgram.G5.M3NormalizedClusterSplitIdentification
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open GProgram.G5.AttainedChronology GProgram.G5.HiddenRegisterTimedProjectivity
open GProgram.G5.SafeExactBlockSupport GProgram.G5.ObservedLiftedBlocks
open GProgram.G5.Normalization
open scoped Classical
variable {V E X V₂ E₂ : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

/-- Existing tree-level root-suppression/cluster equivalence, lifted once to
one source's normalized union. This helper has no rival-carrier elaboration. -/
lemma normalized_quartet_mem_iff_cluster
    (N : RootedBinary V E X) (q : Fin 4 ↪ X) (r : Nanuq.Quartet.Resolution) :
    r ∈ normalizedDisplayedCutQuartets N q ↔
      ∃ D ∈ normalizedDisplayedClusters N,
        ((((resolutionPermutation r).trans q) 0 ∈ D ∧ ((resolutionPermutation r).trans q) 1 ∈ D ∧
          ((resolutionPermutation r).trans q) 2 ∉ D ∧ ((resolutionPermutation r).trans q) 3 ∉ D) ∨
        (((resolutionPermutation r).trans q) 2 ∈ D ∧ ((resolutionPermutation r).trans q) 3 ∈ D ∧
          ((resolutionPermutation r).trans q) 0 ∉ D ∧ ((resolutionPermutation r).trans q) 1 ∉ D)) := by
  simp only [normalizedDisplayedCutQuartets,Finset.mem_filter,mem_allResolutions,true_and]
  constructor
  · rintro ⟨S,T,hT,hr⟩
    have hlabels : T.leaves = Finset.univ := by
      have h := prunedAt_exact_leaves N S Finset.univ hT
      rw [sampledDescendants_root] at h
      simpa only [Genealogy.optionLeaves] using h
    obtain ⟨D,hD,hside⟩ :=
      (root_suppressed_cut_quartet_iff_cluster_quartet T ((resolutionPermutation r).trans q)
        (by intro i; rw [hlabels]; exact Finset.mem_univ _)).mp hr
    refine ⟨D,?_,hside⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,S,T,hT,hD⟩
  · rintro ⟨D,hD,hside⟩
    obtain ⟨S,T,hT,hDT⟩ := (Finset.mem_filter.mp hD).2
    have hlabels : T.leaves = Finset.univ := by
      have h := prunedAt_exact_leaves N S Finset.univ hT
      rw [sampledDescendants_root] at h
      simpa only [Genealogy.optionLeaves] using h
    refine ⟨S,T,hT,?_⟩
    exact (root_suppressed_cut_quartet_iff_cluster_quartet T ((resolutionPermutation r).trans q)
      (by intro i; rw [hlabels]; exact Finset.mem_univ _)).mpr ⟨D,hDT,hside⟩

/-- Unchanged optional consequence: equality of the full normalized cluster
unions implies equality of the normalized quartet unions. -/
theorem normalized_quartets_eq_of_cluster_unions
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (heq : normalizedDisplayedClusters N = normalizedDisplayedClusters N₂) :
    ∀ q : Fin 4 ↪ X, normalizedDisplayedCutQuartets N q = normalizedDisplayedCutQuartets N₂ q := by
  intro q
  ext r
  rw [normalized_quartet_mem_iff_cluster N q r,normalized_quartet_mem_iff_cluster N₂ q r,heq]

#print axioms normalized_quartet_mem_iff_cluster
#print axioms normalized_quartets_eq_of_cluster_unions
end GProgram.G5.M3NormalizedClusterSplitIdentification
