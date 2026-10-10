import G5M3NormalizedClusterSplitIdentification

/-! Optional downstream quartet consequence, extracted unchanged after the original
combined module exhausted its800000-heartbeat elaboration budget. Pending/unverified.
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

set_option maxHeartbeats 800000 in
/-- The already-defined normalized quartet union is a consequence of the full
cluster union, rather than being substituted for the stronger target. -/
theorem normalized_quartets_eq_of_cluster_unions
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (heq : normalizedDisplayedClusters N = normalizedDisplayedClusters N₂) :
    ∀ q : Fin 4 ↪ X, normalizedDisplayedCutQuartets N q = normalizedDisplayedCutQuartets N₂ q := by
  have transfer {V₁ E₁ V₃ E₃ : Type*}
      [Fintype V₁] [Fintype E₁] [DecidableEq V₁] [DecidableEq E₁]
      [Fintype V₃] [Fintype E₃] [DecidableEq V₃] [DecidableEq E₃]
      (M : RootedBinary V₁ E₁ X) (M₃ : RootedBinary V₃ E₃ X)
      (hc : normalizedDisplayedClusters M = normalizedDisplayedClusters M₃)
      (q : Fin 4 ↪ X) (r : Nanuq.Quartet.Resolution) :
      r ∈ normalizedDisplayedCutQuartets M q → r ∈ normalizedDisplayedCutQuartets M₃ q := by
    simp only [normalizedDisplayedCutQuartets,Finset.mem_filter,mem_allResolutions,true_and]
    rintro ⟨S,T,hT,hr⟩
    have labels (M' : RootedBinary V₁ E₁ X) (S' : M'.Switching) (T' : Genealogy X)
        (hT' : PrunedAt M' S' Finset.univ M'.root (some T')) : T'.leaves = Finset.univ := by
      have h := prunedAt_exact_leaves M' S' Finset.univ hT'
      rw [sampledDescendants_root] at h
      simpa only [Genealogy.optionLeaves] using h
    have hlabels := labels M S T hT
    have hquartet := (root_suppressed_cut_quartet_iff_cluster_quartet T ((resolutionPermutation r).trans q)
      (by intro i; rw [hlabels]; exact Finset.mem_univ _)).mp hr
    obtain ⟨D,hD,hside⟩ := hquartet
    have hD₃ : D ∈ normalizedDisplayedClusters M₃ := by
      rw [←hc]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,S,T,hT,hD⟩
    obtain ⟨S₃,T₃,hT₃,hD₃⟩ := (Finset.mem_filter.mp hD₃).2
    have hlabels₃ : T₃.leaves = Finset.univ := by
      have h := prunedAt_exact_leaves M₃ S₃ Finset.univ hT₃
      rw [sampledDescendants_root] at h
      simpa only [Genealogy.optionLeaves] using h
    refine ⟨S₃,T₃,hT₃,?_⟩
    exact (root_suppressed_cut_quartet_iff_cluster_quartet T₃ ((resolutionPermutation r).trans q)
      (by intro i; rw [hlabels₃]; exact Finset.mem_univ _)).mpr ⟨D,hD₃,hside⟩
  intro q
  ext r
  exact ⟨transfer N N₂ heq q r,transfer N₂ N heq.symm q r⟩


#print axioms normalized_quartets_eq_of_cluster_unions
end GProgram.G5.M3NormalizedClusterSplitIdentification
