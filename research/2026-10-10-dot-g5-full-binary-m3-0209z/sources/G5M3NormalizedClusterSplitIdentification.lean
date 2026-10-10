import G5ObservedLiftedBlocks
import G5FairNormalizedCutQuartetIdentification

/-!
# Arbitrary-weight M3 consumer for the documented full cluster and split unions
Contributor: dot / OpenAI, 10 October 2026.
UNCOMPILED CANDIDATE. This reuses actual original-switching pruning and unary
suppression, and the accepted rootSuppressedCuts encoding of binary-root
suppression. It does not infer a full split union from quartet equality, or
claim the co-occurrence family of displayed trees is identified.
The categorical bounded-indegree HG extension is a separate formal obligation.
-/
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

/-- Full rooted cluster UNION of actual pruned/unary-suppressed original
switchings. Singletons and the full original label set are retained. -/
noncomputable def normalizedDisplayedClusters (N : RootedBinary V E X) : Finset (Finset X) :=
  Finset.univ.filter (fun D => ∃ S : N.Switching, ∃ T : Genealogy X,
    PrunedAt N S Finset.univ N.root (some T) ∧ D ∈ treeClusters T)

/-- Nontrivial unordered edge-split UNION using the existing actual
binary-root-suppressed cut encoding. Both sides must have at least two taxa. -/
noncomputable def normalizedDisplayedSplits (N : RootedBinary V E X) : Finset (Finset (Finset X)) :=
  Finset.univ.filter (fun cut => (∀ D ∈ cut, 2 ≤ D.card) ∧
    ∃ S : N.Switching, ∃ T : Genealogy X,
      PrunedAt N S Finset.univ N.root (some T) ∧ cut ∈ rootSuppressedCuts T)

lemma mem_normalized_clusters_iff_vertex (N : RootedBinary V E X) (C : Calendar N.graph)
    (D : Finset X) :
    D ∈ normalizedDisplayedClusters N ↔ D.Nonempty ∧
      ∃ S : N.Switching, ∃ v : V, sampledDescendants N S Finset.univ v = D := by
  simp only [normalizedDisplayedClusters,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨S,T,hT,hD⟩
    obtain ⟨hD,v,_,hv⟩ := (prunedAt_exact_original_clusters N S Finset.univ hT D).mp hD
    exact ⟨hD,S,v,hv⟩
  · rintro ⟨hD,S,v,hv⟩
    obtain ⟨T,hT,_,_⟩ := nonempty_root_pruning_tree_exists N C S Finset.univ
      (hD.mono (Finset.subset_univ D))
    refine ⟨S,T,hT,?_⟩
    exact (prunedAt_exact_original_clusters N S Finset.univ hT D).mpr
      ⟨hD,v,S.selected_rooted v,hv⟩

lemma common_edge_population_block_eq_descendants
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (a : CommonSeed N) (e : (commonSwitching N H a).Edge) (A : Finset X) {t : ℝ}
    (ha : C.Active t e.val) :
    populationBlock N (commonRoutes N C H a) A C t (some e.val) =
      sampledDescendants N (commonSwitching N H a) A (N.graph.target e.val) := by
  ext x
  simp only [populationBlock,sampledDescendants,Finset.mem_filter,Occupies,ha,and_true,
    common_route_edge_iff_selected_descendant N C H a x e]

/-- Every nonempty normalized cluster is realized at a genuine finite original
calendar age. Non-root clusters use their positive incoming-edge interval;
the full root cluster uses the unchanged ancestral population. Conversely,
every nonempty COMMON population block is an actual switching cluster. -/
theorem vertex_cluster_iff_calendar_block
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (D : Finset X) (hD : D.Nonempty) (a0 : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0) :
    (∃ S : N.Switching, ∃ v : V, sampledDescendants N S Finset.univ v = D) ↔
      ∃ t : ℝ, a0 ≤ t ∧ PossibleBlock N C H Finset.univ D t := by
  constructor
  · rintro ⟨S,v,hv⟩
    obtain ⟨a,rfl⟩ := commonSwitching_covers N H S
    obtain ⟨x,hx⟩ := hD
    have hxv : (commonSwitching N H a).graph.DReach v (N.leaf x) := by
      have hmem : x ∈ sampledDescendants N (commonSwitching N H a) Finset.univ v := by rwa [hv]
      exact (Finset.mem_filter.mp hmem).2
    obtain ⟨es,hpath,_⟩ := selected_reach_original_kept_path N (commonSwitching N H a) hxv
    have hav : a0 ≤ C.age v := by
      rw [←htips x]
      exact C.age_le_of_directed hpath.directed
    refine ⟨C.age v,hav,?_⟩
    by_cases hvr : v = N.root
    · subst v
      rw [sampledDescendants_root] at hv
      exact ⟨a,none,(ancestral_block N C (commonRoutes N C H a) Finset.univ le_rfl).trans hv⟩
    · obtain ⟨e,hte⟩ := (commonSwitching N H a).selected_parent hvr
      change N.graph.target e.val = v at hte
      have ha : C.Active (C.age v) e.val := by
        have he := C.edge_older e.val
        rw [hte] at he
        exact ⟨by rw [hte],he⟩
      refine ⟨a,some e.val,?_⟩
      rw [common_edge_population_block_eq_descendants N C H a e Finset.univ ha,hte]
      exact hv
  · rintro ⟨t,_,a,pop,hblock⟩
    obtain ⟨x,hx⟩ := hD
    have hxpop : Occupies N (commonRoutes N C H a) C t x pop := by
      have hm : x ∈ populationBlock N (commonRoutes N C H a) Finset.univ C t pop := by rwa [hblock]
      exact (Finset.mem_filter.mp hm).2
    cases pop with
    | none =>
      refine ⟨commonSwitching N H a,N.root,?_⟩
      rw [sampledDescendants_root]
      exact (ancestral_block N C (commonRoutes N C H a) Finset.univ hxpop).symm.trans hblock
    | some e =>
      let se : (commonSwitching N H a).Edge := ⟨e,common_route_kept N C H a x hxpop.1⟩
      exact ⟨commonSwitching N H a,N.graph.target e,
        (common_edge_population_block_eq_descendants N C H a se Finset.univ hxpop.2).symm.trans hblock⟩

lemma mem_normalized_clusters_iff_calendar_block
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (D : Finset X) (a0 : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0) :
    D ∈ normalizedDisplayedClusters N ↔ D.Nonempty ∧
      ∃ t : ℝ, a0 ≤ t ∧ PossibleBlock N C H Finset.univ D t := by
  rw [mem_normalized_clusters_iff_vertex N C D]
  constructor
  · rintro ⟨hD,hv⟩; exact ⟨hD,(vertex_cluster_iff_calendar_block N C H D hD a0 htips).mp hv⟩
  · rintro ⟨hD,ht⟩; exact ⟨hD,(vertex_cluster_iff_calendar_block N C H D hD a0 htips).mpr ht⟩

/-- Exact bridge to the already-defined binary-root-normalized split encoding.
This is a union statement, so a witnessing cluster may use its own switching. -/
lemma mem_normalized_splits_iff_cluster (N : RootedBinary V E X) (cut : Finset (Finset X)) :
    cut ∈ normalizedDisplayedSplits N ↔ ∃ D ∈ normalizedDisplayedClusters N,
      2 ≤ D.card ∧ 2 ≤ ((Finset.univ : Finset X) \ D).card ∧ cut = {D,Finset.univ \ D} := by
  simp only [normalizedDisplayedSplits,normalizedDisplayedClusters,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hsize,S,T,hT,hcut⟩
    have hlabels : T.leaves = Finset.univ := by
      have h := prunedAt_exact_leaves N S Finset.univ hT
      rw [sampledDescendants_root] at h
      simpa only [Genealogy.optionLeaves] using h
    obtain ⟨D,hD,hcut⟩ := Finset.mem_image.mp hcut
    obtain ⟨hcluster,_,_,_⟩ := Finset.mem_filter.mp hD
    rw [hlabels] at hcut
    refine ⟨D,⟨S,T,hT,hcluster⟩,?_,?_,hcut.symm⟩
    · apply hsize D; rw [←hcut]; exact Finset.mem_insert_self _ _
    · apply hsize (Finset.univ \ D); rw [←hcut]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · rintro ⟨D,⟨S,T,hT,hcluster⟩,hD,hcomp,rfl⟩
    have hlabels : T.leaves = Finset.univ := by
      have h := prunedAt_exact_leaves N S Finset.univ hT
      rw [sampledDescendants_root] at h
      simpa only [Genealogy.optionLeaves] using h
    refine ⟨?_,S,T,hT,?_⟩
    · intro F hF
      rcases Finset.mem_insert.mp hF with hF | hF
      · simpa only [hF] using hD
      · simpa only [Finset.mem_singleton.mp hF] using hcomp
    · apply Finset.mem_image.mpr
      refine ⟨D,Finset.mem_filter.mpr ⟨hcluster,tree_cluster_subset_leaves T hcluster,?_,?_⟩,?_⟩
      · exact Finset.card_pos.mp (by omega)
      · rw [hlabels]; exact Finset.card_pos.mp (by omega)
      · rw [hlabels]

/-- Full binary M3 upper bound for the documented normalized rooted-cluster
UNION and full nontrivial unordered split UNION. Arbitrary strictly interior
inheritance probabilities and source-specific constant positive rates are
allowed, with stored COMMON or current-owner INDEPENDENT routing at each
hybrid. Only ordinary original-tip three-copy calendar genealogy laws are
observed. The shared label order is constructed internally. -/
theorem m3_identifies_documented_full_cluster_split_unions
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (a0 : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (heq : ∀ tip : Fin 3 ↪ X, naturalObservedFullLaw N C tip H p common r =
      naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    normalizedDisplayedClusters N = normalizedDisplayedClusters N₂ ∧
      normalizedDisplayedSplits N = normalizedDisplayedSplits N₂ := by
  letI : LinearOrder X := sharedOriginalLabelOrder X
  have hblocks := m3_identifies_all_original_possible_blocks N C hcut H p common r
    N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ hX a0 htips htips₂ heq
  have hclusters : normalizedDisplayedClusters N = normalizedDisplayedClusters N₂ := by
    ext D
    rw [mem_normalized_clusters_iff_calendar_block N C H D a0 htips,
      mem_normalized_clusters_iff_calendar_block N₂ C₂ H₂ D a0 htips₂]
    constructor
    · rintro ⟨hD,t,ht,hblock⟩; exact ⟨hD,t,ht,(hblocks D hD t ht).mp hblock⟩
    · rintro ⟨hD,t,ht,hblock⟩; exact ⟨hD,t,ht,(hblocks D hD t ht).mpr hblock⟩
  refine ⟨hclusters,?_⟩
  ext cut
  rw [mem_normalized_splits_iff_cluster,mem_normalized_splits_iff_cluster,hclusters]



#print axioms vertex_cluster_iff_calendar_block
#print axioms mem_normalized_splits_iff_cluster
#print axioms m3_identifies_documented_full_cluster_split_unions
end GProgram.G5.M3NormalizedClusterSplitIdentification
