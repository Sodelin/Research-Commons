import G1ActualSelectedClusterTransport
import G5FairNormalizedCutQuartetIdentification

/-! Actual displayed rooted-cluster and unordered split unions survive the
constructed splice. The cut encoding matches proved actual pruning/unary/root
suppression, not a supplied target or semidirected-network convention. -/
namespace G1ActualDisplayedClusterSplitTransport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.Normalization
open G1ActualTwoPortBlob G1BigonSpliceGraph G1SplicedSourceAdmission G1CutChildPorts
open G1SplicedOriginalSwitching G1ActualSelectedClusterTransport
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def actualDisplayedClusters (N : RootedBinary V E X) (panel : Finset X) : Finset (Finset X) :=
  Finset.univ.biUnion (fun S : N.Switching => selectedClusters N S panel)

lemma mem_actualDisplayedClusters (N : RootedBinary V E X) (panel D : Finset X) :
    D ∈ actualDisplayedClusters N panel ↔ ∃ S : N.Switching, D ∈ selectedClusters N S panel := by
  simp [actualDisplayedClusters]

/-- Root/full and empty sides are removed, and complementary binary-root
child cuts are identified as one unordered split, using the inherited encoding. -/
noncomputable def actualDisplayedSplits (N : RootedBinary V E X) (panel : Finset X) :
    Finset (Finset (Finset X)) :=
  ((actualDisplayedClusters N panel).filter (fun D => D ⊆ panel ∧ D.Nonempty ∧ (panel \ D).Nonempty)).image
    (fun D => {D,panel \ D})

/-- Actual evaluator outputs have exactly the source-selected cluster set.
No pruning/cluster-preservation equation is assumed. -/
theorem actual_pruned_root_clusters (N : RootedBinary V E X) (S : N.Switching) (panel : Finset X)
    {T : Genealogy X} (eval : PrunedAt N S panel N.root (some T)) :
    treeClusters T = selectedClusters N S panel := by
  ext D
  rw [mem_selectedClusters]
  have h := prunedAt_exact_original_clusters N S panel eval D
  change D ∈ treeClusters T ↔ VertexClusterBelow N S panel N.root D at h
  rw [h]
  constructor
  · rintro ⟨hn,v,_,he⟩; exact ⟨hn,v,he⟩
  · rintro ⟨hn,v,he⟩; exact ⟨hn,v,S.selected_rooted v,he⟩

theorem actual_pruned_root_splits (N : RootedBinary V E X) (S : N.Switching) (panel : Finset X)
    {T : Genealogy X} (eval : PrunedAt N S panel N.root (some T)) :
    rootSuppressedCuts T =
      ((selectedClusters N S panel).filter (fun D => D ⊆ panel ∧ D.Nonempty ∧ (panel \ D).Nonempty)).image
        (fun D => {D,panel \ D}) := by
  have hl : T.leaves = panel := by
    have h := prunedAt_exact_leaves N S panel eval
    rw [sampledDescendants_root] at h
    exact h
  rw [rootSuppressedCuts,actual_pruned_root_clusters N S panel eval,hl]

/-- C is EXACTLY the union of clusters of actual evaluated normalized
switching trees. This binds the graph incidence definition to the documented
pruning/unary convention, including arbitrary selected taxon panels. -/
theorem actual_displayed_clusters_iff_normalized_evaluator (N : RootedBinary V E X)
    (C : Calendar N.graph) (panel D : Finset X) :
    D ∈ actualDisplayedClusters N panel ↔
      ∃ S : N.Switching, ∃ T : Genealogy X, PrunedAt N S panel N.root (some T) ∧ D ∈ treeClusters T := by
  rw [mem_actualDisplayedClusters]
  constructor
  · rintro ⟨S,hD⟩
    obtain ⟨hn,v,hv⟩ := (mem_selectedClusters N S panel D).mp hD
    obtain ⟨x,hx⟩ := hn
    have hpanel : panel.Nonempty := ⟨x,(Finset.mem_filter.mp (hv.symm ▸ hx)).1⟩
    obtain ⟨T,hT,_,_⟩ := nonempty_root_pruning_tree_exists N C S panel hpanel
    refine ⟨S,T,hT,?_⟩
    rw [actual_pruned_root_clusters N S panel hT]
    exact hD
  · rintro ⟨S,T,hT,hD⟩
    refine ⟨S,?_⟩
    rw [←actual_pruned_root_clusters N S panel hT]
    exact hD

/-- S is EXACTLY the distinct union of actual normalized unordered edge cuts,
with proper/full-root exclusion and complementary binary-root deduplication. -/
theorem actual_displayed_splits_iff_normalized_evaluator (N : RootedBinary V E X)
    (C : Calendar N.graph) (panel : Finset X) (cut : Finset (Finset X)) :
    cut ∈ actualDisplayedSplits N panel ↔
      ∃ S : N.Switching, ∃ T : Genealogy X, PrunedAt N S panel N.root (some T) ∧ cut ∈ rootSuppressedCuts T := by
  constructor
  · intro hcut
    obtain ⟨D,hD,he⟩ := Finset.mem_image.mp hcut
    obtain ⟨hC,hsub,hn,hnComp⟩ := Finset.mem_filter.mp hD
    obtain ⟨S,T,hT,hDtree⟩ := (actual_displayed_clusters_iff_normalized_evaluator N C panel D).mp hC
    refine ⟨S,T,hT,?_⟩
    rw [actual_pruned_root_splits N S panel hT]
    exact Finset.mem_image.mpr ⟨D,Finset.mem_filter.mpr
      ⟨by rwa [actual_pruned_root_clusters N S panel hT] at hDtree,hsub,hn,hnComp⟩,he⟩
  · rintro ⟨S,T,hT,hcut⟩
    rw [actual_pruned_root_splits N S panel hT] at hcut
    obtain ⟨D,hD,he⟩ := Finset.mem_image.mp hcut
    obtain ⟨hDsel,hsub,hn,hnComp⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_image.mpr ⟨D,Finset.mem_filter.mpr
      ⟨(mem_actualDisplayedClusters N panel D).mpr ⟨S,hDsel⟩,hsub,hn,hnComp⟩,he⟩

theorem actual_displayed_clusters_splice (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) (panel : Finset X) :
    actualDisplayedClusters (splicedNetwork N hc b hb A) panel = actualDisplayedClusters N panel := by
  ext D
  rw [mem_actualDisplayedClusters,mem_actualDisplayedClusters]
  constructor
  · rintro ⟨T,hT⟩
    let S := liftSwitching N hc b hb A T
    refine ⟨S,?_⟩
    rw [← actual_selected_clusters_splice N hc b hb A S panel,actual_restrict_lift_switching]
    exact hT
  · rintro ⟨S,hS⟩
    refine ⟨restrictSwitching N hc b hb A S,?_⟩
    rw [actual_selected_clusters_splice]
    exact hS

theorem actual_displayed_splits_splice (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) (panel : Finset X) :
    actualDisplayedSplits (splicedNetwork N hc b hb A) panel = actualDisplayedSplits N panel := by
  rw [actualDisplayedSplits,actualDisplayedSplits,actual_displayed_clusters_splice]

#print axioms actual_displayed_clusters_splice
#print axioms actual_displayed_splits_splice
end G1ActualDisplayedClusterSplitTransport
