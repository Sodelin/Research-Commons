import G1ActualDisplayedClusterSplitTransport

/-! Exact canonical raw and documented normalized displayed quartet unions
survive the constructed original splice. Actual pruning/child/root cut
correspondence is inherited and checked; no target identity is a premise. -/
namespace G1ActualDisplayedQuartetTransport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.Normalization
open GProgram.G5.AttainedChronology
open G1ActualTwoPortBlob G1BigonSpliceGraph G1SplicedSourceAdmission G1CutChildPorts
open G1SplicedOriginalSwitching G1ActualSelectedClusterTransport
open G1ActualDisplayedClusterSplitTransport
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

theorem actual_switching_resolution_splice (N : RootedBinary V E X) (C : Calendar N.graph)
    (hc : CutChild N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (S : N.Switching) (q : Fin 4 ↪ X) (r : Nanuq.Quartet.Resolution) :
    S.graph.Resolves (fun i => N.leaf (q i)) r ↔
      (restrictSwitching N hc b hb A S).graph.Resolves
        (fun i => (splicedNetwork N hc b hb A).leaf (q i)) r := by
  let M := splicedNetwork N hc b hb A
  let T := restrictSwitching N hc b hb A S
  have hpanel : (Finset.univ : Finset X).Nonempty := ⟨q 0,Finset.mem_univ _⟩
  obtain ⟨old,hold,_,_⟩ := nonempty_root_pruning_tree_exists N C S Finset.univ hpanel
  obtain ⟨new,hnew,_,_⟩ := nonempty_root_pruning_tree_exists M (splicedCalendar N hc b hb A C) T Finset.univ hpanel
  have hclusters : treeClusters old = treeClusters new := by
    rw [actual_pruned_root_clusters N S Finset.univ hold,actual_pruned_root_clusters M T Finset.univ hnew]
    exact (actual_selected_clusters_splice N hc b hb A S Finset.univ).symm
  rw [selected_resolution_iff_permuted_first N S q r,selected_resolution_iff_permuted_first M T q r]
  rw [←pruned_tree_quartet_iff_original_cut N S Finset.univ ((resolutionPermutation r).trans q)
      (fun _ => Finset.mem_univ _) hold,
    ←pruned_tree_quartet_iff_original_cut M T Finset.univ ((resolutionPermutation r).trans q)
      (fun _ => Finset.mem_univ _) hnew]
  unfold treeHasQuartet
  rw [hclusters]

theorem actual_raw_displayed_quartets_splice (N : RootedBinary V E X) (C : Calendar N.graph)
    (hc : CutChild N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (q : Fin 4 ↪ X) :
    (splicedNetwork N hc b hb A).rawDisplayedQuartets q = N.rawDisplayedQuartets q := by
  ext r
  rw [actual_raw_mem_iff_selected_resolves,actual_raw_mem_iff_selected_resolves]
  constructor
  · rintro ⟨T,hT⟩
    let S := liftSwitching N hc b hb A T
    refine ⟨S,(actual_switching_resolution_splice N C hc b hb A S q r).mpr ?_⟩
    rw [actual_restrict_lift_switching]
    exact hT
  · rintro ⟨S,hS⟩
    exact ⟨restrictSwitching N hc b hb A S,(actual_switching_resolution_splice N C hc b hb A S q r).mp hS⟩

theorem actual_normalized_displayed_quartets_splice (N : RootedBinary V E X) (C : Calendar N.graph)
    (hc : CutChild N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (q : Fin 4 ↪ X) :
    normalizedDisplayedCutQuartets (splicedNetwork N hc b hb A) q = normalizedDisplayedCutQuartets N q := by
  rw [←raw_displayed_equals_normalized_cut_quartets _ (splicedCalendar N hc b hb A C) q,
    ←raw_displayed_equals_normalized_cut_quartets N C q]
  exact actual_raw_displayed_quartets_splice N C hc b hb A q

#print axioms actual_normalized_displayed_quartets_splice
end G1ActualDisplayedQuartetTransport
