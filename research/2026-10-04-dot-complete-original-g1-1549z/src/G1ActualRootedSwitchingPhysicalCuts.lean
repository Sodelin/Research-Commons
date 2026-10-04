import G1SemidirectedSwitchingRoundTrip

/-! Physical EDGE DELETION cuts of an actual rooted switching tree equal
the inherited normalized pruning/root-suppressed cut serialization. This
is an incidence/path theorem, not a supplied target equality. -/
namespace G1ActualRootedSwitchingPhysicalCuts
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest GProgram.G5.Normalization
open G1ActualSelectedClusterTransport G1ActualDisplayedClusterSplitTransport
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_tree_target_side_iff_descendant {W F : Type*} (G : EdgeGraph W F)
    (hu : G.UniqueIncoming) (ha : G.Acyclic) (e : F) (v : W) :
    G.ReachWithout e (G.target e) v ↔ G.DReach (G.target e) v := by
  have hb := G.uniqueIncoming_all_bridges hu ha e
  constructor
  · intro h
    apply G.ureach_preserves (P := fun v => G.DReach (G.target e) v) (keep := fun f => f ≠ e) _ h .refl
    intro a b hab hdesc
    obtain ⟨f,hfe,hinc⟩ := hab
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact hdesc.tail ⟨f,hs,ht⟩
    · rw [← ht] at hdesc
      rw [← hs]
      exact G.descendant_parent_of_other_edge hu e f hfe hdesc
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact G.bridge_target_forward_closed hb hs ih

noncomputable def actualSelectedTargetSide (N : RootedBinary V E X) (S : N.Switching)
    (panel : Finset X) (e : S.Edge) : Finset X :=
  panel.filter (fun x => S.graph.ReachWithout e (S.graph.target e) (N.leaf x))

theorem actual_selected_target_side_descendants (N : RootedBinary V E X) (S : N.Switching)
    (panel : Finset X) (e : S.Edge) :
    actualSelectedTargetSide N S panel e = sampledDescendants N S panel (S.graph.target e) := by
  ext x
  simp only [actualSelectedTargetSide,sampledDescendants,Finset.mem_filter]
  exact and_congr_right (fun _ => actual_tree_target_side_iff_descendant S.graph S.selected_uniqueIncoming S.selected_acyclic e _)

noncomputable def actualRootedSwitchingPhysicalCuts (N : RootedBinary V E X) (S : N.Switching)
    (panel : Finset X) : Finset (Finset (Finset X)) :=
  ((Finset.univ.image (actualSelectedTargetSide N S panel)).filter
    (fun D => D.Nonempty ∧ (panel \ D).Nonempty)).image (fun D => {D,panel \ D})

lemma actual_physical_target_sides_iff_clusters (N : RootedBinary V E X) (S : N.Switching)
    (panel D : Finset X) :
    D ∈ (Finset.univ.image (actualSelectedTargetSide N S panel)).filter
      (fun D => D.Nonempty ∧ (panel \ D).Nonempty) ↔
    D ∈ (selectedClusters N S panel).filter
      (fun D => D ⊆ panel ∧ D.Nonempty ∧ (panel \ D).Nonempty) := by
  rw [Finset.mem_filter,Finset.mem_filter,mem_selectedClusters,Finset.mem_image]
  constructor
  · rintro ⟨⟨e,_,he⟩,hn,hcomp⟩
    have hd := actual_selected_target_side_descendants N S panel e
    refine ⟨⟨hn,⟨S.graph.target e,hd.symm.trans he⟩⟩,?_,hn,hcomp⟩
    rw [← he]
    exact Finset.filter_subset _ _
  · rintro ⟨⟨hn,v,hv⟩,hsub,_,hcomp⟩
    have hnonroot : v ≠ N.root := by
      intro he
      rw [he,sampledDescendants_root] at hv
      have hc : (panel \ D) = ∅ := by rw [← hv]; simp
      exact (Finset.nonempty_iff_ne_empty.mp hcomp) hc
    obtain ⟨e,ht⟩ := S.selected_parent hnonroot
    refine ⟨⟨e,Finset.mem_univ _,?_⟩,hn,hcomp⟩
    rw [actual_selected_target_side_descendants,ht,hv]

/-- Deleting actual selected ORIGINAL edge IDs, then retaining their proper
unordered taxon cuts, gives exactly the actual normalized unrooted tree. -/
theorem actual_rooted_physical_cuts_iff_normalized_tree (N : RootedBinary V E X) (S : N.Switching)
    (panel : Finset X) {T : Genealogy X} (eval : PrunedAt N S panel N.root (some T)) :
    actualRootedSwitchingPhysicalCuts N S panel = rootSuppressedCuts T := by
  rw [actualRootedSwitchingPhysicalCuts,actual_pruned_root_splits N S panel eval]
  congr 1
  ext D
  exact actual_physical_target_sides_iff_clusters N S panel D

#print axioms actual_rooted_physical_cuts_iff_normalized_tree
end G1ActualRootedSwitchingPhysicalCuts
