import Astra.BridgeTaxonCuts
import G1ActualSelectedClusterTransport
import G5NormalizedSwitchingQuartetCompatibility

/-! Source-only bound on actual distinct bridge taxon cuts.
Choose an actual original switching and its derived pruned genealogy. Every
bridge cut is one of that tree's proper clusters; the tree is not supplied.
This does not count unequal cells per cut or protected dependencies. -/
namespace Astra.BridgeCutClassBudget

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5 GProgram.G5.Normalization GProgram.SourceForest
open G1ActualSelectedClusterTransport Astra.BridgeTaxonCuts
open scoped Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A binary genealogy with no repeated taxon has at most twice its leaf
count minus one distinct clusters, including its root cluster. -/
theorem tree_clusters_card (T : Genealogy X) (hw : T.WellLabelled) :
    (treeClusters T).card + 1 ≤ 2 * T.leaves.card := by
  induction T with
  | leaf x => simp [treeClusters, Genealogy.leaves]
  | graft l r ihl ihr =>
    have hl := ihl hw.1
    have hr := ihr hw.2.1
    have hu : (treeClusters (.graft l r)).card ≤
        (treeClusters l).card + (treeClusters r).card + 1 := by
      exact (Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) 1)
    have hf : (Genealogy.leaves (.graft l r)).card = l.leaves.card + r.leaves.card :=
      Finset.card_union_of_disjoint hw.2.2
    omega

theorem proper_tree_clusters_card (T : Genealogy X) (hw : T.WellLabelled) :
    ((treeClusters T).erase T.leaves).card + 2 ≤ 2 * T.leaves.card := by
  have hc := tree_clusters_card T hw
  have he := Finset.card_erase_add_one (tree_root_cluster_mem T)
  omega

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Distinct actual nonempty selected clades, with the full root clade removed. -/
noncomputable def properSelectedClusters (N : RootedBinary V E X) (S : N.Switching) :
    Finset (Finset X) := (selectedClusters N S Finset.univ).erase Finset.univ

theorem selected_clusters_eq_pruned_tree (N : RootedBinary V E X) (S : N.Switching)
    (T : Genealogy X) (ht : PrunedAt N S Finset.univ N.root (some T)) :
    selectedClusters N S Finset.univ = treeClusters T := by
  ext A
  rw [mem_selectedClusters]
  have hc := prunedAt_exact_original_clusters N S Finset.univ ht A
  constructor
  · rintro ⟨hA, v, hv⟩
    exact hc.mpr ⟨hA, v, S.selected_rooted v, hv⟩
  · intro hA
    obtain ⟨hn, v, _, hv⟩ := hc.mp hA
    exact ⟨hn, v, hv⟩

/-- The actual pruning evaluator, not a supplied small tree, produces the
cluster budget for every original switching. -/
theorem actual_selected_cluster_budget (N : RootedBinary V E X)
    (C : Calendar N.graph) (S : N.Switching) :
    (properSelectedClusters N S).card + 2 ≤ 2 * Fintype.card X := by
  have hn : 0 < Fintype.card X := by
    have h := N.at_least_two_taxa
    omega
  letI : Nonempty X := Fintype.card_pos_iff.mp hn
  obtain ⟨T, ht, hw, hl⟩ := nonempty_root_pruning_tree_exists N C S
    Finset.univ Finset.univ_nonempty
  have hc := proper_tree_clusters_card T hw
  have he := selected_clusters_eq_pruned_tree N S T ht
  rw [hl, Finset.card_univ] at hc
  simpa only [properSelectedClusters, he] using hc

/-- This is the finite image of original bridge occurrences, with duplicate
taxon cuts counted once. No class partition or cell budget is supplied. -/
noncomputable def bridgeCutClasses (N : RootedBinary V E X) : Finset (Finset X) :=
  Finset.univ.image (bridgeTaxa N)

theorem bridge_cut_classes_subset (N : RootedBinary V E X) (S : N.Switching) :
    bridgeCutClasses N ⊆ properSelectedClusters N S := by
  intro A hA
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hA
  apply Finset.mem_erase.mpr
  refine ⟨bridgeTaxa_proper N e, ?_⟩
  rw [mem_selectedClusters]
  refine ⟨bridgeTaxa_nonempty N e, N.graph.target e.val, ?_⟩
  ext x
  simp only [sampledDescendants, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (mem_bridgeTaxa_iff_selected_descendant N S e x).symm

/-- All actual proper bridge cuts fit in one actual displayed genealogy.
The conclusion precedes any conditional bank/program or support argument. -/
theorem actual_bridge_cut_class_budget (N : RootedBinary V E X)
    (C : Calendar N.graph) (S : N.Switching) :
    (bridgeCutClasses N).card + 2 ≤ 2 * Fintype.card X := by
  have hs := Finset.card_le_card (bridge_cut_classes_subset N S)
  have ht := actual_selected_cluster_budget N C S
  omega

-- Future actual type/axiom requests; no execution receipt is claimed.
#print bridgeCutClasses
#check actual_bridge_cut_class_budget
#print axioms tree_clusters_card
#print axioms proper_tree_clusters_card
#print axioms selected_clusters_eq_pruned_tree
#print axioms actual_selected_cluster_budget
#print axioms bridge_cut_classes_subset
#print axioms actual_bridge_cut_class_budget

end Astra.BridgeCutClassBudget
