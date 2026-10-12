import G5OriginalPruningClusterPreservation
import G5ComponentCalendarCoverage

/-!
# Actual normalized original switching trees have the original quartet cuts
Contributor: dot / OpenAI, 2026-10-03.
The tree is produced by the actual pruning/unary evaluator, not supplied as an
abstract target. The quartet predicate is exactly the rooted-cluster criterion
stated in G5-NONPLANAR-CALENDAR-QUARTETS.md section 7. All original taxa on the
quartet are retained; unrelated unsampled labels and dead branches are removed.
-/
namespace GProgram.G5.Normalization
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

lemma sampled_sibling_descendants_disjoint (N : RootedBinary V E X) (S : N.Switching)
    (A : Finset X) {v : V} {e f : S.Edge} (he : S.graph.source e = v)
    (hf : S.graph.source f = v) (hef : e ≠ f) :
    Disjoint (sampledDescendants N S A (S.graph.target e)) (sampledDescendants N S A (S.graph.target f)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hd := (Finset.mem_filter.mp hx).2
  have hdf := (Finset.mem_filter.mp hy).2
  obtain ⟨es,hp⟩ := exists_edgePath_of_directed hd
  have hfn : f ∉ es := by
    intro hfm
    have hv := GProgram.G5.ComponentCalendar.EdgePath.source_reachable_of_mem hp hfm
    rw [hf] at hv
    exact S.selected_acyclic v (Relation.TransGen.head' ⟨e,he,rfl⟩ hv)
  have hpath := hp.reach_without_of_not_mem hfn
  have hstart : S.graph.ReachWithout f (S.graph.source f) (S.graph.target e) :=
    Relation.ReflTransGen.single ⟨e,hef,Or.inl ⟨he.trans hf.symm,rfl⟩⟩
  have hs := hstart.trans hpath
  have hbridge := S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f
  have ht := (S.graph.target_side_iff_descendant S.selected_uniqueIncoming S.selected_acyclic f (N.leaf x)).mpr hdf
  exact S.graph.bridge_sides_disjoint hbridge hs ht

/-- Actual normalized source trees contain every retained original taxon at
most once. This is derived from original switching parent uniqueness. -/
theorem prunedAt_wellLabelled (N : RootedBinary V E X) (S : N.Switching) (A : Finset X)
    {v : V} {T : Option (Genealogy X)} (eval : PrunedAt N S A v T) : Genealogy.optionWellLabelled T := by
  induction eval with
  | taxon x => split_ifs <;> simp [Genealogy.optionWellLabelled,Genealogy.WellLabelled]
  | dead => trivial
  | unary v hn e hout child ih => exact ih
  | binary v hn e f hef hout left right ihl ihr =>
    apply Genealogy.joinPruned_wellLabelled _ _ ihl ihr
    rw [prunedAt_exact_leaves N S A left,prunedAt_exact_leaves N S A right]
    have hem : e ∈ outgoing N S v := by rw [hout]; simp
    have hfm : f ∈ outgoing N S v := by rw [hout]; simp
    exact sampled_sibling_descendants_disjoint N S A (Finset.mem_filter.mp hem).2 (Finset.mem_filter.mp hfm).2 hef

lemma sampledDescendants_root (N : RootedBinary V E X) (S : N.Switching) (A : Finset X) :
    sampledDescendants N S A N.root = A := by
  ext x
  simp [sampledDescendants,S.selected_rooted]

/-- Actual displayed rooted tree exists with precisely the original selected
labels, after real empty-twig deletion and unary/root-chain suppression. -/
theorem nonempty_root_pruning_tree_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (S : N.Switching) (A : Finset X) (hA : A.Nonempty) :
    ∃ T : Genealogy X, PrunedAt N S A N.root (some T) ∧ T.WellLabelled ∧ T.leaves = A := by
  obtain ⟨O,hO⟩ := original_switching_pruning_exists N C S A N.root
  have hl := prunedAt_exact_leaves N S A hO
  rw [sampledDescendants_root] at hl
  cases O with
  | none => rw [←hl] at hA; exact False.elim (Finset.not_nonempty_empty hA)
  | some T => exact ⟨T,hO,prunedAt_wellLabelled N S A hO,hl⟩

/-- The documented cluster criterion for a resolved unrooted quartet. -/
def treeHasQuartet (T : Genealogy X) (q : Fin 4 ↪ X) : Prop :=
  ∃ D ∈ treeClusters T,
    (q 0 ∈ D ∧ q 1 ∈ D ∧ q 2 ∉ D ∧ q 3 ∉ D) ∨
    (q 2 ∈ D ∧ q 3 ∈ D ∧ q 0 ∉ D ∧ q 1 ∉ D)

/-- Pruning and unary suppression preserve exact actual quartet cuts in BOTH
directions. No cluster-preservation premise or selected-tree oracle is supplied. -/
theorem pruned_tree_quartet_iff_original_cut (N : RootedBinary V E X) (S : N.Switching)
    (A : Finset X) (q : Fin 4 ↪ X) (hqA : ∀ i, q i ∈ A) {T : Genealogy X}
    (eval : PrunedAt N S A N.root (some T)) :
    treeHasQuartet T q ↔ S.graph.HasQuartet (N.leaf (q 0)) (N.leaf (q 1)) (N.leaf (q 2)) (N.leaf (q 3)) := by
  have hclusters := prunedAt_exact_original_clusters N S A eval
  have hmem (v : V) (i : Fin 4) : q i ∈ sampledDescendants N S A v ↔ S.graph.DReach v (N.leaf (q i)) := by
    simp [sampledDescendants,hqA i]
  constructor
  · rintro ⟨D,hD,hside⟩
    obtain ⟨hnD,v,_,hdesc⟩ := (hclusters D).mp hD
    have hv : v ≠ N.root := by
      intro he
      subst v
      rw [sampledDescendants_root] at hdesc
      rcases hside with h | h
      · exact h.2.2.1 (hdesc ▸ hqA 2)
      · exact h.2.2.1 (hdesc ▸ hqA 0)
    obtain ⟨e,hte⟩ := S.selected_parent hv
    have hb := S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic e
    have htarget (i : Fin 4) (hi : q i ∈ D) : S.graph.ReachWithout e (S.graph.target e) (N.leaf (q i)) := by
      apply (S.graph.target_side_iff_descendant S.selected_uniqueIncoming S.selected_acyclic e _).mpr
      rw [hte]
      apply (hmem v i).mp
      rwa [hdesc]
    have hsource (i : Fin 4) (hi : q i ∉ D) : S.graph.ReachWithout e (S.graph.source e) (N.leaf (q i)) := by
      rcases S.graph.edge_side_cover e (S.selected_connected _ _) with hs | ht
      · exact hs
      · have hd := (S.graph.target_side_iff_descendant S.selected_uniqueIncoming S.selected_acyclic e _).mp ht
        rw [hte] at hd
        have hm := (hmem v i).mpr hd
        rw [hdesc] at hm
        exact False.elim (hi hm)
    refine ⟨e,hb,?_⟩
    rcases hside with h | h
    · exact Or.inr ⟨hsource 2 h.2.2.1,hsource 3 h.2.2.2,htarget 0 h.1,htarget 1 h.2.1⟩
    · exact Or.inl ⟨hsource 0 h.2.2.1,hsource 1 h.2.2.2,htarget 2 h.1,htarget 3 h.2.1⟩
  · rintro ⟨e,hb,hside⟩
    let D := sampledDescendants N S A (S.graph.target e)
    have htarget (i : Fin 4) (hi : S.graph.ReachWithout e (S.graph.target e) (N.leaf (q i))) : q i ∈ D :=
      (hmem _ i).mpr ((S.graph.target_side_iff_descendant S.selected_uniqueIncoming S.selected_acyclic e _).mp hi)
    have hsource (i : Fin 4) (hi : S.graph.ReachWithout e (S.graph.source e) (N.leaf (q i))) : q i ∉ D := by
      intro hm
      have hd := (hmem _ i).mp hm
      have ht := (S.graph.target_side_iff_descendant S.selected_uniqueIncoming S.selected_acyclic e _).mpr hd
      exact S.graph.bridge_sides_disjoint hb hi ht
    have hnD : D.Nonempty := by
      rcases hside with h | h
      · exact ⟨q 2,htarget 2 h.2.2.1⟩
      · exact ⟨q 0,htarget 0 h.2.2.1⟩
    refine ⟨D,(hclusters D).mpr ⟨hnD,S.graph.target e,S.selected_rooted _,rfl⟩,?_⟩
    rcases hside with h | h
    · exact Or.inr ⟨htarget 2 h.2.2.1,htarget 3 h.2.2.2,hsource 0 h.1,hsource 1 h.2.1⟩
    · exact Or.inl ⟨htarget 0 h.2.2.1,htarget 1 h.2.2.2,hsource 2 h.1,hsource 3 h.2.1⟩

#print axioms prunedAt_wellLabelled
#print axioms nonempty_root_pruning_tree_exists
#print axioms pruned_tree_quartet_iff_original_cut
end GProgram.G5.Normalization
