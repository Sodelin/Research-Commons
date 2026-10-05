import G1SelectedOriginalDeletionPathEquivalence

/-! The exact root-suppression cases for ACTUAL switching trees. With one
selected root arc its descendant side is all taxa and contributes no cut.
With both selected, their two proper cuts are the same unordered cut. -/
namespace G1ActualSelectedRootCutCases
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization G1ActualFormerRootPorts
open G1ActualRootedSwitchingPhysicalCuts G1SelectedOriginalDeletionPathEquivalence
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_sole_root_arc_reaches_every_leaf (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (hn : ¬ S.keep ports.second) (x : X) :
    S.graph.DReach (N.graph.target ports.first) (N.leaf x) := by
  rcases Relation.ReflTransGen.cases_head (S.selected_rooted (N.leaf x)) with he | ⟨v,step,tail⟩
  · exact False.elim (N.leaf_ne_root x he.symm)
  · obtain ⟨e,hs,ht⟩ := step
    rcases ports.exhaustive e.val hs with hf | hsecond
    · have htarget : N.graph.target ports.first = v := hf ▸ ht
      simpa only [EdgeGraph.DReach,htarget] using tail
    · exact False.elim (hn (hsecond ▸ e.property))

theorem actual_single_root_arc_descendants_full (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (hn : ¬ S.keep ports.second) (panel : Finset X) :
    sampledDescendants N S panel (N.graph.target ports.first) = panel := by
  ext x
  simp [sampledDescendants,actual_sole_root_arc_reaches_every_leaf N ports S hn x]

lemma actual_root_other_side_iff_descendant (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (hf : S.keep ports.first) (hs : S.keep ports.second) (x : X) :
    S.graph.ReachWithout ⟨ports.first,hf⟩ N.root (N.leaf x) ↔
      S.graph.DReach (N.graph.target ports.second) (N.leaf x) := by
  let first : S.Edge := ⟨ports.first,hf⟩
  let second : S.Edge := ⟨ports.second,hs⟩
  constructor
  · intro h
    have hclosed : ∀ ⦃a b⦄, S.graph.UStep (fun f => f ≠ first) a b →
        (a = N.root ∨ S.graph.DReach (N.graph.target ports.second) a) →
        b = N.root ∨ S.graph.DReach (N.graph.target ports.second) b := by
      intro a b hab ha
      obtain ⟨f,hne,hinc⟩ := hab
      rcases ha with hroot | hdesc
      · rcases hinc with ⟨hsource,htarget⟩ | ⟨hsource,htarget⟩
        · have hsource' : N.graph.source f.val = N.root := hsource.trans hroot
          rcases ports.exhaustive f.val hsource' with he | he
          · exact False.elim (hne (Subtype.ext he))
          · have ht : N.graph.target ports.second = b := he ▸ htarget
            exact Or.inr (ht ▸ Relation.ReflTransGen.refl)
        · exact False.elim (N.edge_target_ne_root f.val (htarget.trans hroot))
      · rcases hinc with ⟨hsource,htarget⟩ | ⟨hsource,htarget⟩
        · exact Or.inr (hdesc.tail ⟨f,hsource,htarget⟩)
        · by_cases hsecond : f = second
          · exact Or.inl (hsource.symm.trans (hsecond ▸ ports.source_second))
          · rw [← htarget] at hdesc
            rw [← hsource]
            exact Or.inr (S.graph.descendant_parent_of_other_edge S.selected_uniqueIncoming second f hsecond hdesc)
    have hside := S.graph.ureach_preserves hclosed h (Or.inl rfl)
    exact hside.resolve_left (N.leaf_ne_root x)
  · intro hdesc
    have hn : ¬ S.graph.DReach (N.graph.target ports.second) (S.graph.source first) := by
      intro hreturn
      have hr : S.graph.source first = N.root := ports.source_first
      rw [hr] at hreturn
      exact S.selected_acyclic N.root (Relation.TransGen.head' ⟨second,ports.source_second,rfl⟩ hreturn)
    have htail := actual_dreach_without_of_source_unreachable S.graph first hdesc hn
    have hhead : S.graph.ReachWithout first N.root (N.graph.target ports.second) :=
      S.graph.ureach_single ⟨second,(fun he => ports.different (congrArg Subtype.val he).symm),Or.inl ⟨ports.source_second,rfl⟩⟩
    exact hhead.trans htail

/-- Actual complementary sides, proved from graph deletion and unique
incoming-edge tree structure, not merely from a binary renderer convention. -/
theorem actual_two_selected_root_clusters_complement (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (hf : S.keep ports.first) (hs : S.keep ports.second) (panel : Finset X) :
    sampledDescendants N S panel (N.graph.target ports.second) =
      panel \ sampledDescendants N S panel (N.graph.target ports.first) := by
  let first : S.Edge := ⟨ports.first,hf⟩
  have hb := S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic first
  ext x
  simp only [sampledDescendants,Finset.mem_filter,Finset.mem_sdiff]
  constructor
  · rintro ⟨hx,hdescSecond⟩
    refine ⟨hx,?_⟩
    rintro ⟨_,hdescFirst⟩
    have hsource := (actual_root_other_side_iff_descendant N ports S hf hs x).mpr hdescSecond
    have htarget := (actual_tree_target_side_iff_descendant S.graph S.selected_uniqueIncoming S.selected_acyclic first _).mpr hdescFirst
    exact S.graph.bridge_sides_disjoint hb (ports.source_first.symm ▸ hsource) htarget
  · rintro ⟨hx,hn⟩
    have hnDesc : ¬ S.graph.DReach (N.graph.target ports.first) (N.leaf x) := fun h => hn ⟨hx,h⟩
    have hcover := S.graph.edge_side_cover first (S.selected_connected (S.graph.source first) (N.leaf x))
    rcases hcover with hsource | htarget
    · refine ⟨hx,(actual_root_other_side_iff_descendant N ports S hf hs x).mp ?_⟩
      simpa only [show S.graph.source first = N.root from ports.source_first] using hsource
    · exact False.elim (hnDesc ((actual_tree_target_side_iff_descendant S.graph S.selected_uniqueIncoming S.selected_acyclic first _).mp htarget))

#print axioms actual_two_selected_root_clusters_complement
end G1ActualSelectedRootCutCases
