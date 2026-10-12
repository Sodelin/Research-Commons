import G1ActualDisplayedTreeFamily

/-! Complete co-occurring cut SYSTEMS of actual normalized switching trees
after the documented binary-root suppression. Each family member comes from
one entire actual tree. This is stronger than the union of displayed splits;
it is an explicit cut representation, with rooted tree families retained. -/
namespace G1ActualWholeUnrootedCutTreeFamily
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.Normalization
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedTreeClusterUniqueness G1ActualDisplayedTreeFamily G1ActualDisplayedClusterSplitTransport
open G1ActualTwoPortBlob G1SplicedSourceAdmission G1CutChildPorts
open scoped Classical
variable {X : Type*} [Fintype X]

theorem unordered_tree_clusters {a b : Genealogy X} (h : UnorderedEquiv a b) :
    treeClusters a = treeClusters b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | graft h1 h2 ih1 ih2 => simp only [treeClusters,ih1,ih2,unordered_leaves h1,unordered_leaves h2]
  | swap a b => simp only [treeClusters,Finset.union_comm]

theorem unordered_root_suppressed_cuts {a b : Genealogy X} (h : UnorderedEquiv a b) :
    rootSuppressedCuts a = rootSuppressedCuts b := by
  simp only [rootSuppressedCuts,unordered_tree_clusters h,unordered_leaves h]

/-- The actual inherited root-suppression cut encoding descends to exactly
the child-swap quotient; it does not relabel taxa or flatten binary ancestry. -/
noncomputable def unrankedRootSuppressedCuts : UnrankedTree X → Finset (Finset (Finset X)) :=
  Quotient.lift rootSuppressedCuts (fun _ _ h => unordered_root_suppressed_cuts h)

variable {V E : Type*}
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def actualDisplayedUnrootedCutTreeFamily (N : RootedBinary V E X)
    (C : Calendar N.graph) (panel : Finset X) : Finset (Finset (Finset (Finset X))) :=
  (actualDisplayedRootedTrees N C panel).image unrankedRootSuppressedCuts

/-- Membership uses ONE actual switching and ONE evaluated tree with its
whole root-suppressed edge-cut system. It cannot mix cuts from rival trees. -/
theorem actual_unrooted_cut_tree_family_iff_evaluator (N : RootedBinary V E X)
    (C : Calendar N.graph) (panel : Finset X) (cuts : Finset (Finset (Finset X))) :
    cuts ∈ actualDisplayedUnrootedCutTreeFamily N C panel ↔
      ∃ S : N.Switching, ∃ t : Genealogy X, PrunedAt N S panel N.root (some t) ∧ rootSuppressedCuts t = cuts := by
  rw [actualDisplayedUnrootedCutTreeFamily,Finset.mem_image]
  constructor
  · rintro ⟨q,hq,he⟩
    obtain ⟨S,t,ht,rfl⟩ := (actual_displayed_rooted_tree_iff_evaluator N C panel q).mp hq
    exact ⟨S,t,ht,he⟩
  · rintro ⟨S,t,ht,he⟩
    exact ⟨toUnranked t,(actual_displayed_rooted_tree_iff_evaluator N C panel _).mpr ⟨S,t,ht,rfl⟩,he⟩

/-- The old proper-split UNION is explicitly obtained only AFTER preserving
each actual tree's complete cut system. Co-occurrence is retained beforehand. -/
theorem actual_whole_cut_family_union_is_proper_split_union (N : RootedBinary V E X)
    (C : Calendar N.graph) (panel : Finset X) :
    (actualDisplayedUnrootedCutTreeFamily N C panel).biUnion id = actualDisplayedSplits N panel := by
  ext cut
  rw [Finset.mem_biUnion,actual_displayed_splits_iff_normalized_evaluator N C panel cut]
  constructor
  · rintro ⟨cuts,hcuts,hcut⟩
    obtain ⟨S,t,ht,rfl⟩ := (actual_unrooted_cut_tree_family_iff_evaluator N C panel cuts).mp hcuts
    exact ⟨S,t,ht,hcut⟩
  · rintro ⟨S,t,ht,hcut⟩
    exact ⟨rootSuppressedCuts t,(actual_unrooted_cut_tree_family_iff_evaluator N C panel _).mpr ⟨S,t,ht,rfl⟩,hcut⟩

theorem actual_whole_unrooted_cut_tree_family_splice (N : RootedBinary V E X) (C : Calendar N.graph)
    (hc : CutChild N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (panel : Finset X) :
    actualDisplayedUnrootedCutTreeFamily (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C) panel =
      actualDisplayedUnrootedCutTreeFamily N C panel := by
  rw [actualDisplayedUnrootedCutTreeFamily,actualDisplayedUnrootedCutTreeFamily,
    actual_displayed_rooted_tree_family_splice]

/-- Equality of the actual whole rooted-tree families preserves EVERY
well-defined tree readout family, including a later explicit root-forgetting
implementation. No adjacency renderer or semidirected target is invented. -/
theorem actual_whole_tree_readout_family_splice {Output : Type*} [DecidableEq Output]
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hc : CutChild N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (panel : Finset X) (readout : UnrankedTree X → Output) :
    (actualDisplayedRootedTrees (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C) panel).image readout =
      (actualDisplayedRootedTrees N C panel).image readout := by
  rw [actual_displayed_rooted_tree_family_splice]

#print axioms actual_whole_unrooted_cut_tree_family_splice
#print axioms actual_whole_tree_readout_family_splice
end G1ActualWholeUnrootedCutTreeFamily
