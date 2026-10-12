import G1UnrankedTreeClusterUniqueness
import G1ActualDisplayedQuartetTransport

/-! Entire finite families of ACTUAL normalized rooted unranked switching
trees. Whole tree co-occurrence is retained before taking any union target.
The actual pruning/unary evaluator supplies the tree, not an oracle. -/
namespace G1ActualDisplayedTreeFamily
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.Normalization
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedTreeClusterUniqueness G1ActualDisplayedClusterSplitTransport
open G1ActualTwoPortBlob G1SplicedSourceAdmission G1CutChildPorts G1SplicedOriginalSwitching
open G1ActualSelectedClusterTransport
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

theorem actual_pruning_unranked_unique (N : RootedBinary V E X) (S : N.Switching) (panel : Finset X)
    {a b : Option (Genealogy X)} (ha : PrunedAt N S panel N.root a) (hb : PrunedAt N S panel N.root b) :
    optionUnranked a = optionUnranked b := by
  have hla := prunedAt_exact_leaves N S panel ha
  have hlb := prunedAt_exact_leaves N S panel hb
  rw [sampledDescendants_root] at hla hlb
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hn : b.leaves.Nonempty := tree_leaves_nonempty b
      have he : b.leaves = ∅ := hlb.trans hla.symm
      rw [he] at hn
      exact False.elim (Finset.not_nonempty_empty hn)
  | some a =>
    cases b with
    | none =>
      have hn : a.leaves.Nonempty := tree_leaves_nonempty a
      have he : a.leaves = ∅ := hla.trans hlb.symm
      rw [he] at hn
      exact False.elim (Finset.not_nonempty_empty hn)
    | some b =>
      exact congrArg some (actual_tree_clusters_determine_unranked a b
        (prunedAt_wellLabelled N S panel ha) (prunedAt_wellLabelled N S panel hb)
        ((actual_pruned_root_clusters N S panel ha).trans (actual_pruned_root_clusters N S panel hb).symm))

noncomputable def actualNormalizedRootTree (N : RootedBinary V E X) (C : Calendar N.graph)
    (S : N.Switching) (panel : Finset X) : Option (UnrankedTree X) :=
  optionUnranked (Classical.choose (original_switching_pruning_exists N C S panel N.root))

theorem actual_normalized_root_tree_at_evaluation (N : RootedBinary V E X) (C : Calendar N.graph)
    (S : N.Switching) (panel : Finset X) {t : Option (Genealogy X)}
    (ht : PrunedAt N S panel N.root t) : actualNormalizedRootTree N C S panel = optionUnranked t :=
  actual_pruning_unranked_unique N S panel
    (Classical.choose_spec (original_switching_pruning_exists N C S panel N.root)) ht

noncomputable def actualDisplayedRootedTrees (N : RootedBinary V E X) (C : Calendar N.graph) (panel : Finset X) :
    Finset (UnrankedTree X) :=
  Finset.univ.biUnion (fun S : N.Switching => match actualNormalizedRootTree N C S panel with
    | none => ∅
    | some q => {q})

/-- Membership means an ACTUAL switching/evaluation with the entire tree,
not independent per-clade membership in a displayed cluster union. -/
theorem actual_displayed_rooted_tree_iff_evaluator (N : RootedBinary V E X) (C : Calendar N.graph)
    (panel : Finset X) (q : UnrankedTree X) :
    q ∈ actualDisplayedRootedTrees N C panel ↔
      ∃ S : N.Switching, ∃ t : Genealogy X, PrunedAt N S panel N.root (some t) ∧ toUnranked t = q := by
  rw [actualDisplayedRootedTrees,Finset.mem_biUnion]
  constructor
  · rintro ⟨S,_,hq⟩
    let t := Classical.choose (original_switching_pruning_exists N C S panel N.root)
    have ht := Classical.choose_spec (original_switching_pruning_exists N C S panel N.root)
    change PrunedAt N S panel N.root t at ht
    change q ∈ (match optionUnranked t with | none => ∅ | some q => {q}) at hq
    cases he : t with
    | none => simp [he,optionUnranked] at hq
    | some t =>
      refine ⟨S,t,he ▸ ht,?_⟩
      have hq' : q = toUnranked t := by simpa [he,optionUnranked] using hq
      exact hq'.symm
  · rintro ⟨S,t,ht,rfl⟩
    refine ⟨S,Finset.mem_univ _,?_⟩
    rw [actual_normalized_root_tree_at_evaluation N C S panel ht]
    simp [optionUnranked]

theorem actual_normalized_root_tree_splice (N : RootedBinary V E X) (C : Calendar N.graph)
    (hc : CutChild N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (S : N.Switching) (panel : Finset X) :
    actualNormalizedRootTree (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (restrictSwitching N hc b hb A S) panel = actualNormalizedRootTree N C S panel := by
  obtain ⟨a,ha⟩ := original_switching_pruning_exists N C S panel N.root
  obtain ⟨d,hd⟩ := original_switching_pruning_exists (splicedNetwork N hc b hb A)
    (splicedCalendar N hc b hb A C) (restrictSwitching N hc b hb A S) panel (splicedNetwork N hc b hb A).root
  rw [actual_normalized_root_tree_at_evaluation _ _ _ _ ha,actual_normalized_root_tree_at_evaluation _ _ _ _ hd]
  have hla := prunedAt_exact_leaves N S panel ha
  have hld := prunedAt_exact_leaves (splicedNetwork N hc b hb A) (restrictSwitching N hc b hb A S) panel hd
  rw [sampledDescendants_root] at hla hld
  cases a with
  | none =>
    cases d with
    | none => rfl
    | some d =>
      have he : d.leaves = ∅ := hld.trans hla.symm
      exact False.elim (Finset.not_nonempty_empty (he ▸ tree_leaves_nonempty d))
  | some a =>
    cases d with
    | none =>
      have he : a.leaves = ∅ := hla.trans hld.symm
      exact False.elim (Finset.not_nonempty_empty (he ▸ tree_leaves_nonempty a))
    | some d =>
      apply congrArg some
      apply actual_tree_clusters_determine_unranked d a
        (prunedAt_wellLabelled _ _ _ hd) (prunedAt_wellLabelled _ _ _ ha)
      rw [actual_pruned_root_clusters _ _ _ hd,actual_pruned_root_clusters _ _ _ ha]
      exact actual_selected_clusters_splice N hc b hb A S panel

/-- BOTH original switching directions preserve the WHOLE finite family of
actual normalized unranked trees, including all co-occurring clades. -/
theorem actual_displayed_rooted_tree_family_splice (N : RootedBinary V E X) (C : Calendar N.graph)
    (hc : CutChild N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (panel : Finset X) :
    actualDisplayedRootedTrees (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C) panel =
      actualDisplayedRootedTrees N C panel := by
  ext q
  simp only [actualDisplayedRootedTrees,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨T,hT⟩
    let S := liftSwitching N hc b hb A T
    refine ⟨S,?_⟩
    have hrow := actual_normalized_root_tree_splice N C hc b hb A S panel
    rw [actual_restrict_lift_switching] at hrow
    rw [←hrow]
    exact hT
  · rintro ⟨S,hS⟩
    refine ⟨restrictSwitching N hc b hb A S,?_⟩
    rw [actual_normalized_root_tree_splice]
    exact hS

#print axioms actual_pruning_unranked_unique
#print axioms actual_displayed_rooted_tree_family_splice
end G1ActualDisplayedTreeFamily
