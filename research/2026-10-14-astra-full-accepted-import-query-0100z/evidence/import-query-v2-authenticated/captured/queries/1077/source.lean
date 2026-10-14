import G5FairSharpnessSources

/-!
# The concrete admitted sources have different documented normalized Q
Contributor: dot / OpenAI, 2026-10-03.
Constructs actual retained ORIGINAL edge witnesses in every switching. The
inherited original-bridge incompatibility theorem excludes the crossed
resolution. Actual pruning/unary/binary-root compatibility transports this
strict target difference to the exact upper-bound theorem's target.
-/
namespace GProgram.G5.Sharpness
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization
open Nanuq.Quartet
open scoped Classical

def quartet : Fin 4 ↪ Taxon := Function.Embedding.refl _

lemma every_switching_tree_quartet (N : RootedBinary Vertex Edge Taxon)
    (hg : N.graph = treeGraph) (S : N.Switching) : S.graph.HasQuartet 3 4 5 6 := by
  have hk : ∀ e, S.keep e := by
    intro e
    apply S.ordinary
    rw [hg]
    exact no_hybrid _
  let edge : Edge → S.Edge := fun e => ⟨e,hk e⟩
  have hs (e : Edge) : S.graph.source (edge e) = treeGraph.source e := by
    change N.graph.source e = _
    rw [hg]
  have ht (e : Edge) : S.graph.target (edge e) = treeGraph.target e := by
    change N.graph.target e = _
    rw [hg]
  have step (e f : Edge) (hne : e ≠ f) :
      S.graph.UStep (fun g => g ≠ edge f) (treeGraph.source e) (treeGraph.target e) := by
    refine ⟨edge e,?_,Or.inl ⟨hs e,ht e⟩⟩
    intro h
    exact hne (congrArg Subtype.val h)
  refine ⟨edge 0,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic _,Or.inr ?_⟩
  simp only [EdgeGraph.OrientedQuartet,hs,ht]
  change S.graph.ReachWithout (edge 0) 0 5 ∧ S.graph.ReachWithout (edge 0) 0 6 ∧
    S.graph.ReachWithout (edge 0) 1 3 ∧ S.graph.ReachWithout (edge 0) 1 4
  exact ⟨(S.graph.ureach_single (step 1 0 (by decide))).trans
      (S.graph.ureach_single (step 4 0 (by decide))),
    (S.graph.ureach_single (step 1 0 (by decide))).trans
      (S.graph.ureach_single (step 5 0 (by decide))),
    S.graph.ureach_single (step 2 0 (by decide)),
    S.graph.ureach_single (step 3 0 (by decide))⟩

lemma sourceA_first_raw : Resolution.xy_zw ∈ sourceA.rawDisplayedQuartets quartet := by
  rw [actual_raw_mem_iff_selected_resolves]
  exact ⟨sourceA.defaultSwitching,every_switching_tree_quartet sourceA rfl _⟩

lemma sourceB_not_first_raw : Resolution.xy_zw ∉ sourceB.rawDisplayedQuartets quartet := by
  intro h
  rw [actual_raw_mem_iff_selected_resolves] at h
  obtain ⟨S,hS⟩ := h
  have hcorrect := every_switching_tree_quartet sourceB rfl S
  exact S.graph.hasQuartet_incompatible hcorrect hS

/-- Difference in the actual edge-indexed original switching quartet union. -/
theorem actual_raw_quartet_targets_differ :
    sourceA.rawDisplayedQuartets quartet ≠ sourceB.rawDisplayedQuartets quartet := by
  intro h
  exact sourceB_not_first_raw (h ▸ sourceA_first_raw)

/-- Difference in the IDENTICAL documented normalized target used by the
full fair-M2 upper endpoint, after actual taxon/dead-twig/unary/root reduction. -/
theorem documented_normalized_quartet_targets_differ :
    normalizedDisplayedCutQuartets sourceA quartet ≠ normalizedDisplayedCutQuartets sourceB quartet := by
  rw [←raw_displayed_equals_normalized_cut_quartets sourceA treeCalendar quartet,
    ←raw_displayed_equals_normalized_cut_quartets sourceB treeCalendar quartet]
  exact actual_raw_quartet_targets_differ

#print axioms every_switching_tree_quartet
#print axioms actual_raw_quartet_targets_differ
#print axioms documented_normalized_quartet_targets_differ
end GProgram.G5.Sharpness
