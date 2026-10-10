import SourceForestKingmanProjection

/-!
Source-population wrapper for the selected-label Kingman pair bijection.

Active operands are now computed from the actual state at one original edge or
the retained root population. Every candidate pair is proved LegalMerge in the
existing source semantics, and every projected nonempty-block pair has a unique
original legal preimage. Invisible representatives are not required to belong
to the selected label panel.

This proves the visible pair-rate ingredient on actual source-legal operands.
The silent-merger/pruned-genealogy generator equation and transition-semigroup
projectivity remain separate obligations.
-/

namespace GProgram.SourceForestKingmanPopulationProjection

open GProgram.SourceForest GProgram.SourceForestKingmanProjection

variable {V E Copy : Type*} [DecidableEq V] [DecidableEq E]
  [Fintype V] [Fintype E] [DecidableEq Copy] [Fintype Copy]

def populationRoots (s : State V E Copy) (place : Location V E) : Finset Copy :=
  s.live.filter (fun a => s.location a = place)

theorem populationRoots_subset_live (s : State V E Copy) (place : Location V E) :
    populationRoots s place ⊆ s.live := by
  intro a ha
  exact (Finset.mem_filter.mp ha).1

theorem population_pair_is_source_legal
    (s : State V E Copy) (place : Location V E)
    (hplace : ∀ v, place ≠ Location.node v)
    {a b : Copy} (hab : (a, b) ∈ (populationRoots s place).offDiag) :
    LegalMerge s a b := by
  rcases Finset.mem_offDiag.mp hab with ⟨ha, hb, hne⟩
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  refine ⟨ha'.1, hb'.1, hne, ha'.2.trans hb'.2.symm, ?_⟩
  intro v hv
  exact hplace v (ha'.2.symm.trans hv)

theorem visible_population_pair_is_source_legal
    (s : State V E Copy) (keep : Finset Copy) (place : Location V E)
    (hplace : ∀ v, place ≠ Location.node v)
    {a b : Copy}
    (hab : (a, b) ∈ (visibleActiveRoots s keep (populationRoots s place)).offDiag) :
    LegalMerge s a b := by
  rcases Finset.mem_offDiag.mp hab with ⟨ha, hb, hne⟩
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  exact population_pair_is_source_legal s place hplace
    (Finset.mem_offDiag.mpr ⟨ha'.1, hb'.1, hne⟩)

theorem projected_population_pair_has_unique_legal_preimage
    (s : State V E Copy) (hs : Valid s) (keep : Finset Copy)
    (place : Location V E) (hplace : ∀ v, place ≠ Location.node v)
    (p : Finset Copy × Finset Copy)
    (hp : p ∈ (selectedActiveBlocks s keep (populationRoots s place)).offDiag) :
    ∃! q : Copy × Copy,
      q ∈ (visibleActiveRoots s keep (populationRoots s place)).offDiag ∧
      pairMap (selectedBlock s keep) q = p ∧ LegalMerge s q.1 q.2 := by
  obtain ⟨q, hq, huniq⟩ := source_visible_pair_unique_preimage s hs keep
    (populationRoots s place) (populationRoots_subset_live s place) p hp
  have hlegal : LegalMerge s q.1 q.2 :=
    visible_population_pair_is_source_legal s keep place hplace hq.1
  refine ⟨q, ⟨hq.1, hq.2, hlegal⟩, ?_⟩
  intro r hr
  exact huniq r ⟨hr.1, hr.2.1⟩

theorem actual_population_visible_generator_identity
    (s : State V E Copy) (hs : Valid s) (keep : Finset Copy)
    (place : Location V E) (increment : Finset Copy × Finset Copy → ℝ) :
    visiblePairGenerator s keep (populationRoots s place) increment =
      projectedPairGenerator s keep (populationRoots s place) increment := by
  exact actual_source_visible_generator_identity s hs keep (populationRoots s place)
    (populationRoots_subset_live s place) increment

theorem edge_projected_pair_has_unique_legal_preimage
    (s : State V E Copy) (hs : Valid s) (keep : Finset Copy) (e : E)
    (p : Finset Copy × Finset Copy)
    (hp : p ∈ (selectedActiveBlocks s keep (populationRoots s (Location.edge e))).offDiag) :
    ∃! q : Copy × Copy,
      q ∈ (visibleActiveRoots s keep (populationRoots s (Location.edge e))).offDiag ∧
      pairMap (selectedBlock s keep) q = p ∧ LegalMerge s q.1 q.2 := by
  apply projected_population_pair_has_unique_legal_preimage s hs keep (Location.edge e)
    (fun v h => by cases h) p hp

theorem root_projected_pair_has_unique_legal_preimage
    (s : State V E Copy) (hs : Valid s) (keep : Finset Copy) (root : V)
    (p : Finset Copy × Finset Copy)
    (hp : p ∈ (selectedActiveBlocks s keep
      (populationRoots s (Location.rootPopulation root))).offDiag) :
    ∃! q : Copy × Copy,
      q ∈ (visibleActiveRoots s keep (populationRoots s (Location.rootPopulation root))).offDiag ∧
      pairMap (selectedBlock s keep) q = p ∧ LegalMerge s q.1 q.2 := by
  apply projected_population_pair_has_unique_legal_preimage s hs keep
    (Location.rootPopulation root) (fun v h => by cases h) p hp

end GProgram.SourceForestKingmanPopulationProjection

#print axioms GProgram.SourceForestKingmanPopulationProjection.edge_projected_pair_has_unique_legal_preimage
#print axioms GProgram.SourceForestKingmanPopulationProjection.root_projected_pair_has_unique_legal_preimage
#print axioms GProgram.SourceForestKingmanPopulationProjection.actual_population_visible_generator_identity
