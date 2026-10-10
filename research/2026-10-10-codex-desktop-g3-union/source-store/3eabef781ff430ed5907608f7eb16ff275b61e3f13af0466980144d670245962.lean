import G1NonrootBigonKernel
import UnifiedLean.Source.SourceCrossCarrierEpoch

/-!
# Actual source mergers in disjoint original population panels

Contributor: dot, 2026-10-03. Population separation is a physical input
condition on original copy locations. The conclusions below are derived from
the actual legal current-owner pairs and the inherited whole genealogy view.
No independence, desired generator identity or desired output law is assumed.
-/
namespace G1JointSeparatedSourceGeometry
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceStepGeneratorBinding
open G1NonrootBigonKernel
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The two original-label panels occupy disjoint ORIGINAL populations. -/
def PopulationSeparated (s : State V E Copy) (inside outside : Finset Copy) : Prop :=
  ∀ x ∈ inside, ∀ y ∈ outside, copyLocation s x ≠ copyLocation s y

lemma visible_copy_population (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a : Copy} (ha : a ∈ s.live)
    {x : Copy} (hx : x ∈ selectedBlock s keep a) :
    x ∈ keep ∧ copyLocation s x = s.location a := by
  obtain ⟨hleaf,hkeep⟩ := Finset.mem_inter.mp hx
  exact ⟨hkeep, congrArg s.location ((hs.leaf_fiber a ha x).mp hleaf)⟩

/-- A legal source pair cannot have an inside-visible and an outside-visible
operand: its actual two owners occupy the same original population. -/
theorem separated_legal_pair_not_both_visible (s : State V E Copy) (hs : Valid s)
    (inside outside : Finset Copy) (hsep : PopulationSeparated s inside outside)
    {a b : Copy} (hm : LegalMerge s a b)
    (hin : (selectedBlock s inside a).Nonempty) :
    ¬ (selectedBlock s outside b).Nonempty := by
  rintro ⟨y,hy⟩
  obtain ⟨x,hx⟩ := hin
  obtain ⟨hxi,hxl⟩ := visible_copy_population s hs inside hm.first_live hx
  obtain ⟨hyo,hyl⟩ := visible_copy_population s hs outside hm.second_live hy
  exact hsep x hxi y hyo (hxl.trans (hm.same_population.trans hyl.symm))

/-- Each actual current-owner merger leaves at least one ENTIRE pruned
forest/population/register panel unchanged, not merely a scalar readout. -/
theorem actual_merge_changes_at_most_one_panel (s : State V E Copy) (hs : Valid s)
    (inside outside : Finset Copy) (hsep : PopulationSeparated s inside outside)
    {a b : Copy} (hm : LegalMerge s a b) :
    selectedView (merge s a b) inside = selectedView s inside ∨
      selectedView (merge s a b) outside = selectedView s outside := by
  by_cases hin : (selectedBlock s inside a).Nonempty
  · right
    apply selectedView_merge_silent s hs outside hm
    exact Or.inr (separated_legal_pair_not_both_visible s hs inside outside hsep hm hin)
  · left
    exact selectedView_merge_silent s hs inside hm (Or.inl hin)

theorem actual_choice_changes_at_most_one_panel (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (inside outside : Finset Copy)
    (hsep : PopulationSeparated (state s) inside outside) (p : Choice N s) :
    selectedView (state (stepDestination N s (some p))) inside = selectedView (state s) inside ∨
      selectedView (state (stepDestination N s (some p))) outside = selectedView (state s) outside := by
  rw [merged_destination_selectedView,merged_destination_selectedView]
  exact actual_merge_changes_at_most_one_panel _ s.property.forest inside outside hsep
    (population_pair_is_source_legal _ _ (originalPlace_not_node N p.1) p.2.property)

/-- The physical separator is preserved by each ACTUAL merger, so it is
available at every later state of the continuous original population epoch. -/
theorem actual_step_separation_iff (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (inside outside : Finset Copy) (p : Option (Choice N s)) :
    PopulationSeparated (state (stepDestination N s p)) inside outside ↔
      PopulationSeparated (state s) inside outside := by
  unfold PopulationSeparated
  simp only [actual_step_copy_population]

#print axioms actual_merge_changes_at_most_one_panel
#print axioms actual_choice_changes_at_most_one_panel
#print axioms actual_step_separation_iff
end G1JointSeparatedSourceGeometry
