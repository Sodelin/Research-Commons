import UnifiedLean.Source.SourceForestSilentPruning
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Actual source-population generator after full genealogy pruning

Contributor: dot, 2026-10-02. Reuses the inherited legal visible-pair bijection
and the actual silent-merger pruning link. A projected merger is defined from
the selected genealogies themselves; no generator identity is a contract field.
This is the infinitesimal source link. A continuous-time transition semigroup,
calendar scheduler/pulse transport and entire full-source law still require
construction and integration before a whole-source projectivity theorem.
-/
namespace UnifiedLean.Source.SourceForestGeneratorIntertwining
open GProgram.SourceForest GProgram.SourceForestKingmanProjection
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.SourceForestSilentPruning
open scoped BigOperators Classical
variable {V E Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

/-- Read one whole selected genealogy using any selected label in its block.
Valid original source states prove this independent of the label choice. -/
noncomputable def viewBlockTree (v : SelectedView V E Copy) (A : Finset Copy) :
    Option (Genealogy Copy) :=
  if h : A.Nonempty then v.genealogy (Classical.choose h) else none

noncomputable def projectedMerge (v : SelectedView V E Copy) (A B : Finset Copy) :
    SelectedView V E Copy where
  genealogy x := if x ∈ A ∪ B then
    Genealogy.joinPruned (viewBlockTree v A) (viewBlockTree v B) else v.genealogy x
  population := v.population
  register := v.register

lemma selectedGenealogy_at_block (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a x : Copy} (ha : a ∈ s.live)
    (hx : x ∈ selectedBlock s keep a) :
    (selectedView s keep).genealogy x = (s.genealogy a).prune keep := by
  obtain ⟨hxkeep,hxa⟩ := (selectedBlock_eq_fiber s hs keep ha x).mp hx
  simp only [selectedView,selectedGenealogy,if_pos hxkeep,hxa]

lemma viewBlockTree_source (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a : Copy} (ha : a ∈ s.live)
    (hA : (selectedBlock s keep a).Nonempty) :
    viewBlockTree (selectedView s keep) (selectedBlock s keep a) =
      (s.genealogy a).prune keep := by
  rw [viewBlockTree,dif_pos hA]
  exact selectedGenealogy_at_block s hs keep ha (Classical.choose_spec hA)

/-- A visible original legal merger induces exactly the genealogy graft on
its two selected blocks, regardless of the original representative IDs. -/
theorem selectedView_merge_visible (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a b : Copy} (hm : LegalMerge s a b)
    (hA : (selectedBlock s keep a).Nonempty)
    (hB : (selectedBlock s keep b).Nonempty) :
    selectedView (merge s a b) keep =
      projectedMerge (selectedView s keep) (selectedBlock s keep a) (selectedBlock s keep b) := by
  apply SelectedView.ext
  · funext x
    change selectedGenealogy (merge s a b) keep x =
      if x ∈ selectedBlock s keep a ∪ selectedBlock s keep b then
        Genealogy.joinPruned (viewBlockTree (selectedView s keep) (selectedBlock s keep a))
          (viewBlockTree (selectedView s keep) (selectedBlock s keep b))
      else selectedGenealogy s keep x
    rw [viewBlockTree_source s hs keep hm.first_live hA,
      viewBlockTree_source s hs keep hm.second_live hB]
    by_cases hx : x ∈ keep
    · have hxA : x ∈ selectedBlock s keep a ↔ s.ancestor x = a := by
        rw [selectedBlock_eq_fiber s hs keep hm.first_live x]
        simp only [hx,true_and]
      have hxB : x ∈ selectedBlock s keep b ↔ s.ancestor x = b := by
        rw [selectedBlock_eq_fiber s hs keep hm.second_live x]
        simp only [hx,true_and]
      simp only [selectedGenealogy,if_pos hx,Finset.mem_union,hxA,hxB]
      by_cases hb : s.ancestor x = b
      · simp [merge,hb,Genealogy.prune]
      · by_cases ha : s.ancestor x = a
        · simp [merge,hb,ha,Genealogy.prune]
        · simp [merge,hb,ha]
    · have hxA : x ∉ selectedBlock s keep a := by
        intro h
        exact hx ((Finset.mem_inter.mp h).2)
      have hxB : x ∉ selectedBlock s keep b := by
        intro h
        exact hx ((Finset.mem_inter.mp h).2)
      simp [selectedGenealogy,hx,hxA,hxB]
  · exact selectedLocation_merge_unchanged s keep hm
  · rfl

noncomputable def sourceIncrement (s : State V E Copy) (keep : Finset Copy)
    (f : SelectedView V E Copy → ℝ) (p : Copy × Copy) : ℝ :=
  f (selectedView (merge s p.1 p.2) keep) - f (selectedView s keep)

noncomputable def projectedIncrement (s : State V E Copy) (keep : Finset Copy)
    (f : SelectedView V E Copy → ℝ) (p : Finset Copy × Finset Copy) : ℝ :=
  f (projectedMerge (selectedView s keep) p.1 p.2) - f (selectedView s keep)

noncomputable def originalPopulationGenerator (s : State V E Copy)
    (keep : Finset Copy) (place : Location V E) (rate : ℝ)
    (f : SelectedView V E Copy → ℝ) : ℝ :=
  (rate/2) * ∑ p ∈ (populationRoots s place).offDiag, sourceIncrement s keep f p

noncomputable def selectedPopulationGenerator (s : State V E Copy)
    (keep : Finset Copy) (place : Location V E) (rate : ℝ)
    (f : SelectedView V E Copy → ℝ) : ℝ :=
  (rate/2) * ∑ p ∈ (selectedActiveBlocks s keep (populationRoots s place)).offDiag,
    projectedIncrement s keep f p

lemma visible_offDiag_subset (s : State V E Copy) (keep active : Finset Copy) :
    (visibleActiveRoots s keep active).offDiag ⊆ active.offDiag := by
  intro p hp
  rcases Finset.mem_offDiag.mp hp with ⟨ha,hb,hne⟩
  exact Finset.mem_offDiag.mpr
    ⟨(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp hb).1,hne⟩

/-- All source-legal population pairs participate. Invisible pairs cancel
because actual pruning makes their whole forest/population/register increment
zero; visible pairs then use the inherited unique legal pair preimage. -/
theorem actual_population_generator_intertwining (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (place : Location V E) (hplace : ∀ v, place ≠ Location.node v)
    (rate : ℝ) (f : SelectedView V E Copy → ℝ) :
    originalPopulationGenerator s keep place rate f =
      selectedPopulationGenerator s keep place rate f := by
  unfold originalPopulationGenerator selectedPopulationGenerator
  congr 1
  have hrestrict :
      (∑ p ∈ (populationRoots s place).offDiag, sourceIncrement s keep f p) =
        ∑ p ∈ (visibleActiveRoots s keep (populationRoots s place)).offDiag,
          sourceIncrement s keep f p := by
    symm
    apply Finset.sum_subset (visible_offDiag_subset s keep (populationRoots s place))
    intro p hp hv
    have hm := population_pair_is_source_legal s place hplace hp
    have hi : ¬(selectedBlock s keep p.1).Nonempty ∨
        ¬(selectedBlock s keep p.2).Nonempty := by
      by_contra hn
      push Not at hn
      apply hv
      obtain ⟨ha,hb,hne⟩ := Finset.mem_offDiag.mp hp
      exact Finset.mem_offDiag.mpr
        ⟨Finset.mem_filter.mpr ⟨ha,hn.1⟩,Finset.mem_filter.mpr ⟨hb,hn.2⟩,hne⟩
    exact silent_merger_readout_increment_zero s hs keep hm hi f
  rw [hrestrict]
  trans ∑ p ∈ (visibleActiveRoots s keep (populationRoots s place)).offDiag,
    projectedIncrement s keep f (pairMap (selectedBlock s keep) p)
  · apply Finset.sum_congr rfl
    intro p hp
    have hm := visible_population_pair_is_source_legal s keep place hplace hp
    obtain ⟨ha,hb,_⟩ := Finset.mem_offDiag.mp hp
    unfold sourceIncrement projectedIncrement pairMap
    rw [selectedView_merge_visible s hs keep hm
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2]
  · exact projected_pair_sum _ _
      (selectedBlock_injective_on_visibleActive s hs keep (populationRoots s place)
        (populationRoots_subset_live s place)) (projectedIncrement s keep f)

#print axioms viewBlockTree_source
#print axioms selectedView_merge_visible
#print axioms actual_population_generator_intertwining
end UnifiedLean.Source.SourceForestGeneratorIntertwining
