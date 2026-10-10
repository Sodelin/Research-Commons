import UnifiedLean.Source.SourceForestGeneratorIntertwining

/-!
# Intrinsic selected-view generator for the full original population catalogue

Contributor: dot, 2026-10-02. Selected active blocks are reconstructed from
selected genealogies and their original population IDs, rather than looked up
through hidden original representative IDs. The derived generator is therefore
an intrinsic function of the pruned view. This fills the actual generator
factor-through gate for arbitrary finite copy panels; full finite-time kernels,
calendar/pulse scheduling and stochastic source projectivity remain separate.
-/
namespace UnifiedLean.Source.SourceForestIntrinsicGenerator
open Nanuq.Source GProgram.SourceForest GProgram.SourceForestKingmanProjection
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestGeneratorIntertwining
open scoped BigOperators Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

/-- Reads the selected CURRENT block from the INTERNAL pruned genealogy of
any retained original label, retaining its ORIGINAL population ID. -/
noncomputable def viewPopulationBlocks (v : SelectedView V E Copy)
    (keep : Finset Copy) (place : Location V E) : Finset (Finset Copy) :=
  (keep.filter (fun x => v.population x = some place)).image
    (fun x => Genealogy.optionLeaves (v.genealogy x))

lemma selected_view_block_leaves (s : State V E Copy) (keep : Finset Copy)
    {x : Copy} (hx : x ∈ keep) :
    Genealogy.optionLeaves ((selectedView s keep).genealogy x) =
      selectedBlock s keep (s.ancestor x) := by
  simp only [selectedView,selectedGenealogy,if_pos hx,Genealogy.prune_leaves,selectedBlock]

/-- The old full-state catalogue is exactly reconstructible from the selected
view. Hidden original representatives do not enter the projected generator. -/
theorem selected_active_blocks_eq_intrinsic (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (place : Location V E) :
    selectedActiveBlocks s keep (populationRoots s place) =
      viewPopulationBlocks (selectedView s keep) keep place := by
  ext A
  unfold selectedActiveBlocks viewPopulationBlocks
  constructor
  · intro h
    obtain ⟨l,hl,hA⟩ := Finset.mem_image.mp h
    obtain ⟨hpop,hvis⟩ := Finset.mem_filter.mp hl
    obtain ⟨hlive,hlplace⟩ := Finset.mem_filter.mp hpop
    obtain ⟨x,hx⟩ := hvis
    obtain ⟨hxkeep,hxa⟩ := (selectedBlock_eq_fiber s hs keep hlive x).mp hx
    apply Finset.mem_image.mpr
    refine ⟨x,Finset.mem_filter.mpr ⟨hxkeep,?_⟩,?_⟩
    · simp only [selectedView,selectedLocation,if_pos hxkeep,copyLocation,hxa,hlplace]
    · rw [selected_view_block_leaves s keep hxkeep,hxa]
      exact hA
  · intro h
    obtain ⟨x,hx,hA⟩ := Finset.mem_image.mp h
    obtain ⟨hxkeep,hxpop⟩ := Finset.mem_filter.mp hx
    have hlive : s.ancestor x ∈ s.live := hs.ancestor_live x
    have hlplace : s.location (s.ancestor x) = place := by
      exact Option.some.inj (by simpa only
        [selectedView,selectedLocation,if_pos hxkeep,copyLocation] using hxpop)
    have hvis : (selectedBlock s keep (s.ancestor x)).Nonempty :=
      ⟨x,(selectedBlock_eq_fiber s hs keep hlive x).mpr ⟨hxkeep,rfl⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨s.ancestor x,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hlive,hlplace⟩,hvis⟩,?_⟩
    rw [selected_view_block_leaves s keep hxkeep] at hA
    exact hA

noncomputable def viewPopulationGenerator (v : SelectedView V E Copy)
    (keep : Finset Copy) (place : Location V E) (rate : ℝ)
    (f : SelectedView V E Copy → ℝ) : ℝ :=
  (rate/2) * ∑ p ∈ (viewPopulationBlocks v keep place).offDiag,
    (f (projectedMerge v p.1 p.2) - f v)

/-- Infinitesimal factor-through in the actual source state and its intrinsic
selected pruned view, for every forest/population/register readout. -/
theorem original_population_generator_factors_through_view (s : State V E Copy)
    (hs : Valid s) (keep : Finset Copy) (place : Location V E)
    (hplace : ∀ v, place ≠ Location.node v) (rate : ℝ)
    (f : SelectedView V E Copy → ℝ) :
    originalPopulationGenerator s keep place rate f =
      viewPopulationGenerator (selectedView s keep) keep place rate f := by
  rw [actual_population_generator_intertwining s hs keep place hplace rate f]
  unfold selectedPopulationGenerator viewPopulationGenerator projectedIncrement
  rw [selected_active_blocks_eq_intrinsic s hs keep place]

/-- ORIGINAL edge occurrences plus the retained ORIGINAL ancestral population.
No physical source is contracted, and rates remain one assignment per source. -/
noncomputable def nativeSourceGenerator (root : V) (s : State V E Copy)
    (keep : Finset Copy) (edgeRate : E → ℝ) (ancestralRate : ℝ)
    (f : SelectedView V E Copy → ℝ) : ℝ :=
  (∑ e : E, originalPopulationGenerator s keep (.edge e) (edgeRate e) f) +
    originalPopulationGenerator s keep (.rootPopulation root) ancestralRate f

noncomputable def intrinsicSourceGenerator (root : V) (v : SelectedView V E Copy)
    (keep : Finset Copy) (edgeRate : E → ℝ) (ancestralRate : ℝ)
    (f : SelectedView V E Copy → ℝ) : ℝ :=
  (∑ e : E, viewPopulationGenerator v keep (.edge e) (edgeRate e) f) +
    viewPopulationGenerator v keep (.rootPopulation root) ancestralRate f

/-- All original source populations simultaneously. Multiple original copies,
including invisible live representatives, are supported by the actual state. -/
theorem native_source_generator_intertwining (root : V) (s : State V E Copy)
    (hs : Valid s) (keep : Finset Copy) (edgeRate : E → ℝ) (ancestralRate : ℝ)
    (f : SelectedView V E Copy → ℝ) :
    nativeSourceGenerator root s keep edgeRate ancestralRate f =
      intrinsicSourceGenerator root (selectedView s keep) keep edgeRate ancestralRate f := by
  unfold nativeSourceGenerator intrinsicSourceGenerator
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    exact original_population_generator_factors_through_view s hs keep (.edge e)
      (fun v h => by cases h) _ f
  · exact original_population_generator_factors_through_view s hs keep (.rootPopulation root)
      (fun v h => by cases h) _ f

/-- Explicit native-source wrapper uses the inherited original graph and
copy-to-original-tip sample assignment. It assumes only its genuine proved
source-state invariant, not a generator/kernel equation. -/
theorem original_source_valid_generator_intertwining [Fintype X]
    (N : RootedBinary V E X) (sample : Copy → X) (s : State V E Copy)
    (hs : SourceValid N sample s) (keep : Finset Copy)
    (edgeRate : E → ℝ) (ancestralRate : ℝ) (f : SelectedView V E Copy → ℝ) :
    nativeSourceGenerator N.root s keep edgeRate ancestralRate f =
      intrinsicSourceGenerator N.root (selectedView s keep) keep edgeRate ancestralRate f :=
  native_source_generator_intertwining N.root s hs.forest keep edgeRate ancestralRate f

#print axioms selected_active_blocks_eq_intrinsic
#print axioms original_population_generator_factors_through_view
#print axioms native_source_generator_intertwining
#print axioms original_source_valid_generator_intertwining
end UnifiedLean.Source.SourceForestIntrinsicGenerator
