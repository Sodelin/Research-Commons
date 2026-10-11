import UnifiedLean.Source.SourceCopyCarrierTransport

/-!
# Actual independently initialized small-copy source generator binding

Contributor: dot, 2026-10-02. Reconstructs genuine small-carrier current roots
and their original populations as ORIGINAL-label blocks, then derives the
same intrinsic selected genealogy generator as the full source. All current
pair rates and merged destinations are actual; no cross-carrier generator
identity or posterior/source fitting is supplied as a premise.
-/
namespace UnifiedLean.Source.SourceSmallCarrierGenerator
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.SourceForestKingmanProjection
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestGeneratorIntertwining
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.SourceCopyCarrierTransport
open scoped Classical BigOperators
variable {V E Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def liftedBlock (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (a : SelectedCopy keep) : Finset Copy :=
  (s.genealogy a).leaves.image (fun x : SelectedCopy keep => x.val)

lemma selected_label_in_liftedBlock (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) {a : SelectedCopy keep} (ha : a ∈ s.live) (x : SelectedCopy keep) :
    x.val ∈ liftedBlock keep s a ↔ s.ancestor x = a := by
  unfold liftedBlock
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    have hxy : y = x := Subtype.ext he
    subst y
    exact (hs.leaf_fiber a ha x).mp hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x,(hs.leaf_fiber a ha x).mpr hx,rfl⟩

lemma liftedBlock_nonempty (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) {a : SelectedCopy keep} (ha : a ∈ s.live) : (liftedBlock keep s a).Nonempty :=
  ⟨a.val,(selected_label_in_liftedBlock keep s hs ha a).mpr (hs.representative a ha)⟩

lemma liftedBlock_injective_live (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) {a b : SelectedCopy keep} (ha : a ∈ s.live) (hb : b ∈ s.live)
    (he : liftedBlock keep s a = liftedBlock keep s b) : a = b := by
  have ham := (selected_label_in_liftedBlock keep s hs ha a).mpr (hs.representative a ha)
  rw [he] at ham
  exact (hs.representative a ha).symm.trans ((selected_label_in_liftedBlock keep s hs hb a).mp ham)

/-- Every actual small-source current population block is read as exactly its
original-label clade. Hidden representative IDs do not occur in the view. -/
theorem small_population_catalogue (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) (place : Location V E) :
    viewPopulationBlocks (liftView keep (selectedView s Finset.univ)) keep place =
      (populationRoots s place).image (liftedBlock keep s) := by
  ext A
  unfold viewPopulationBlocks
  constructor
  · intro h
    obtain ⟨x,hx,hA⟩ := Finset.mem_image.mp h
    obtain ⟨hx,hpop⟩ := Finset.mem_filter.mp hx
    let y : SelectedCopy keep := ⟨x,hx⟩
    have hloc : copyLocation s y = place := by
      have hh := lifted_original_population keep s y
      rw [hh] at hpop
      exact Option.some.inj hpop
    apply Finset.mem_image.mpr
    refine ⟨s.ancestor y,Finset.mem_filter.mpr ⟨hs.ancestor_live y,hloc⟩,?_⟩
    have hg := lifted_original_genealogy keep s y
    rw [hg] at hA
    simpa only [Genealogy.optionLeaves,mapLabels_leaves,liftedBlock] using hA
  · intro h
    obtain ⟨a,ha,hA⟩ := Finset.mem_image.mp h
    obtain ⟨hal,hpop⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_image.mpr
    refine ⟨a.val,Finset.mem_filter.mpr ⟨a.property,?_⟩,?_⟩
    · rw [lifted_original_population]
      change some (s.location (s.ancestor a)) = some place
      rw [hs.representative a hal,hpop]
    · rw [lifted_original_genealogy]
      change (mapLabels Subtype.val (s.genealogy (s.ancestor a))).leaves = A
      rw [hs.representative a hal,mapLabels_leaves]
      exact hA

lemma lifted_block_tree (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) {a : SelectedCopy keep} (ha : a ∈ s.live) :
    viewBlockTree (liftView keep (selectedView s Finset.univ)) (liftedBlock keep s a) =
      some (mapLabels Subtype.val (s.genealogy a)) := by
  have hn := liftedBlock_nonempty keep s hs ha
  rw [viewBlockTree,dif_pos hn]
  obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp (Classical.choose_spec hn)
  rw [←heq,lifted_original_genealogy,(hs.leaf_fiber a ha y).mp hy]

/-- Actual small-source mergers induce precisely the SAME original-labelled
selected graft, with no choice of a full-source representative ID. -/
theorem small_merger_original_view (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) {a b : SelectedCopy keep} (hm : LegalMerge s a b) :
    liftView keep (selectedView (merge s a b) Finset.univ) =
      projectedMerge (liftView keep (selectedView s Finset.univ))
        (liftedBlock keep s a) (liftedBlock keep s b) := by
  apply SelectedView.ext
  · funext x
    by_cases hx : x ∈ keep
    · let y : SelectedCopy keep := ⟨x,hx⟩
      have ha : y.val ∈ liftedBlock keep s a ↔ s.ancestor y = a :=
        selected_label_in_liftedBlock keep s hs hm.first_live y
      have hb : y.val ∈ liftedBlock keep s b ↔ s.ancestor y = b :=
        selected_label_in_liftedBlock keep s hs hm.second_live y
      change (liftView keep (selectedView (merge s a b) Finset.univ)).genealogy y.val =
        if y.val ∈ liftedBlock keep s a ∪ liftedBlock keep s b then _
          else (liftView keep (selectedView s Finset.univ)).genealogy y.val
      rw [lifted_original_genealogy,lifted_block_tree keep s hs hm.first_live,
        lifted_block_tree keep s hs hm.second_live,lifted_original_genealogy]
      simp only [Finset.mem_union,ha,hb,Genealogy.joinPruned]
      by_cases hab : s.ancestor y = b
      · simp [merge,hab,mapLabels]
      · by_cases haa : s.ancestor y = a
        · simp [merge,hab,haa,mapLabels]
        · simp [merge,hab,haa]
    · have ha : x ∉ liftedBlock keep s a := by
        rintro h; obtain ⟨y,_,hy⟩ := Finset.mem_image.mp h
        exact hx (hy ▸ y.property)
      have hb : x ∉ liftedBlock keep s b := by
        rintro h; obtain ⟨y,_,hy⟩ := Finset.mem_image.mp h
        exact hx (hy ▸ y.property)
      simp [liftView,projectedMerge,hx,ha,hb]
  · funext x
    by_cases hx : x ∈ keep
    · let y : SelectedCopy keep := ⟨x,hx⟩
      change (liftView keep (selectedView (merge s a b) Finset.univ)).population y.val =
        (liftView keep (selectedView s Finset.univ)).population y.val
      rw [lifted_original_population,lifted_original_population,merge_population_preserved s hm y]
    · simp [liftView,projectedMerge,hx]
  · rfl

/-- The actual independently initialized small-carrier population generator,
viewed on original copy labels, is the intrinsic full selected generator. -/
theorem small_original_population_generator (keep : Finset Copy)
    (s : State V E (SelectedCopy keep)) (hs : Valid s) (place : Location V E)
    (hplace : ∀ v, place ≠ Location.node v) (rate : ℝ)
    (f : SelectedView V E Copy → ℝ) :
    originalPopulationGenerator s Finset.univ place rate (fun v => f (liftView keep v)) =
      viewPopulationGenerator (liftView keep (selectedView s Finset.univ)) keep place rate f := by
  unfold originalPopulationGenerator viewPopulationGenerator sourceIncrement
  rw [small_population_catalogue keep s hs place]
  congr 1
  trans ∑ p ∈ (populationRoots s place).offDiag,
    (f (projectedMerge (liftView keep (selectedView s Finset.univ))
      (liftedBlock keep s p.1) (liftedBlock keep s p.2)) -
      f (liftView keep (selectedView s Finset.univ)))
  · apply Finset.sum_congr rfl
    intro p hp
    dsimp only
    rw [small_merger_original_view keep s hs (population_pair_is_source_legal s place hplace hp)]
  · simpa only [pairMap] using projected_pair_sum _ _
      (fun a ha b hb he => liftedBlock_injective_live keep s hs
        (populationRoots_subset_live s place ha) (populationRoots_subset_live s place hb) he)
      (fun p : Finset Copy × Finset Copy =>
        f (projectedMerge (liftView keep (selectedView s Finset.univ)) p.1 p.2) -
          f (liftView keep (selectedView s Finset.univ)))

/-- All ORIGINAL graph edges and the ORIGINAL ancestral population, at their
SAME supplied rates: the cross-copy-carrier generator binding is DERIVED. -/
theorem small_original_source_generator (root : V) (keep : Finset Copy)
    (s : State V E (SelectedCopy keep)) (hs : Valid s)
    (edgeRate : E → ℝ) (ancestralRate : ℝ) (f : SelectedView V E Copy → ℝ) :
    nativeSourceGenerator root s Finset.univ edgeRate ancestralRate (fun v => f (liftView keep v)) =
      intrinsicSourceGenerator root (liftView keep (selectedView s Finset.univ))
        keep edgeRate ancestralRate f := by
  unfold nativeSourceGenerator intrinsicSourceGenerator
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    exact small_original_population_generator keep s hs (.edge e) (fun v h => by cases h) _ f
  · exact small_original_population_generator keep s hs (.rootPopulation root) (fun v h => by cases h) _ f

#print axioms small_population_catalogue
#print axioms small_merger_original_view
#print axioms small_original_population_generator
#print axioms small_original_source_generator
end UnifiedLean.Source.SourceSmallCarrierGenerator
