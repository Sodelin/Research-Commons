import G1OriginalRecipePopulationOwnership

/-! Every original source population has exactly one constructed core-edge
owner. Distinct originated bridge labels cannot overlap in original population
IDs, even when their demographic age intervals overlap. -/
namespace G1ConstructedPopulationPartition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1LiftedOriginalBigon G1DecoratedSpliceConstruction G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1OriginalRecipePopulationOwnership
open G1BigonFootprint G1BigonSpliceGraph G1ActualTwoPortBlob
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def PopulationOwnership (O T : Source X) (D : Decoration O T) : Prop :=
  ∀ population : O.Edge, ∃! edge : T.Edge, population ∈ recipePopulations O (D.recipe edge)

lemma actual_initial_population_ownership (O : Source X) : PopulationOwnership O O (initialDecoration O) := by
  intro population
  refine ⟨population,Finset.mem_singleton_self _,?_⟩
  intro e he
  exact (Finset.mem_singleton.mp he).symm

lemma actual_splice_population_ownership (O T : Source X) (D : Decoration O T)
    (H : OriginalParentRegistry O.network) (b : T.network.graph.Blob)
    (hb : b ≠ T.network.graph.blobOf T.network.root) (A : ActualBlobBigon T.network b)
    (hown : PopulationOwnership O T D) :
    PopulationOwnership O (actualSplicedSource T b hb A) (spliceDecoration O T D H b hb A) := by
  intro population
  obtain ⟨owner,howner,hunique⟩ := hown population
  have hnew : population ∈ recipePopulations O
      ((spliceDecoration O T D H b hb A).recipe (.inr ())) ↔
      ∃ old ∈ removedEdges T.network b A, population ∈ recipePopulations O (D.recipe old) := by
    change population ∈ edgeRegion O (newOriginalSpan O T D H b A) ↔ _
    rw [actual_new_span_population_union,Finset.mem_biUnion]
  by_cases hrem : owner ∈ removedEdges T.network b A
  · refine ⟨.inr (),hnew.mpr ⟨owner,hrem,howner⟩,?_⟩
    intro e he
    cases e with
    | inl e =>
        have he' : population ∈ recipePopulations O (D.recipe e.val) := he
        have hsame := hunique e.val he'
        exact False.elim (e.property (hsame ▸ hrem))
    | inr z => cases z; rfl
  · let retained : RetainedEdge T.network b A := ⟨owner,hrem⟩
    refine ⟨.inl retained,howner,?_⟩
    intro e he
    cases e with
    | inl e => exact congrArg Sum.inl (Subtype.ext (hunique e.val he))
    | inr z =>
        cases z
        obtain ⟨old,hold,hpop⟩ := hnew.mp he
        exact False.elim (hrem ((hunique old hpop) ▸ hold))

/-- Literal physical Originated surgery derives the ownership partition; no
source-law equality or supplied independence condition is an admission field. -/
theorem actual_originated_population_ownership (O : Source X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) : PopulationOwnership O T D := by
  induction hD with
  | initial => exact actual_initial_population_ownership O
  | @splice T D prior b hb hp ih => exact actual_splice_population_ownership O T D H b hb _ ih

theorem actual_distinct_originated_recipes_disjoint (O : Source X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (e f : T.Edge) (hef : e ≠ f) :
    Disjoint (recipePopulations O (D.recipe e)) (recipePopulations O (D.recipe f)) := by
  apply Finset.disjoint_left.mpr
  intro population he hf
  obtain ⟨owner,_,hunique⟩ := actual_originated_population_ownership O H D hD population
  exact hef ((hunique e he).trans (hunique f hf).symm)

theorem actual_distinct_originated_bridge_regions_disjoint (O : Source X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (e f : T.Edge) (he : T.network.graph.IsBridge e)
    (hf : T.network.graph.IsBridge f) (hef : e ≠ f) :
    Disjoint (edgeRegion O (bridgeSpan O T D e he)) (edgeRegion O (bridgeSpan O T D f hf)) := by
  rw [actual_bridge_span_populations,actual_bridge_span_populations]
  exact actual_distinct_originated_recipes_disjoint O H D hD e f hef

#print axioms actual_originated_population_ownership
#print axioms actual_distinct_originated_bridge_regions_disjoint
end G1ConstructedPopulationPartition
