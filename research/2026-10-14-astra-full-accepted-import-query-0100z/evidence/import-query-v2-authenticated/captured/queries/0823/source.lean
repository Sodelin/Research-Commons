import G1CanonicalOriginatedCompletedHistory

/-! Literal original population ownership of source-derived core edge recipes.
This is physical provenance for concurrent scheduling, independent of age
interval overlap. Contributor: dot, 2026-10-03. -/
namespace G1OriginalRecipePopulationOwnership
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G2
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1LiftedOriginalBigon G1DecoratedSpliceConstruction G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1OriginatedSpanRegistryAdmission G1OriginatedNeutralSpanRegion
open G1BigonFootprint G1BigonSpliceGraph G1ActualTwoPortBlob
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def recipePopulations (O : Source X) : Recipe O → Finset O.Edge
  | .raw e => {e}
  | .span _ _ word => edgeRegion O word

lemma actual_recipe_span_populations (O : Source X) {a b : O.Vertex} (label : Recipe O)
    (ep : label.input = a ∧ label.output = b)
    (rawBridge : ∀ f, label = .raw f → O.network.graph.IsBridge f) :
    edgeRegion O (physicalRecipeSpan O label ep rawBridge) = recipePopulations O label := by
  cases label with
  | raw f =>
      simp only [Recipe.input,Recipe.output] at ep
      obtain ⟨rfl,rfl⟩ := ep
      simp [physicalRecipeSpan,recipePopulations,edgeRegion]
  | span c d word =>
      simp only [Recipe.input,Recipe.output] at ep
      obtain ⟨rfl,rfl⟩ := ep
      simp [physicalRecipeSpan,recipePopulations]

lemma actual_bridge_span_populations (O T : Source X) (D : Decoration O T)
    (e : T.Edge) (he : T.network.graph.IsBridge e) :
    edgeRegion O (bridgeSpan O T D e he) = recipePopulations O (D.recipe e) := by
  change edgeRegion O (physicalRecipeSpan O (D.recipe e) (D.endpoints e)
    (fun f hf => (D.raw_bridge e f hf).mp he)) = _
  exact actual_recipe_span_populations O _ _ _

lemma edge_region_mpr_left (O : Source X) {a a' b : O.Vertex}
    (h : a = a') (word : OriginalSpan O.network a' b) :
    edgeRegion O ((congrArg (fun v => OriginalSpan O.network v b) h).mpr word) = edgeRegion O word := by
  subst a'
  rfl

lemma edge_region_mpr_right (O : Source X) {a b b' : O.Vertex}
    (h : b = b') (word : OriginalSpan O.network a b') :
    edgeRegion O ((congrArg (OriginalSpan O.network a) h).mpr word) = edgeRegion O word := by
  subst b'
  rfl

lemma edge_region_cast_left (O : Source X) {a a' b : O.Vertex}
    (h : a = a') (word : OriginalSpan O.network a b) :
    edgeRegion O (cast (congrArg (fun v => OriginalSpan O.network v b) h) word) = edgeRegion O word := by
  subst a'
  rfl

lemma actual_lifted_parent_population_set (O T : Source X) (D : Decoration O T)
    (H : OriginalParentRegistry O.network) (b : T.network.graph.Blob) (A : ActualBlobBigon T.network b) :
    {(liftedOriginalFragment O T D H b A).parents.parent0,
      (liftedOriginalFragment O T D H b A).parents.parent1} =
      ({rawOriginalParent O T D b A false,rawOriginalParent O T D b A true} : Finset O.Edge) := by
  let es := Finset.univ.filter (fun e : O.Edge =>
    O.network.graph.target e = D.vertex A.fragment.parents.hybrid)
  have hcard : es.card = 2 := (originalHybridSite O T D b A).property.1
  have h0 : rawOriginalParent O T D b A false ∈ es :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,actual_raw_original_parent_target O T D b A false⟩
  have h1 : rawOriginalParent O T D b A true ∈ es :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,actual_raw_original_parent_target O T D b A true⟩
  have ht0 : (liftedOriginalFragment O T D H b A).parents.parent0 ∈ es := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(liftedOriginalFragment O T D H b A).parents.target0.trans (H.original_site _)⟩
  have ht1 : (liftedOriginalFragment O T D H b A).parents.parent1 ∈ es := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(liftedOriginalFragment O T D H b A).parents.target1.trans (H.original_site _)⟩
  ext f
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact G1ActualTwoPortBlob.edge_pair_exhaustive es _ _
        (actual_raw_original_parents_different O T D b A) h0 h1 hcard _ ht0
    · exact G1ActualTwoPortBlob.edge_pair_exhaustive es _ _
        (actual_raw_original_parents_different O T D b A) h0 h1 hcard _ ht1
  · rintro (rfl | rfl)
    · exact G1ActualTwoPortBlob.edge_pair_exhaustive es _ _
        (liftedOriginalFragment O T D H b A).parents.different ht0 ht1 hcard _ h0
    · exact G1ActualTwoPortBlob.edge_pair_exhaustive es _ _
        (liftedOriginalFragment O T D H b A).parents.different ht0 ht1 hcard _ h1

/-- A new actual synthetic edge owns exactly the original populations owned
by the four literal current edges removed by its constructed splice. -/
theorem actual_new_span_population_union (O T : Source X) (D : Decoration O T)
    (H : OriginalParentRegistry O.network) (b : T.network.graph.Blob) (A : ActualBlobBigon T.network b) :
    edgeRegion O (newOriginalSpan O T D H b A) =
      (removedEdges T.network b A).biUnion (fun e => recipePopulations O (D.recipe e)) := by
  have hc := actual_bridge_span_populations O T D A.child A.child_bridge
  have he := actual_bridge_span_populations O T D A.entry A.entry_bridge
  have h0 := actual_raw_original_parent_recipe O T D b A false
  have h1 := actual_raw_original_parent_recipe O T D b A true
  unfold newOriginalSpan
  simp only [edgeRegion]
  trans recipePopulations O (D.recipe A.child) ∪
    ({(liftedOriginalFragment O T D H b A).parents.parent0,
      (liftedOriginalFragment O T D H b A).parents.parent1} ∪ recipePopulations O (D.recipe A.entry))
  · apply congrArg₂ (fun x y : Finset O.Edge => x ∪ y)
    · exact (G1OriginatedBridgeBookends.property_mpr_right O
        (fun _ _ word => edgeRegion O word = recipePopulations O (D.recipe A.child))
        (congrArg D.vertex A.child_source).symm _).mpr hc
    · apply congrArg₂ (fun x y : Finset O.Edge => x ∪ y)
      · have hsite : (liftedOriginalFragment O T D H b A).parents.hybrid = D.vertex A.fragment.parents.hybrid :=
          H.original_site _
        exact (property_cast_left O (fun _ _ word => edgeRegion O word =
          {(liftedOriginalFragment O T D H b A).parents.parent0,
            (liftedOriginalFragment O T D H b A).parents.parent1}) hsite _).mpr rfl
      · exact (G1OriginatedBridgeBookends.property_mpr_left O
          (fun _ _ word => edgeRegion O word = recipePopulations O (D.recipe A.entry))
          (congrArg D.vertex A.entry_target).symm _).mpr he
  rw [actual_lifted_parent_population_set]
  have h0' : recipePopulations O (D.recipe A.fragment.parents.parent0) = {rawOriginalParent O T D b A false} := by
    simpa [OriginalHybridParents.parent,recipePopulations] using congrArg (recipePopulations O) h0
  have h1' : recipePopulations O (D.recipe A.fragment.parents.parent1) = {rawOriginalParent O T D b A true} := by
    simpa [OriginalHybridParents.parent,recipePopulations] using congrArg (recipePopulations O) h1
  simp only [removedEdges,Finset.biUnion_insert,Finset.singleton_biUnion,h0',h1']
  ext f
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  tauto

#print axioms actual_new_span_population_union
end G1OriginalRecipePopulationOwnership
