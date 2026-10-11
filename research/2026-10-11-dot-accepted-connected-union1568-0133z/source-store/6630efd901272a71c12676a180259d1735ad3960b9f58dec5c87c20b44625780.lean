import G1OriginalSpanRegion

/-! Source-generated bridge regions are descendant-neutral. This graph
admission is DERIVED from actual splices, not true for arbitrary words.
Contributor: dot, 2026-10-03. -/
namespace G1OriginatedNeutralSpanRegion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1LiftedOriginalBigon G1DecoratedSpliceConstruction G1FiniteOriginalDecoratedCore
open G1OriginatedSpanRegistryAdmission G1OriginatedBridgeBookends
open G1OriginalSpanRegion G1OriginatedTaxonReachTransport G1ComponentDescendantClosure
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def NeutralRecipe (O : Source X) : Recipe O → Prop
  | .raw _ => True
  | .span _ _ word => DescendantNeutral O word

lemma actual_edge_span_neutral (O : Source X) (e : O.Edge)
    (degree : O.network.graph.inDegree (O.network.graph.target e) = 1) :
    DescendantNeutral O (.edge e degree) := by
  intro v hv x
  have hv : v = O.network.graph.target e := Finset.mem_singleton.mp hv
  subst v; rfl

lemma actual_bigon_span_neutral (O : Source X) (B : G1NonrootBigonKernel.NonrootBigon O.network) :
    DescendantNeutral O (.bigon B) := by
  intro v hv x
  have hv : v = B.parents.hybrid := Finset.mem_singleton.mp hv
  subst v; rfl

lemma actual_append_region_neutral (O : Source X) {a b c : O.Vertex}
    (first : OriginalSpan O.network a b) (last : OriginalSpan O.network b c)
    (hf : DescendantNeutral O first) (hl : DescendantNeutral O last)
    (hjoin : ∀ x : X, O.network.graph.DReach b (O.network.leaf x) ↔ O.network.graph.DReach a (O.network.leaf x)) :
    DescendantNeutral O (.append first last) := by
  intro v hv x
  rcases Finset.mem_union.mp hv with hv | hv
  · exact hf v hv x
  · exact (hl v hv x).trans (hjoin x)

lemma actual_recipe_span_neutral (O : Source X) {a b : O.Vertex} (label : Recipe O)
    (ep : label.input = a ∧ label.output = b)
    (rawBridge : ∀ f, label = .raw f → O.network.graph.IsBridge f)
    (hr : NeutralRecipe O label) : DescendantNeutral O (physicalRecipeSpan O label ep rawBridge) := by
  cases label with
  | raw f =>
      simp only [Recipe.input,Recipe.output] at ep
      obtain ⟨rfl,rfl⟩ := ep
      simpa [physicalRecipeSpan] using actual_edge_span_neutral O f (actual_original_bridge_target_ordinary O f (rawBridge f rfl))
  | span c d word =>
      simp only [Recipe.input,Recipe.output] at ep
      obtain ⟨rfl,rfl⟩ := ep
      simpa [physicalRecipeSpan,NeutralRecipe] using hr

lemma actual_bridge_span_neutral (O S : Source X) (D : Decoration O S)
    (e : S.Edge) (he : S.network.graph.IsBridge e) (hr : NeutralRecipe O (D.recipe e)) :
    DescendantNeutral O (bridgeSpan O S D e he) := by
  change DescendantNeutral O (physicalRecipeSpan O (D.recipe e) (D.endpoints e) (fun f hf => (D.raw_bridge e f hf).mp he))
  exact actual_recipe_span_neutral O _ _ _ hr

lemma property_cast_left (O : Source X)
    (P : (a b : O.Vertex) → OriginalSpan O.network a b → Prop)
    {a a' b : O.Vertex} (h : a = a') (word : OriginalSpan O.network a b) :
    P a' b (cast (congrArg (fun v => OriginalSpan O.network v b) h) word) ↔ P a b word := by
  subst a'
  rfl

lemma actual_new_original_region_neutral (O S : Source X) (D : Decoration O S)
    (H : OriginalParentRegistry O.network) (hD : Originated O H D)
    (b : S.network.graph.Blob) (A : G1ActualTwoPortBlob.ActualBlobBigon S.network b)
    (hr : ∀ e, NeutralRecipe O (D.recipe e)) : DescendantNeutral O (newOriginalSpan O S D H b A) := by
  have hchild := actual_bridge_span_neutral O S D A.child A.child_bridge (hr A.child)
  have hentry := actual_bridge_span_neutral O S D A.entry A.entry_bridge (hr A.entry)
  have hhy : ∀ x : X,
      O.network.graph.DReach (D.vertex A.fragment.parents.hybrid) (O.network.leaf x) ↔
        O.network.graph.DReach (D.vertex (S.network.graph.target A.child)) (O.network.leaf x) := by
    intro x
    exact (actual_originated_taxon_reach O H D hD _ x).symm.trans
      ((actual_hybrid_descendant_closure S.network b A x).trans (actual_originated_taxon_reach O H D hD _ x))
  have hup : ∀ x : X,
      O.network.graph.DReach (D.vertex A.fragment.upper) (O.network.leaf x) ↔
        O.network.graph.DReach (D.vertex A.fragment.parents.hybrid) (O.network.leaf x) := by
    intro x
    exact (actual_originated_taxon_reach O H D hD _ x).symm.trans
      ((actual_upper_descendant_closure S.network S.cutChild b A x).trans
        ((actual_hybrid_descendant_closure S.network b A x).symm.trans (actual_originated_taxon_reach O H D hD _ x)))
  unfold newOriginalSpan
  apply actual_append_region_neutral
  · exact (property_mpr_right O (fun _ _ word => DescendantNeutral O word)
      (congrArg D.vertex A.child_source).symm _).mpr hchild
  · apply actual_append_region_neutral
    · have hsite : (liftedOriginalFragment O S D H b A).parents.hybrid = D.vertex A.fragment.parents.hybrid :=
        H.original_site _
      exact (property_cast_left O (fun _ _ word => DescendantNeutral O word) hsite _).mpr
        (actual_bigon_span_neutral O (liftedOriginalFragment O S D H b A))
    · exact (property_mpr_left O (fun _ _ word => DescendantNeutral O word)
        (congrArg D.vertex A.entry_target).symm _).mpr hentry
    · exact hup
  · exact hhy

theorem actual_originated_recipes_neutral (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) :
    ∀ e, NeutralRecipe O (D.recipe e) := by
  induction hD with
  | initial => exact fun _ => trivial
  | @splice S D prior b hb hp ih =>
      intro e
      cases e with
      | inl e => exact ih e.val
      | inr z => exact actual_new_original_region_neutral O S D H prior b _ ih

theorem actual_originated_bridge_region_neutral (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (e : T.Edge) (he : T.network.graph.IsBridge e) :
    DescendantNeutral O (bridgeSpan O T D e he) :=
  actual_bridge_span_neutral O T D e he (actual_originated_recipes_neutral O H D hD e)

#print axioms actual_originated_bridge_region_neutral
end G1OriginatedNeutralSpanRegion
