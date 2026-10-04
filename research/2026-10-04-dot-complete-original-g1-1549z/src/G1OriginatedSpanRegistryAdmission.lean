import G1OriginalMultiSpanCalendarRow

/-! Constructed physical bridge words retain the SAME original registry at
EVERY pulse. Contributor: dot, 2026-10-03. -/
namespace G1OriginatedSpanRegistryAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1LiftedOriginalBigon G1DecoratedSpliceConstruction G1FiniteOriginalDecoratedCore
open G1OriginalSpanCalendarDecomposition
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def RegistryRecipe (O : Source X) (H : OriginalParentRegistry O.network) : Recipe O → Prop
  | .raw _ => True
  | .span _ _ word => RegistrySpan O.network H word

lemma registry_span_transport (O : Source X) (H : OriginalParentRegistry O.network)
    {a b a' b' : O.Vertex} (ha : a = a') (hb : b = b') (word : OriginalSpan O.network a b) :
    RegistrySpan O.network H (ha ▸ hb ▸ word) ↔ RegistrySpan O.network H word := by
  subst a' b'
  rfl

noncomputable def physicalRecipeSpan (O : Source X) {a b : O.Vertex} (label : Recipe O)
    (endpoints : label.input = a ∧ label.output = b)
    (rawBridge : ∀ f, label = .raw f → O.network.graph.IsBridge f) : OriginalSpan O.network a b := by
  have hep := endpoints
  cases hr : label with
  | raw f =>
      rw [hr] at hep
      have ho := rawBridge f hr
      simp only [Recipe.input,Recipe.output] at hep
      rw [← hep.1,← hep.2]
      exact .edge f (actual_original_bridge_target_ordinary O f ho)
  | span c d word =>
      rw [hr] at hep
      simp only [Recipe.input,Recipe.output] at hep
      rw [← hep.1,← hep.2]
      exact word

lemma actual_physical_recipe_registry (O : Source X) (H : OriginalParentRegistry O.network)
    {a b : O.Vertex} (label : Recipe O) (endpoints : label.input = a ∧ label.output = b)
    (rawBridge : ∀ f, label = .raw f → O.network.graph.IsBridge f)
    (hr : RegistryRecipe O H label) : RegistrySpan O.network H (physicalRecipeSpan O label endpoints rawBridge) := by
  cases label with
  | raw f =>
      simp only [Recipe.input,Recipe.output] at endpoints
      obtain ⟨rfl,rfl⟩ := endpoints
      simp [physicalRecipeSpan,Recipe.input,Recipe.output,RegistrySpan]
  | span c d word =>
      simp only [Recipe.input,Recipe.output] at endpoints
      obtain ⟨rfl,rfl⟩ := endpoints
      simpa [physicalRecipeSpan,Recipe.input,Recipe.output,RegistryRecipe] using hr

lemma actual_bridge_span_registry (O S : Source X) (D : Decoration O S)
    (H : OriginalParentRegistry O.network) (e : S.Edge) (he : S.network.graph.IsBridge e)
    (hr : RegistryRecipe O H (D.recipe e)) : RegistrySpan O.network H (bridgeSpan O S D e he) := by
  change RegistrySpan O.network H (physicalRecipeSpan O (D.recipe e) (D.endpoints e)
    (fun f hf => (D.raw_bridge e f hf).mp he))
  exact actual_physical_recipe_registry O H (D.recipe e) (D.endpoints e) _ hr

lemma actual_lifted_fragment_registry (O S : Source X) (D : Decoration O S)
    (H : OriginalParentRegistry O.network) (b : S.network.graph.Blob)
    (A : G1ActualTwoPortBlob.ActualBlobBigon S.network b) :
    RegistrySpan O.network H (.bigon (liftedOriginalFragment O S D H b A)) := by
  change H.parents (originalHybridSite O S D b A) = H.parents
    ⟨(H.parents (originalHybridSite O S D b A)).hybrid,(H.parents (originalHybridSite O S D b A)).isHybrid⟩
  congr 1
  apply Subtype.ext
  exact (H.original_site _).symm

lemma registry_span_mpr_left (O : Source X) (H : OriginalParentRegistry O.network)
    {a a' b : O.Vertex} (h : a = a') (word : OriginalSpan O.network a' b) :
    RegistrySpan O.network H ((congrArg (fun v => OriginalSpan O.network v b) h).mpr word) ↔
      RegistrySpan O.network H word := by
  subst a'
  rfl

lemma registry_span_mpr_right (O : Source X) (H : OriginalParentRegistry O.network)
    {a b b' : O.Vertex} (h : b = b') (word : OriginalSpan O.network a b') :
    RegistrySpan O.network H ((congrArg (OriginalSpan O.network a) h).mpr word) ↔
      RegistrySpan O.network H word := by
  subst b'
  rfl

lemma registry_span_cast_left (O : Source X) (H : OriginalParentRegistry O.network)
    {a a' b : O.Vertex} (h : a = a') (word : OriginalSpan O.network a b) :
    RegistrySpan O.network H (cast (congrArg (fun v => OriginalSpan O.network v b) h) word) ↔
      RegistrySpan O.network H word := by
  subst a'
  rfl

lemma actual_new_original_span_registry (O S : Source X) (D : Decoration O S)
    (H : OriginalParentRegistry O.network) (b : S.network.graph.Blob)
    (A : G1ActualTwoPortBlob.ActualBlobBigon S.network b)
    (hr : ∀ e, RegistryRecipe O H (D.recipe e)) : RegistrySpan O.network H (newOriginalSpan O S D H b A) := by
  have hchild := actual_bridge_span_registry O S D H A.child A.child_bridge (hr A.child)
  have hentry := actual_bridge_span_registry O S D H A.entry A.entry_bridge (hr A.entry)
  have hbigon := actual_lifted_fragment_registry O S D H b A
  unfold newOriginalSpan
  simp only [RegistrySpan]
  constructor
  · exact (registry_span_mpr_right O H (congrArg D.vertex A.child_source).symm _).mpr hchild
  · constructor
    · have hsite : (liftedOriginalFragment O S D H b A).parents.hybrid = D.vertex A.fragment.parents.hybrid :=
        H.original_site _
      exact (registry_span_cast_left O H hsite _).mpr hbigon
    · exact (registry_span_mpr_left O H (congrArg D.vertex A.entry_target).symm _).mpr hentry

theorem actual_originated_recipes_registered (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) :
    ∀ e, RegistryRecipe O H (D.recipe e) := by
  induction hD with
  | initial => exact fun _ => trivial
  | @splice S D prior b hb hp ih =>
      intro e
      cases e with
      | inl e => exact ih e.val
      | inr z => exact actual_new_original_span_registry O S D H b _ ih

theorem actual_originated_bridge_word_registered (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (e : T.Edge) (he : T.network.graph.IsBridge e) :
    RegistrySpan O.network H (bridgeSpan O T D e he) :=
  actual_bridge_span_registry O T D H e he (actual_originated_recipes_registered O H D hD e)

#print axioms actual_originated_bridge_word_registered
end G1OriginatedSpanRegistryAdmission
