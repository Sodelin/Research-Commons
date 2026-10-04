import G1OriginalSpanBridgeBookends

/-! Both cut-edge bookends are inherited through EVERY constructed splice.
Contributor: dot, 2026-10-03. The original cuts, not synthetic-rate connectors,
admit naturally initialized interfaces and precise closing boundaries. -/
namespace G1OriginatedBridgeBookends
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1LiftedOriginalBigon G1DecoratedSpliceConstruction G1FiniteOriginalDecoratedCore
open G1OriginalSpanBridgeBookends
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma property_mpr_left (O : Source X)
    (P : (a b : O.Vertex) → OriginalSpan O.network a b → Prop)
    {a a' b : O.Vertex} (h : a = a') (word : OriginalSpan O.network a' b) :
    P a b ((congrArg (fun v => OriginalSpan O.network v b) h).mpr word) ↔ P a' b word := by
  subst a'
  rfl

lemma property_mpr_right (O : Source X)
    (P : (a b : O.Vertex) → OriginalSpan O.network a b → Prop)
    {a b b' : O.Vertex} (h : b = b') (word : OriginalSpan O.network a b') :
    P a b ((congrArg (OriginalSpan O.network a) h).mpr word) ↔ P a b' word := by
  subst b'
  rfl

lemma actual_new_original_span_bookends (O S : Source X) (D : Decoration O S)
    (H : OriginalParentRegistry O.network) (b : S.network.graph.Blob)
    (A : G1ActualTwoPortBlob.ActualBlobBigon S.network b)
    (hr : ∀ e, BookendedRecipe O (D.recipe e)) :
    StartsBridge O (newOriginalSpan O S D H b A) ∧ EndsBridge O (newOriginalSpan O S D H b A) := by
  have hchild := actual_bridge_span_bookends O S D A.child A.child_bridge (hr A.child)
  have hentry := actual_bridge_span_bookends O S D A.entry A.entry_bridge (hr A.entry)
  unfold newOriginalSpan
  simp only [StartsBridge,EndsBridge]
  constructor
  · exact (property_mpr_right O (fun _ _ word => StartsBridge O word)
      (congrArg D.vertex A.child_source).symm _).mpr hchild.1
  · exact (property_mpr_left O (fun _ _ word => EndsBridge O word)
      (congrArg D.vertex A.entry_target).symm _).mpr hentry.2

theorem actual_originated_recipes_bookended (O : Source X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) :
    ∀ e, BookendedRecipe O (D.recipe e) := by
  induction hD with
  | initial => exact fun _ => trivial
  | @splice S D prior b hb hp ih =>
      intro e
      cases e with
      | inl e => exact ih e.val
      | inr z => exact actual_new_original_span_bookends O S D H b _ ih

theorem actual_originated_bridge_original_cut_endpoints (O : Source X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (e : T.Edge) (he : T.network.graph.IsBridge e) :
    (∃ c : O.Edge, O.network.graph.IsBridge c ∧ O.network.graph.target c = D.vertex (T.network.graph.target e)) ∧
    (∃ c : O.Edge, O.network.graph.IsBridge c ∧ O.network.graph.source c = D.vertex (T.network.graph.source e)) := by
  have hw := actual_bridge_span_bookends O T D e he (actual_originated_recipes_bookended O H D hD e)
  exact ⟨actual_start_bridge_endpoint O _ hw.1,actual_end_bridge_endpoint O _ hw.2⟩

#print axioms actual_originated_bridge_original_cut_endpoints
end G1OriginatedBridgeBookends
