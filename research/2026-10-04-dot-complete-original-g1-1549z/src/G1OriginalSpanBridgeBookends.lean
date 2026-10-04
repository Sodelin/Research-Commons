import G1OriginatedBridgeCalendarAdmission

/-! Physical original cut-edge bookends of generated decorated bridge words.
Contributor: dot, 2026-10-03. No kernel/output equalities are admission fields. -/
namespace G1OriginalSpanBridgeBookends
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1OriginatedSpanRegistryAdmission
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def StartsBridge (O : Source X) {a b : O.Vertex} : OriginalSpan O.network a b → Prop
  | .edge e _ => O.network.graph.IsBridge e
  | .bigon _ => False
  | .append first _ => StartsBridge O first

def EndsBridge (O : Source X) {a b : O.Vertex} : OriginalSpan O.network a b → Prop
  | .edge e _ => O.network.graph.IsBridge e
  | .bigon _ => False
  | .append _ last => EndsBridge O last

def BookendedRecipe (O : Source X) : Recipe O → Prop
  | .raw _ => True
  | .span _ _ word => StartsBridge O word ∧ EndsBridge O word

lemma actual_recipe_span_bookends (O : Source X) {a b : O.Vertex} (label : Recipe O)
    (ep : label.input = a ∧ label.output = b)
    (rawBridge : ∀ f, label = .raw f → O.network.graph.IsBridge f)
    (hr : BookendedRecipe O label) :
    StartsBridge O (physicalRecipeSpan O label ep rawBridge) ∧
      EndsBridge O (physicalRecipeSpan O label ep rawBridge) := by
  cases label with
  | raw f =>
      simp only [Recipe.input,Recipe.output] at ep
      obtain ⟨rfl,rfl⟩ := ep
      simpa [physicalRecipeSpan,StartsBridge,EndsBridge] using And.intro (rawBridge f rfl) (rawBridge f rfl)
  | span c d word =>
      simp only [Recipe.input,Recipe.output] at ep
      obtain ⟨rfl,rfl⟩ := ep
      simpa [physicalRecipeSpan,BookendedRecipe] using hr

lemma actual_bridge_span_bookends (O S : Source X) (D : Decoration O S)
    (e : S.Edge) (he : S.network.graph.IsBridge e) (hr : BookendedRecipe O (D.recipe e)) :
    StartsBridge O (bridgeSpan O S D e he) ∧ EndsBridge O (bridgeSpan O S D e he) := by
  change StartsBridge O (physicalRecipeSpan O (D.recipe e) (D.endpoints e) (fun f hf => (D.raw_bridge e f hf).mp he)) ∧
    EndsBridge O (physicalRecipeSpan O (D.recipe e) (D.endpoints e) (fun f hf => (D.raw_bridge e f hf).mp he))
  exact actual_recipe_span_bookends O _ _ (fun f hf => (D.raw_bridge e f hf).mp he) hr

lemma actual_start_bridge_endpoint (O : Source X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (h : StartsBridge O word) :
    ∃ e : O.Edge, O.network.graph.IsBridge e ∧ O.network.graph.target e = a := by
  induction word with
  | edge e _ => exact ⟨e,h,rfl⟩
  | bigon _ => exact False.elim h
  | append _ _ ih _ => exact ih h

lemma actual_end_bridge_endpoint (O : Source X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (h : EndsBridge O word) :
    ∃ e : O.Edge, O.network.graph.IsBridge e ∧ O.network.graph.source e = b := by
  induction word with
  | edge e _ => exact ⟨e,h,rfl⟩
  | bigon _ => exact False.elim h
  | append _ _ _ ih => exact ih h

end G1OriginalSpanBridgeBookends
