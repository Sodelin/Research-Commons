import G1OriginatedTaxonReachTransport

/-! Literal original populations and nonterminal node sites of a source span.
Contributor: dot, 2026-10-03. Descendant isolation is a separate graph predicate. -/
namespace G1OriginalSpanRegion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open G1ActualGraphNormalization G1OriginalDecoratedSpan
open G1OriginalSpanAtomAdmission G1OriginalNodeBatchBinding G1OriginalComponentNodeIdentity
open G1OriginalSpanCalendarDecomposition
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def nodeRegion (O : Source X) {a b : O.Vertex} : OriginalSpan O.network a b → Finset O.Vertex
  | .edge e _ => {O.network.graph.target e}
  | .bigon B => {B.parents.hybrid}
  | .append first last => nodeRegion O first ∪ nodeRegion O last

noncomputable def edgeRegion (O : Source X) {a b : O.Vertex} : OriginalSpan O.network a b → Finset O.Edge
  | .edge e _ => {e}
  | .bigon B => {B.parents.parent0,B.parents.parent1}
  | .append first last => edgeRegion O first ∪ edgeRegion O last

noncomputable def SpanLocation (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b) :
    Location O.Vertex O.Edge → Prop
  | .node v => v ∈ nodeRegion O word
  | .edge e => e ∈ edgeRegion O word
  | .rootPopulation _ => False

lemma actual_span_input_in_region (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b) :
    a ∈ nodeRegion O word := by
  induction word with
  | edge _ _ => exact Finset.mem_singleton_self _
  | bigon _ => exact Finset.mem_singleton_self _
  | append _ _ h _ => exact Finset.mem_union_left _ h

lemma actual_span_nodes_nonroot (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b) :
    ∀ v ∈ nodeRegion O word, v ≠ O.network.root := by
  induction word with
  | edge e _ =>
      intro v hv
      have h : v = O.network.graph.target e := Finset.mem_singleton.mp hv
      subst v; exact O.network.edge_target_ne_root e
  | bigon B =>
      intro v hv
      have h : v = B.parents.hybrid := Finset.mem_singleton.mp hv
      subst v
      rw [← B.parents.target0]
      exact O.network.edge_target_ne_root _
  | append _ _ hfirst hlast =>
      intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · exact hfirst v h
      · exact hlast v h

lemma actual_span_incoming_closed (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b) :
    ∀ v ∈ nodeRegion O word, incomingEdges O.network v ⊆ edgeRegion O word := by
  induction word with
  | edge e degree =>
      intro v hv f hf
      have hv : v = O.network.graph.target e := Finset.mem_singleton.mp hv
      subst v
      simpa only [edgeRegion,actual_single_incoming_edges O.network e degree] using hf
  | bigon B =>
      intro v hv f hf
      have hv : v = B.parents.hybrid := Finset.mem_singleton.mp hv
      subst v
      simpa only [edgeRegion,actual_bigon_incoming_pair O.network B] using hf
  | append _ _ hfirst hlast =>
      intro v hv e he
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_left _ (hfirst v hv he)
      · exact Finset.mem_union_right _ (hlast v hv he)

lemma actual_span_edge_target_inside (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b) :
    ∀ e ∈ edgeRegion O word, O.network.graph.target e ∈ nodeRegion O word := by
  induction word with
  | edge e _ =>
      intro f hf
      have h : f = e := Finset.mem_singleton.mp hf
      subst f; exact Finset.mem_singleton_self _
  | bigon B =>
      intro e he
      rcases (by simpa only [edgeRegion,Finset.mem_insert,Finset.mem_singleton] using he :
        e = B.parents.parent0 ∨ e = B.parents.parent1) with rfl | rfl
      · simpa only [nodeRegion,B.parents.target0] using Finset.mem_singleton_self B.parents.hybrid
      · simpa only [nodeRegion,B.parents.target1] using Finset.mem_singleton_self B.parents.hybrid
  | append _ _ hfirst hlast =>
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact Finset.mem_union_left _ (hfirst e he)
      · exact Finset.mem_union_right _ (hlast e he)

/-- A physical graph predicate. It is false for general words that traverse a
branching node and is derived later for labels produced by actual splices. -/
def DescendantNeutral (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b) : Prop :=
  ∀ v ∈ nodeRegion O word, ∀ x : X,
    O.network.graph.DReach v (O.network.leaf x) ↔ O.network.graph.DReach a (O.network.leaf x)

end G1OriginalSpanRegion
