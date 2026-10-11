import G1ConcurrentSpanPhysicalSeparation

/-! Actual joint original-source law in a concurrent actor window. Literal
original operations are processed once; tensor factorization is derived from
population ownership and real support closure. -/
namespace G1ConcurrentOriginalSourceWindow
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanRegion G1OriginatedClosingSourceAdmission
open G1OriginalSpanClosingPhase G1OriginalSpanClosingSourceRow
open G1SpanRegionOriginalOperations G1ConcurrentSpanPhysicalSeparation
open G1OriginalEpochPanelCompression G1ActualJointProgram G1ActualJointEpoch
open G1ActualJointGenerator UnifiedLean.Source.SourceFiniteProjection
open G1JointSeparatedSourceGeometry
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- A concurrent window stops before either actor's literal closing cut.
Both panels stay in disjoint derived regions through every actual operation. -/
theorem actual_concurrent_originated_window_separated (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (e f : T.Edge) (he : T.network.graph.IsBridge e)
    (hf : T.network.graph.IsBridge f) (hef : e ≠ f)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (ops : List (ProgramStep O.network))
    (safeLeft : ∀ op ∈ ops, EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val)
      {originatedLastCut O H D hD e he} op)
    (safeRight : ∀ op ∈ ops, EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val)
      {originatedLastCut O H D hD f hf} op)
    (s : Code O.network sample) (left right : Finset Copy)
    (hl : ∀ x ∈ left, SpanLocation O (bridgeSpan O T D e he) (copyLocation (state s) x))
    (hr : ∀ x ∈ right, SpanLocation O (bridgeSpan O T D f hf) (copyLocation (state s) x)) :
    SeparatedAgenda O.network r left right ops s := by
  have hlastLeft := actual_original_last_cut O (bridgeSpan O T D e he)
    (G1OriginalSpanBridgeBookends.actual_bridge_span_bookends O T D e he
      (G1OriginatedBridgeBookends.actual_originated_recipes_bookended O H D hD e)).2
  have hlastRight := actual_original_last_cut O (bridgeSpan O T D f hf)
    (G1OriginalSpanBridgeBookends.actual_bridge_span_bookends O T D f hf
      (G1OriginatedBridgeBookends.actual_originated_recipes_bookended O H D hD f)).2
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih =>
      refine ⟨actual_concurrent_originated_span_panel_separator O H D hD e f he hf hef s left right hl hr,?_⟩
      intro d hd
      exact ih (fun q hq => safeLeft q (List.mem_cons_of_mem op hq))
        (fun q hq => safeRight q (List.mem_cons_of_mem op hq)) d
        (actual_span_safe_step_support O _ _ hlastLeft.2.2 H gamma common r op
          (safeLeft op (by simp)) s left hl hd)
        (actual_span_safe_step_support O _ _ hlastRight.2.2 H gamma common r op
          (safeRight op (by simp)) s right hr hd)

/-- The joint complete selected genealogy/population/SAME-register law factors
into the two ACTUAL selected window kernels. The full original window occurs
once on the left; no fitted synthetic rate or supplied law enters. -/
theorem actual_concurrent_originated_window_source_law (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (e f : T.Edge) (he : T.network.graph.IsBridge e)
    (hf : T.network.graph.IsBridge f) (hef : e ≠ f)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (ops : List (ProgramStep O.network))
    (safeLeft : ∀ op ∈ ops, EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val)
      {originatedLastCut O H D hD e he} op)
    (safeRight : ∀ op ∈ ops, EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val)
      {originatedLastCut O H D hD f hf} op)
    (s : Code O.network sample) (left right : Finset Copy)
    (hl : ∀ x ∈ left, SpanLocation O (bridgeSpan O T D e he) (copyLocation (state s) x))
    (hr : ∀ x ∈ right, SpanLocation O (bridgeSpan O T D f hf) (copyLocation (state s) x)) :
    (sourceProgram O.network r ops s).map (jointProjection O.network left right) =
      independentProduct (selectedProgram O.network r left ops (projection O.network left s))
        (selectedProgram O.network r right ops (projection O.network right s)) := by
  apply actual_separated_joint_program_law
  exact actual_concurrent_originated_window_separated O H D hD e f he hf hef gamma common r ops
    safeLeft safeRight s left right hl hr

#print axioms actual_concurrent_originated_window_source_law
end G1ConcurrentOriginalSourceWindow
