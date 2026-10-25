import G1SpanRegionOriginalOperations

/-! Derive source population separation for neutral original spans until their
LAST closing exit. Contributor: dot, 2026-10-03. No source kernel equality or
independence is a premise. Subsequent original interaction is unrestricted. -/
namespace G1DerivedSpanSeparatedAgenda
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1OriginalSpanRegion
open G1OriginalSpanClosingPhase G1SpanRegionOriginalOperations
open G1OriginalEpochPanelCompression G1ActualJointProgram G1JointSeparatedSourceGeometry
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_neutral_span_population_separator (O : Source.{u,v,w} X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (hn : DescendantNeutral O word)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (inside outside : Finset Copy)
    (hin : ∀ x ∈ inside, SpanLocation O word (copyLocation (state s) x))
    (hout : ∀ y ∈ outside, ¬ O.network.graph.DReach a (O.network.leaf (sample y))) :
    PopulationSeparated (state s) inside outside := by
  intro x hx y hy heq
  have hreg : SpanLocation O word (copyLocation (state s) y) := heq ▸ hin x hx
  exact hout y hy (actual_neutral_span_location_descends O word hn _ _ hreg (s.property.original_descendant y))

/-- Physical graph closure and original operation syntax derive the full
separated actual source agenda. The closing exit is last; output may meet
outside populations and no restriction is imposed on the actual future. -/
theorem actual_original_span_separated_agenda (O : Source.{u,v,w} X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (hn : DescendantNeutral O word)
    (lastEdge : O.Edge) (hend : EndsAt O lastEdge word)
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (ops : List (ProgramStep O.network))
    (hsafe : ∀ op ∈ ops, EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val) {lastEdge} op)
    (s : Code O.network sample) (inside outside : Finset Copy)
    (hin : ∀ x ∈ inside, SpanLocation O word (copyLocation (state s) x))
    (hout : ∀ y ∈ outside, ¬ O.network.graph.DReach a (O.network.leaf (sample y))) :
    SeparatedAgenda O.network r inside outside (ops ++ [.boundary (.exit lastEdge)]) s := by
  induction ops generalizing s with
  | nil =>
      exact ⟨actual_neutral_span_population_separator O word hn s inside outside hin hout,by simp [SeparatedAgenda]⟩
  | cons op ops ih =>
      refine ⟨actual_neutral_span_population_separator O word hn s inside outside hin hout,?_⟩
      intro d hd
      exact ih (fun p hp => hsafe p (List.mem_cons_of_mem op hp)) d
        (actual_span_safe_step_support O word lastEdge hend H gamma common r op (hsafe op (by simp)) s inside hin hd)

end G1DerivedSpanSeparatedAgenda
