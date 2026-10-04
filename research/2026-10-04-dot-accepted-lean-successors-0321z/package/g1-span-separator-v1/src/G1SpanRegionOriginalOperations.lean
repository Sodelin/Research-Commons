import G1SpanRegionExitClosure

/-! Actual original generator/boundary support preserves a physical span
region until its precise closing cut. Contributor: dot, 2026-10-03. -/
namespace G1SpanRegionOriginalOperations
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourcePoissonKernel
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1OriginalSpanRegion
open G1SpanRegionExitClosure G1OriginalSpanClosingPhase G1NonrootBigonKernel
open G1OriginalNodeBatchBinding G1OriginalEpochPanelCompression
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_span_node_movement_closed (O : Source X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (v : O.Vertex) {old new : Location O.Vertex O.Edge}
    (hp : SpanLocation O word old) (hm : NodeMovement O.network v old new) : SpanLocation O word new := by
  unfold NodeMovement at hm
  by_cases hn : old = .node v
  · rw [if_pos hn] at hm
    rw [hn] at hp
    have hr := actual_span_nodes_nonroot O word v hp
    rw [if_neg hr] at hm
    obtain ⟨e,he,hnew⟩ := hm
    rw [hnew]
    exact actual_span_incoming_closed O word v hp
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  · rw [if_neg hn] at hm
    exact hm ▸ hp

lemma actual_span_exit_closed (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b)
    (lastEdge : O.Edge) (hlast : EndsAt O lastEdge word) (edge : O.Edge) (hne : edge ≠ lastEdge)
    {old : Location O.Vertex O.Edge} (hp : SpanLocation O word old) :
    SpanLocation O word (exitLocation O.network edge old) := by
  unfold exitLocation
  by_cases ho : old = .edge edge
  · rw [if_pos ho]
    rw [ho] at hp
    exact actual_nonclosing_exit_stays_inside O word lastEdge hlast edge hp hne
  · rw [if_neg ho]; exact hp

lemma actual_span_safe_step_support (O : Source.{u,v,w} X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (lastEdge : O.Edge) (hlast : EndsAt O lastEdge word)
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (op : ProgramStep O.network)
    (hsafe : EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val) {lastEdge} op)
    (s : Code O.network sample) (inside : Finset Copy)
    (hin : ∀ x ∈ inside, SpanLocation O word (copyLocation (state s) x))
    {d : Code O.network sample} (hd : d ∈ (sourceProgramStep O.network r op s).support) :
    ∀ x ∈ inside, SpanLocation O word (copyLocation (state d) x) := by
  rcases hsafe with ⟨t,rfl⟩ | ⟨e,hne,rfl⟩ | ⟨v,rfl⟩
  · intro x hx
    change d ∈ (sourceTimeKernel O.network r t s).support at hd
    rw [actual_time_copy_population O.network r t s hd x]
    exact hin x hx
  · have heq : d = exitCode O.network s e := by simpa [sourceProgramStep,boundaryKernel] using hd
    subst d
    intro x hx
    rw [exitCode_copyLocation]
    exact actual_span_exit_closed O word lastEdge hlast e (by simpa using hne) (hin x hx)
  · intro x hx
    exact actual_span_node_movement_closed O word v (hin x hx)
      (actual_original_node_kernel_movement O.network H (fun h => gamma h.val) (fun h => common h.val) v s hd x)

/-- Source spatial admission and the DERIVED neutral graph region exclude
all actual original exterior samples from every internal span population. -/
lemma actual_neutral_span_location_descends (O : Source X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (hn : DescendantNeutral O word)
    (p : Location O.Vertex O.Edge) (x : X) (hp : SpanLocation O word p)
    (hd : DescendsTo O.network p x) : O.network.graph.DReach a (O.network.leaf x) := by
  cases p with
  | rootPopulation _ => exact False.elim hp
  | node v => exact (hn v hp x).mp hd
  | edge e => exact (hn _ (actual_span_edge_target_inside O word e hp) x).mp hd

end G1SpanRegionOriginalOperations
