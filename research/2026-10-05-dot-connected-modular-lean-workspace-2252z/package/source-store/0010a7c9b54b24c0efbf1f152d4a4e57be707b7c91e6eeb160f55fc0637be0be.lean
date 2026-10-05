import G1CanonicalCompactCompletedReplacement
import G1BinaryCoreBudgets

/-! Endpoint-typed ORIGINAL source spans for decorated core edges.
Contributor: dot, 2026-10-03. Every program/rate/register remains on ONE
original source. Final connectors may reach the retained original root. -/
namespace G1OriginalDecoratedSpan
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.UnrankedGenealogyObservation
open G1CutChildPorts G1NonrootBigonKernel G1ExtractedComponentProgram
open G1SameOriginalExteriorContinuation
open G1ContextualForestReplacement G1OriginalCurrentRootReconstruction
open scoped Classical
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- A literal finite original source word; no desired kernel is a field. -/
inductive OriginalSpan (N : RootedBinary V E X) : V → V → Type _
  | edge (e : E) (ordinary : N.graph.inDegree (N.graph.target e) = 1) :
      OriginalSpan N (N.graph.target e) (N.graph.source e)
  | bigon (B : NonrootBigon N) : OriginalSpan N B.parents.hybrid B.upper
  | append {a b c : V} (first : OriginalSpan N a b) (last : OriginalSpan N b c) : OriginalSpan N a c

noncomputable def spanProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (gamma : V → unitInterval) (common : V → Bool) {a b : V} : OriginalSpan N a b → List (ProgramStep N)
  | .edge e degree => edgeProgram N C e degree
  | .bigon B => bigonProgram N C B (gamma B.parents.hybrid) (common B.parents.hybrid)
  | .append first last => spanProgram N C gamma common first ++ spanProgram N C gamma common last

/-- Every original span exits at its typed ORIGINAL upper endpoint. It also
includes an ordinary last population ending at the retained original root. -/
theorem actual_original_span_exit_population (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (gamma : V → unitInterval) (common : V → Bool)
    {a b : V} (word : OriginalSpan N a b) (s : Code N sample)
    (hs : ∀ l ∈ (state s).live, (state s).location l = .node a)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r (spanProgram N C gamma common word) s).support) :
    ∀ l ∈ (state d).live, (state d).location l = .node b := by
  induction word generalizing s d with
  | edge e degree => exact actual_original_edge_exit_population N C r e degree s hs hd
  | bigon B => exact actual_nonroot_bigon_exit_population N C r B _ _ s hs hd
  | append first last ihfirst ihlast =>
      rw [spanProgram,actual_source_program_append] at hd
      obtain ⟨z,hz,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ihlast z (ihfirst s hs hz) hd

/-- The actual K family uses the true independently initialized CURRENT-root
carrier, arbitrary already formed entering forests and the original source. -/
noncomputable def originalSpanK (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (gamma : V → unitInterval) (common : V → Bool)
    {a b : V} (word : OriginalSpan N a b) (s : Code N sample)
    (hs : ∀ l ∈ (state s).live, (state s).location l = .node a) :=
  smallerCurrentRootKernel N r (spanProgram N C gamma common word) s (.node a) hs

theorem actual_original_span_cap_context (N : RootedBinary V E X) {sample : Copy → X}
    {History Obs : Type*} (C : Calendar N.graph) (r : PositivePairRates E)
    (gamma : V → unitInterval) (common : V → Bool) {a b : V} (word : OriginalSpan N a b)
    (s : Code N sample) (hs : ∀ l ∈ (state s).live, (state s).location l = .node a)
    (m : Nat) (cap : (state s).live.card ≤ m) (history : History)
    (exterior : History × (V → Bool) × Finset (UnrankedTree Copy) → PMF Obs) :
    Fintype.card (SelectedCopy (state s).live) ≤ m ∧
    (∀ d ∈ (sourceProgram N r (spanProgram N C gamma common word) s).support,
      ∀ l ∈ (state d).live, (state d).location l = .node b) ∧
    ((sourceProgram N r (spanProgram N C gamma common word) s).bind
      (fun d => exterior (history,(state d).register,rootForest N d)) =
      (originalSpanK N C r gamma common word s hs).bind
        (fun F => exterior (history,(state s).register,
          F.image (G1OpaqueSourceGrafting.graftUnranked (fun l => (state s).genealogy l.val))))) := by
  refine ⟨actual_kernel_carrier_cap N s m cap,?_,?_⟩
  · exact fun d hd => actual_original_span_exit_population N C r gamma common word s hs hd
  · exact actual_original_contextual_forest_replacement N r _ s (.node a) hs history exterior

#print axioms actual_original_span_cap_context
end G1OriginalDecoratedSpan
