import G1DecoratedSpliceConstruction

/-! Finite bounded physical cores carrying CONSTRUCTED ORIGINAL source-word
provenance. Contributor: dot, 2026-10-03. This source admission is not yet the
full repeated decorated-interpreter law or displayed-target theorem. -/
namespace G1FiniteOriginalDecoratedCore
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.UnrankedGenealogyObservation
open G1ContextualForestReplacement
open G1ActualGraphNormalization G1BinaryCoreBudgets G1OriginalDecoratedSpan
open G1DecoratedOriginalProvenance G1DecoratedSpliceConstruction G1ReducedCoreCounts
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- Provenance is generated from the actual original source and the exact
constructed graph splices, not supplied as an arbitrary decoration. -/
inductive Originated (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network) :
    {S : Source X} → Decoration O S → Prop
  | initial : Originated O H (initialDecoration O)
  | splice {S : Source X} (D : Decoration O S) (prior : Originated O H D)
      (b : S.network.graph.Blob) (hb : b ≠ S.network.graph.blobOf S.network.root)
      (hp : Fintype.card (S.network.BlobPort b) = 2) :
      Originated O H (normalizedSpliceDecoration O S D H b hb hp)

theorem actual_steps_construct_decorations (O : Source X) (H : OriginalParentRegistry O.network)
    {S T : Source X} (steps : Steps S T) (D : Decoration O S) (hD : Originated O H D) :
    ∃ K : Decoration O T, Originated O H K := by
  induction steps with
  | refl => exact ⟨D,hD⟩
  | @tail T U _ hstep ih =>
      obtain ⟨K,hK⟩ := ih
      cases hstep with
      | splice b hb hp => exact ⟨normalizedSpliceDecoration O T K H b hb hp,Originated.splice K hK b hb hp⟩

/-- A finite actual reduced graph with accepted census bounds, ALL original
root-blob vertices retained and source-generated word labels is constructed. -/
theorem actual_finite_original_decorated_core (O : Source X) (H : OriginalParentRegistry O.network) :
    ∃ (T : Source X) (D : Decoration O T), Steps O T ∧ Originated O H D ∧ Reduced T ∧
      (hybrids T.network).card ≤ 2 * Fintype.card X - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card X - 5 ∧
      Fintype.card T.Edge ≤ 8 * Fintype.card X - 8 := by
  obtain ⟨T,hsteps,hr,hh,hv,he⟩ := actual_finite_bounded_core O
  obtain ⟨D,hD⟩ := actual_steps_construct_decorations O H hsteps (initialDecoration O) (Originated.initial)
  exact ⟨T,D,hsteps,hD,hr,hh,hv,he⟩

/-- Every admitted decorated bridge has a source-derived CURRENT-root K
family from ONE fixed original source, with endpoint/history/register and
opaque forest transport as proved for the literal original span. -/
theorem actual_decorated_bridge_original_source_exit
    (O T : Source X) (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (e : T.Edge) (he : T.network.graph.IsBridge e)
    (s : Code O.network sample)
    (hs : ∀ l ∈ (state s).live, (state s).location l = .node (D.vertex (T.network.graph.target e)))
    {d : Code O.network sample}
    (hd : d ∈ (UnifiedLean.Source.SourceProgramTransport.sourceProgram O.network r
      (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he)) s).support) :
    ∀ l ∈ (state d).live, (state d).location l = .node (D.vertex (T.network.graph.source e)) :=
  actual_original_span_exit_population O.network O.calendar r gamma common (bridgeSpan O T D e he) s hs hd

theorem actual_decorated_bridge_cap_context (O T : Source X) (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X} {History Obs : Type*}
    (r : PositivePairRates O.Edge) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (e : T.Edge) (he : T.network.graph.IsBridge e) (s : Code O.network sample)
    (hs : ∀ l ∈ (state s).live, (state s).location l = .node (D.vertex (T.network.graph.target e)))
    (m : Nat) (cap : (state s).live.card ≤ m) (history : History)
    (exterior : History × (O.Vertex → Bool) × Finset (UnrankedTree Copy) → PMF Obs) :
    Fintype.card (SelectedCopy (state s).live) ≤ m ∧
    (∀ d ∈ (UnifiedLean.Source.SourceProgramTransport.sourceProgram O.network r
      (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he)) s).support,
      ∀ l ∈ (state d).live, (state d).location l = .node (D.vertex (T.network.graph.source e))) ∧
    ((UnifiedLean.Source.SourceProgramTransport.sourceProgram O.network r
      (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he)) s).bind
        (fun d => exterior (history,(state d).register,rootForest O.network d)) =
      (originalSpanK O.network O.calendar r gamma common (bridgeSpan O T D e he) s hs).bind
        (fun F => exterior (history,(state s).register,
          F.image (G1OpaqueSourceGrafting.graftUnranked (fun l => (state s).genealogy l.val))))) :=
  actual_original_span_cap_context O.network O.calendar r gamma common (bridgeSpan O T D e he)
    s hs m cap history exterior

#print axioms actual_decorated_bridge_cap_context
end G1FiniteOriginalDecoratedCore
