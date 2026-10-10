import G1ExactSemidirectedPartnerAdmission

/-! Attach actual outer-labelled semidirected partner admission to the
SAME checked core/decoration selected before every stochastic quantifier.
Both original and output are literal former-root-suppressed faithful curved
multigraph partners with taxon-only unbounded-face admission. Parallel arcs
and hybrid direction marks follow the exact original rooted-partner rule.
The existing raw-source stochastic/target/history theorem is reused intact.
No full Code-stage or ancestral-jump trajectory equality is asserted. -/
namespace G1OneSameOuterSemidirectedCoreAssembly
set_option backward.isDefEq.respectTransparency false
open G1OneSameOriginalCoreAssembly G1ExactSemidirectedPartnerAdmission
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceForestSilentPruning
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore G1ReducedCoreCounts
open G1DecoratedRootBlobRetention G1OriginalDecoratedSpan G1ContextualForestReplacement
open G1ActualDisplayedClusterSplitTransport G1FiniteNormalizationDisplayedTargets
open G1ActualDisplayedQuartetTransport
open G1AcceptedNontrivialSplitTarget G1AcceptedAllCompatibleCircularOrders
open G1ActualDisplayedTreeFamily G1ActualWholeUnrootedCutTreeFamily G1FiniteCoreWholeDisplayedTreeFamilies
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalOriginalExitAsyncStep
open G1CanonicalInitializedWholeCalendarHistory G1CanonicalWholeCalendarSameCompletion
open G1CanonicalOwnTwoInterfaceRuntime G1CanonicalPendingTrueKExposure G1AllOriginalPromotedKLabels
open G1EveryPromotedKInputRealCurrentRoot G1CanonicalOriginalKOnlyActorRow
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open G1PendingBaseCheckpointRecorder G1PendingInterfaceEntryRecorder G1OriginalWholeCausalView G1UnrankedSourceView
open G1ActiveCoreBridgeCohorts G1InitializedFrontierPrefix G1ActualOriginalRootRecordedProgram
open scoped Classical
universe u v w c h o
variable {X : Type w} [Fintype X]

theorem actual_one_same_outer_semidirected_core_source_assembly (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (hO : HasOuterSemidirectedPartner O) :
    ∃ (T : Source X) (D : Decoration O T) (hD : Originated O H D),
      HasOuterSemidirectedPartner T ∧ Steps O T ∧ Reduced T ∧ (hybrids T.network).card ≤ 2 * Fintype.card X - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card X - 5 ∧ Fintype.card T.Edge ≤ 8 * Fintype.card X - 8 ∧
      SamePhysicalTargets O T ∧ UniformCurrentRootInterface O T D ∧
      (∀ f : O.Edge, O.network.graph.SameBlob O.network.root (O.network.graph.source f) →
        O.network.graph.SameBlob O.network.root (O.network.graph.target f) → ∃ e : T.Edge, D.recipe e = .raw f) ∧
      (∀ (Copy : Type c) [Fintype Copy] [DecidableEq Copy]
        (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval)
        (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (history : List (UnrankedView O.Vertex O.Edge Copy)),
        SameCompletedOriginalHistory O H D hD sample register gamma common r history ∧
        ActualKInputs O H D hD sample register gamma common r history) := by
  obtain ⟨T,D,hD,properties⟩ := actual_one_same_original_core_source_assembly O H
  exact ⟨T,D,hD,actual_steps_preserve_outer_semidirected_partner properties.1 hO,properties⟩

#print axioms actual_one_same_outer_semidirected_core_source_assembly
end G1OneSameOuterSemidirectedCoreAssembly
