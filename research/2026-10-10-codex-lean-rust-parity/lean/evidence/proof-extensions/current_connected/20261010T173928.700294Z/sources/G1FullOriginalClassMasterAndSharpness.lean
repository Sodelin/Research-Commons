import G1ExactOriginalClassAllNSharpness

/-! The precise original G1 headline in ONE statement: uniform source-derived
current-root contextual UNRANKED kernel normalization on the original finite
binary LSA/CutChild/outer-labelled GALLED semidirected parallel-arc class,
with SAME original whole root blob/register/calendar history/completion and
literal complete displayed-tree/Q/S/all-compatible-order preservation.
The core census is h≤2n−2,V≤6n−5,E≤8n−8; ALL three bounds are attained by
actual admitted reduced positive/interior sources for EVERY n≥4.
No ordinary-network inverse witness bound, empirical admission, ranked merge
time experiment, or ancestral jump-trajectory equality is asserted. -/
namespace G1FullOriginalClassMasterAndSharpness
set_option backward.isDefEq.respectTransparency false
open G1OriginalClassSameCoreAssembly G1ExactOriginalClassAllNSharpness
open G1OneSameOriginalCoreAssembly G1OneSameOuterSemidirectedCoreAssembly
open G1SameCoreLiteralSemidirectedTargets G1ExactSemidirectedPartnerAdmission
open UnifiedLean.Source.NativeIndependentPairMixture
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

theorem actual_G1_original_class_master_with_all_n_sharpness :
    (∀ (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (_hn : 4 ≤ Fintype.card X) (hO : HasGalledOuterSemidirectedPartner O),
    ∃ (T : Source X) (D : Decoration O T) (hD : Originated O H D),
      HasGalledOuterSemidirectedPartner T ∧ Steps O T ∧ Reduced T ∧ (hybrids T.network).card ≤ 2 * Fintype.card X - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card X - 5 ∧ Fintype.card T.Edge ≤ 8 * Fintype.card X - 8 ∧
      SameLiteralSemidirectedTargets O T ∧ SamePhysicalTargets O T ∧ UniformCurrentRootInterface O T D ∧
      (∀ f : O.Edge, O.network.graph.SameBlob O.network.root (O.network.graph.source f) →
        O.network.graph.SameBlob O.network.root (O.network.graph.target f) → ∃ e : T.Edge, D.recipe e = .raw f) ∧
      (∀ (Copy : Type c) [Fintype Copy] [DecidableEq Copy]
        (sample : Copy → X) (register : O.Vertex → Bool) (p : HybridProbabilities O.network)
        (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (history : List (UnrankedView O.Vertex O.Edge Copy)),
        SameCompletedOriginalHistory O H D hD sample register (naturalInteriorGamma O.network p) common r history ∧
        ActualKInputs O H D hD sample register (naturalInteriorGamma O.network p) common r history)) ∧
    (∀ (n : ℕ) (hn : 4 ≤ n),
    ∃ S : Source.{0,0,0} (Fin n), Reduced S ∧ HasGalledOuterSemidirectedPartner S ∧
      Nonempty (PositivePairRates S.Edge) ∧ Nonempty (HybridProbabilities S.network) ∧
      (hybrids S.network).card = 2*n-2 ∧ Fintype.card S.Vertex = 6*n-5 ∧
      Fintype.card S.Edge = 8*n-8 ∧ (∀ x : Fin n, S.calendar.age (S.network.leaf x) = 0)) := by
  exact ⟨fun O H hn hO => actual_one_same_original_class_G1_assembly O H hn hO,
    every_n_has_exact_original_class_saturating_source⟩

#print axioms actual_G1_original_class_master_with_all_n_sharpness
end G1FullOriginalClassMasterAndSharpness
