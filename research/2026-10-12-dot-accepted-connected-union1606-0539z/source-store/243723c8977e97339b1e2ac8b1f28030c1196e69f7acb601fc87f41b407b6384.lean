import G1EveryPromotedKInputRealCurrentRoot
import G1FiniteCoreWholeDisplayedTreeFamilies
import G1AcceptedAllCompatibleCircularOrders
import G1DecoratedRootBlobRetention

/-! ONE constructed original-provenance core simultaneously carries the
accepted physical targets, uniform arbitrary opaque current-root interface,
and the actual all-actor SAME-original-source completed root-history law.
The current Source bundles raw binary/LSA/CutChild/calendar admission; generic
outer-planar partner/embedding transport is a distinct final class gate. -/
namespace G1OneSameOriginalCoreAssembly
set_option backward.isDefEq.respectTransparency false
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

def SamePhysicalTargets (O T : Source.{u,v,w} X) : Prop :=
  (∀ panel : Finset X,
    actualDisplayedClusters T.network panel = actualDisplayedClusters O.network panel ∧
    acceptedDisplayedSplits T.network panel = acceptedDisplayedSplits O.network panel ∧
    actualDisplayedRootedTrees T.network T.calendar panel = actualDisplayedRootedTrees O.network O.calendar panel ∧
    actualDisplayedUnrootedCutTreeFamily T.network T.calendar panel = actualDisplayedUnrootedCutTreeFamily O.network O.calendar panel) ∧
  (∀ q : Fin 4 ↪ X, normalizedDisplayedCutQuartets T.network q = normalizedDisplayedCutQuartets O.network q) ∧
  sourceCompatibleOrders T.network = sourceCompatibleOrders O.network

def ActualKInputs (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type c} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (history : List (UnrankedView O.Vertex O.Edge Copy)) : Prop :=
  ∀ actor : BridgeActor T, ∃ before gap later opening,
    (ownRuntimeParts O H D hD sample gamma common r actor).opening = AsyncOperation.interface actor opening ∧
    promoteEveryActor (Finset.univ.toList) (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r) =
      before ++ .interface actor opening ::
        (gap ++ .localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor) :: later) ∧
    ∀ input : ((UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) ×
        List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy)) × (BridgeActor T → UnrankedView O.Vertex O.Edge Copy),
      input ∈ (asyncProgram ((before ++ [AsyncOperation.interface actor opening] ++ gap).map interfaceRecordingLift)
        (withEntryRecords [] (withBaseHistory history
          (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
            (initialCode O.network sample register))))).support →
      ∃ s : Code O.network sample,
        s ∈ (sourceProgram O.network r
          (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
            (O.calendar.age (actorInput O D actor))) (initialCode O.network sample register)).support ∧
        input.2 actor = unrankedView (selectedView (state s) (originalInsideCopies O sample (actorInput O D actor))) ∧
        canonicalPendingKRow O H D hD sample gamma common r actor (input.2 actor) =
          canonicalOriginalKActorRow O D gamma common r actor.val actor.property s

def SameCompletedOriginalHistory (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type c} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (history : List (UnrankedView O.Vertex O.Edge Copy)) : Prop :=
  (originalRootRecordedProgram O r
    (compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val))
    (initialCode O.network sample register) history).bind
    (fun result => (completionKernel O.network r result.1).map (fun final => (wholeOriginalView O.network final,result.2))) =
  (asyncProgram (promoteEveryActor (Finset.univ.toList)
    (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r))
    (withBaseHistory history (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
      (initialCode O.network sample register)))).bind
    (fun out => canonicalCompletedBaseHistory O r (initialCode O.network sample register) out.1)

/-- Uniform component interface on arbitrary ALREADY FORMED opaque forests.
Its cap is the initialized CURRENT live roots of the one entering panel,
never the number of original descendant leaves. Same history/register and
an arbitrary exterior continuation are retained through the real K graft. -/
def UniformCurrentRootInterface (O T : Source.{u,v,w} X) (D : Decoration O T) : Prop :=
  ∀ (Copy : Type c) [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (r : PositivePairRates O.Edge) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (e : T.Edge) (he : T.network.graph.IsBridge e) (s : Code O.network sample)
    (hs : ∀ l ∈ (state s).live, (state s).location l = .node (D.vertex (T.network.graph.target e)))
    (m : ℕ) (cap : (state s).live.card ≤ m) (History : Type h) (Obs : Type o) (history : History)
    (exterior : History × (O.Vertex → Bool) × Finset (UnrankedTree Copy) → PMF Obs),
    Fintype.card (SelectedCopy (state s).live) ≤ m ∧
    (∀ d ∈ (sourceProgram O.network r (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he)) s).support,
      ∀ l ∈ (state d).live, (state d).location l = .node (D.vertex (T.network.graph.source e))) ∧
    (sourceProgram O.network r (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he)) s).bind
      (fun d => exterior (history,(state d).register,rootForest O.network d)) =
    (originalSpanK O.network O.calendar r gamma common (bridgeSpan O T D e he) s hs).bind
      (fun F => exterior (history,(state s).register,
        F.image (G1OpaqueSourceGrafting.graftUnranked (fun l => (state s).genealogy l.val))))

/-- This single original-provenance witness supplies ALL physical targets
and the genuine completed all-actor source execution. It does not select
different existential cores for different observables. -/
theorem actual_one_same_original_core_source_assembly (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network) :
    ∃ (T : Source X) (D : Decoration O T) (hD : Originated O H D),
      Steps O T ∧ Reduced T ∧ (hybrids T.network).card ≤ 2 * Fintype.card X - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card X - 5 ∧ Fintype.card T.Edge ≤ 8 * Fintype.card X - 8 ∧
      SamePhysicalTargets O T ∧ UniformCurrentRootInterface O T D ∧
      (∀ f : O.Edge, O.network.graph.SameBlob O.network.root (O.network.graph.source f) →
        O.network.graph.SameBlob O.network.root (O.network.graph.target f) → ∃ e : T.Edge, D.recipe e = .raw f) ∧
      (∀ (Copy : Type c) [Fintype Copy] [DecidableEq Copy]
        (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval)
        (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (history : List (UnrankedView O.Vertex O.Edge Copy)),
        SameCompletedOriginalHistory O H D hD sample register gamma common r history ∧
        ActualKInputs O H D hD sample register gamma common r history) := by
  obtain ⟨T,D,steps,origin,reduced,hh,hv,he⟩ := actual_finite_original_decorated_core O H
  refine ⟨T,D,origin,steps,reduced,hh,hv,he,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,actual_steps_preserve_every_compatible_circle steps⟩
    · intro panel
      have htargets := actual_steps_displayed_targets steps panel
      have htrees := actual_steps_whole_displayed_tree_families steps panel
      exact ⟨htargets.1,actual_steps_preserve_accepted_S steps panel,htrees.1,htrees.2⟩
    · intro q
      exact (actual_steps_displayed_targets steps (Finset.univ : Finset X)).2.2 q
  · intro Copy _ _ sample r gamma common e he s hs m cap History Obs history exterior
    exact actual_decorated_bridge_cap_context O T D r gamma common e he s hs m cap history exterior
  · intro f hs ht
    exact actual_original_root_blob_raw_edges_survive O H D origin f hs ht
  · intro Copy _ _ sample register gamma common r history
    exact ⟨actual_promoted_whole_original_same_completed_history O H D origin sample register gamma common r history,
      fun actor => actual_every_promoted_K_input_is_real_current_root O H D origin sample register gamma common r actor history⟩

#print axioms actual_one_same_original_core_source_assembly
end G1OneSameOriginalCoreAssembly
