import G1ActualOriginalOpenCloseAsyncInterface

/-! Canonical last-cut source support derives close-interface forest purity.
Rootward delivered output is promoted into base immediately after the actual
cut, before its original checkpoint. No post-cut separation is assumed. -/
namespace G1ActualFinalCutCloseAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1OriginatedNeutralSpanRegion G1DerivedSpanSeparatedAgenda G1JointUnrankedForestAssembly
open G1JointForestPreservation G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler
open G1ActiveCoreBridgeCohorts G1ActualCanonicalFinalCutPort
open G1ActualOriginalPrivateAsyncStep G1ActualOriginalOpenCloseAsyncInterface G1PendingActorInterfaceCommutation
open G1UnrankedSourceView G1InitializedFrontierPrefix
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- Actual pre-cut one-port support and the constructed outside footprint
DERIVE the close fibre condition on every actual cut output. The delivered
roots may share base populations; the cut cannot merge their forests. -/
theorem actual_last_cut_close_purity (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (base : Finset Copy)
    (hbase : Disjoint (originalInsideCopies O sample (actorInput O D actor)) base)
    (hin : ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
      copyLocation (state s) x = .edge (actorCut O H D hD actor))
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r [.boundary (.exit (actorCut O H D hD actor))] s).support) :
    PrunedPanelSeparated (state d) (originalInsideCopies O sample (actorInput O D actor)) base := by
  have hsep := actual_neutral_span_population_separator O (bridgeSpan O T D actor.val actor.property)
    (actual_originated_bridge_region_neutral O H D hD actor.val actor.property) s
    (originalInsideCopies O sample (actorInput O D actor)) base
    (fun x hx => hin x hx ▸ actual_actor_cut_in_region O H D hD actor)
    (fun x hx hd => Finset.disjoint_left.mp hbase (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩) hx)
  apply actual_boundary_pruned_panel_separation O.network (.exit (actorCut O H D hD actor)) s _ base
    (population_separated_pruned_panels (state s) s.property.forest _ base hsep)
  simpa [sourceProgram,sourceProgramStep] using hd

/-- At ANY real original partial closing batch, the K-only actor close is
source-admitted without a supplied purity/single-exit/output equality field.
It releases every original opaque descendant subtree before root recording. -/
theorem actual_canonical_final_cut_close_async_interface (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {initial : Code O.network sample}
    (hs : initial ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.source actor.val)))) (initialCode O.network sample register)).support)
    (processed : List O.Edge) (hunclosed : actorCut O H D hD actor ∉ processed)
    {s : Code O.network sample}
    (hp : s ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) initial).support)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r [.boundary (.exit (actorCut O H D hD actor))] s).support)
    (base : Finset Copy) (slots : BridgeActor T → Finset Copy)
    (hbase : Disjoint (originalInsideCopies O sample (actorInput O D actor)) base)
    (hslot : slots actor = originalInsideCopies O sample (actorInput O D actor)) :
    PMF.pure (originalAsyncProjection O
      (originalInsideCopies O sample (actorInput O D actor) ∪ base) (Function.update slots actor ∅) d) =
      asyncStep (.interface actor (originalCloseKernel (originalInsideCopies O sample (actorInput O D actor))))
        (originalAsyncProjection O base slots d) := by
  have hin := actual_real_partial_closing_batch_at_cut O H D hD actor sample register gamma common r hs processed hunclosed hp
  exact actual_original_close_async_interface O d actor _ base slots hslot
    (actual_last_cut_close_purity O H D hD actor r s base hbase hin hd)

#print axioms actual_canonical_final_cut_close_async_interface
end G1ActualFinalCutCloseAdmission
