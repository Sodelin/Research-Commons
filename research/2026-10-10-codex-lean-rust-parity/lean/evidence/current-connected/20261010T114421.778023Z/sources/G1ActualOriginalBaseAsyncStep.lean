import G1ActualOriginalPrivateAsyncStep

/-! The ACTUAL retained-base boundary is a genuine exterior step of the
pending actor algebra. Every private original coordinate is a derived
identity on real support; the base uses its true original unranked row. -/
namespace G1ActualOriginalBaseAsyncStep
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceForestSilentPruning
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1TaggedOriginalCalendar
open G1OriginalActorUnrankedBoundaryFrames G1UnrankedSourceView G1UnrankedActualGenerator G1UnrankedActualFuture
open G1ActualOriginalUnrankedLocalKernel G1ActualOriginalPrivateAsyncStep G1PendingActorInterfaceCommutation
open G1ContextualForestReplacement
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_base_boundary_actor_panel_support (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (event : OriginalEvent O) (howner : eventActor O H D hD event = none)
    (hboundary : ∀ a b, event ≠ .interval a b)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (keep : Finset Copy)
    (hregion : ∀ x ∈ keep, SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x))
    {d : Code O.network sample} (hd : d ∈ (sourceProgram O.network r [eraseEvent O H gamma common event] s).support) :
    unrankedView (selectedView (state d) keep) = unrankedView (selectedView (state s) keep) := by
  have hframe := actual_base_boundary_actor_original_factor_pure O H D hD actor event howner hboundary gamma common r s keep hregion
  have hm : unrankedView (selectedView (state d) keep) ∈
      ((sourceProgram O.network r [eraseEvent O H gamma common event] s).map
        (fun z => unrankedView (selectedView (state z) keep))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨d,hd,rfl⟩
  have hrow := congrArg (fun p => p.map Subtype.val)
    (actual_unranked_source_program O.network r keep [eraseEvent O H gamma common event] s)
  rw [PMF.map_comp] at hrow
  change ((sourceProgram O.network r [eraseEvent O H gamma common event] s).map
      (fun z => unrankedView (selectedView (state z) keep))) = _ at hrow
  rw [hrow,hframe] at hm
  exact (PMF.mem_support_pure_iff _ _).mp hm

/-- Actual source-to-AsyncOperation exterior binding for every original
retained-base boundary, including original root-blob/common/root operations.
All private slot frames are derived from their actual physical regions. -/
theorem actual_original_base_boundary_async_step (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (event : OriginalEvent O) (howner : eventActor O H D hD event = none)
    (hboundary : ∀ a b, event ≠ .interval a b)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample)
    (base : Finset Copy) (slots : BridgeActor T → Finset Copy)
    (hregions : ∀ actor, ∀ x ∈ slots actor,
      SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x)) :
    (sourceProgram O.network r [eraseEvent O H gamma common event] s).map (originalAsyncProjection O base slots) =
      asyncStep (.exterior (originalLocalRow O.network sample r base [eraseEvent O H gamma common event]))
        (originalAsyncProjection O base slots s) := by
  let initial := originalAsyncProjection O base slots s
  calc
    _ = (sourceProgram O.network r [eraseEvent O H gamma common event] s).map (fun d =>
        (unrankedView (selectedView (state d) base),initial.2)) := by
      apply map_eq_of_eq_on_support
      intro d hd
      apply Prod.ext
      · rfl
      · funext actor
        exact actual_base_boundary_actor_panel_support O H D hD actor event howner hboundary gamma common r s _ (hregions actor) hd
    _ = ((sourceProgram O.network r [eraseEvent O H gamma common event] s).map
        (fun d => unrankedView (selectedView (state d) base))).map (fun value => (value,initial.2)) := by
      rw [PMF.map_comp]; rfl
    _ = _ := by rw [actual_original_local_source_row]; rfl

#print axioms actual_original_base_boundary_async_step
end G1ActualOriginalBaseAsyncStep
