import G1WholeOriginalActorBoundaryTensor
import G1ActualActorBoundaryFrames

/-! Actual private/base original boundary rows have the precise unranked
coordinate frame required for pending actor algebra. A private operation
changes only its own full original descendant cohort. No ordered equality. -/
namespace G1OriginalActorUnrankedBoundaryFrames
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1ActiveCoreBridgeCohorts G1OriginalActorOperationOwnership
open G1CanonicalActorLifecycleCompiler G1TaggedOriginalCalendar G1PrivateActorLifetimeAdmission
open G1ActualActorBoundaryFrames G1UnrankedSourceView G1ActualFiniteOriginalQuotientTensor
open G1UnrankedActualFuture
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_boundary_quotient_frame (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (op : BoundaryOperation O.network) (s : Code O.network sample) (keep : Finset Copy)
    (hframe : (boundaryKernel O.network op s).map (projection O.network keep) = PMF.pure (projection O.network keep s)) :
    (unrankedProgram O.network r keep [.boundary op] (G1UnrankedActualGenerator.unrankedProjection O.network keep s)).map Subtype.val =
      PMF.pure (unrankedView (selectedView (state s) keep)) := by
  rw [←actual_selected_panel_quotient_row,←actual_source_program_projection,PMF.map_comp]
  simp only [sourceProgram,sourceProgramStep,PMF.bind_pure]
  calc
    _ = ((boundaryKernel O.network op s).map (projection O.network keep)).map (fun v => unrankedView v.val) := by
      rw [PMF.map_comp]
    _ = _ := by rw [hframe,PMF.pure_map]; rfl

/-- Every actual private original boundary is identity on EVERY complete
original outside panel. Disjoint original cohorts provide its physical
outside condition, even with arbitrary already formed opaque subtrees. -/
theorem actual_owned_boundary_other_original_factor_pure (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (event : OriginalEvent O) (howner : eventActor O H D hD event = some actor)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (outside : Finset Copy)
    (hdis : Disjoint (originalInsideCopies O sample (actorInput O D actor)) outside) :
    (unrankedProgram O.network r outside [eraseEvent O H gamma common event]
      (G1UnrankedActualGenerator.unrankedProjection O.network outside s)).map Subtype.val =
        PMF.pure (unrankedView (selectedView (state s) outside)) := by
  have hout : ∀ x ∈ outside, ¬ O.network.graph.DReach (actorInput O D actor) (O.network.leaf (sample x)) := by
    intro x hx hd
    exact Finset.disjoint_left.mp hdis (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩) hx
  cases event with
  | interval _ _ => cases howner
  | node v =>
    apply actual_boundary_quotient_frame
    exact actual_owned_node_outside_row_silent O H D hD actor v (actual_owned_node_member O H D hD v actor howner)
      gamma common s outside hout
  | exit e =>
    apply actual_boundary_quotient_frame
    exact actual_owned_exit_outside_row_silent O H D hD actor e (actual_owned_exit_member O H D hD e actor howner)
      s outside hout

/-- The retained-base event factor is identity on every physically active
private actor coordinate. Its true base kernel still uses the SAME original
node/edge operation, including the entire original root blob. -/
theorem actual_base_boundary_actor_original_factor_pure (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (event : OriginalEvent O) (howner : eventActor O H D hD event = none)
    (hboundary : ∀ a b, event ≠ .interval a b)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (inside : Finset Copy)
    (hregion : ∀ x ∈ inside, SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x)) :
    (unrankedProgram O.network r inside [eraseEvent O H gamma common event]
      (G1UnrankedActualGenerator.unrankedProjection O.network inside s)).map Subtype.val =
        PMF.pure (unrankedView (selectedView (state s) inside)) := by
  cases event with
  | interval a b => exact False.elim (hboundary a b rfl)
  | node v =>
    apply actual_boundary_quotient_frame
    exact actual_unowned_node_actor_row_silent O H D hD v howner actor gamma common s inside hregion
  | exit e =>
    have hn : ¬ T.network.graph.IsBridge (populationOwner O H D hD e) := by
      intro hb
      simp only [eventActor,dif_pos hb] at howner
      cases howner
    apply actual_boundary_quotient_frame
    exact actual_base_exit_actor_row_silent O H D hD e hn actor s inside hregion

#print axioms actual_owned_boundary_other_original_factor_pure
#print axioms actual_base_boundary_actor_original_factor_pure
end G1OriginalActorUnrankedBoundaryFrames
