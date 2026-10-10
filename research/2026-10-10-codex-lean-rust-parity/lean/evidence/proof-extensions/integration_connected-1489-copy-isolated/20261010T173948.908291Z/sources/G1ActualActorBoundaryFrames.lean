import G1RootBlobRetainedBaseOwnership

/-! Actual ORIGINAL node/exit kernels obey the derived actor/base footprints.
All untouched complete labelled forest/population/SAME-register rows are
identity PMFs, not merely scalar/count invariance. -/
namespace G1ActualActorBoundaryFrames
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanRegion G1OriginatedNeutralSpanRegion
open G1SpanRegionOriginalOperations G1OriginalNodeBatchBinding G1ExteriorBoundarySilence
open G1OriginalActorOperationOwnership G1OriginalRecipePopulationOwnership G1ConstructedPopulationPartition
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- An original source-valid outside copy cannot occupy any original private
actor location. Arbitrary already-formed old subtrees are retained. -/
lemma actual_outside_actor_location_excluded (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (x : Copy)
    (hout : ¬ O.network.graph.DReach (D.vertex (T.network.graph.target actor.val)) (O.network.leaf (sample x))) :
    ¬ SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x) := by
  intro hp
  exact hout (actual_neutral_span_location_descends O _
    (actual_originated_bridge_region_neutral O H D hD actor.val actor.property) _ (sample x) hp
    (s.property.original_descendant x))

theorem actual_owned_node_outside_row_silent (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (node : O.Vertex)
    (hn : node ∈ nodeRegion O (bridgeSpan O T D actor.val actor.property))
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (outside : Finset Copy)
    (hout : ∀ x ∈ outside, ¬ O.network.graph.DReach (D.vertex (T.network.graph.target actor.val))
      (O.network.leaf (sample x))) :
    (boundaryKernel O.network (originalNodeOperation O.network H (fun h => gamma h.val) (fun h => common h.val) node) s).map
      (projection O.network outside) = PMF.pure (projection O.network outside s) := by
  apply actual_untouched_boundary_law
  intro x hx hpop
  rw [actual_node_touched_site] at hpop
  have hr : SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x) := hpop ▸ hn
  exact actual_outside_actor_location_excluded O H D hD actor s x (hout x hx) hr

theorem actual_owned_exit_outside_row_silent (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (population : O.Edge)
    (hp : population ∈ edgeRegion O (bridgeSpan O T D actor.val actor.property))
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (outside : Finset Copy)
    (hout : ∀ x ∈ outside, ¬ O.network.graph.DReach (D.vertex (T.network.graph.target actor.val))
      (O.network.leaf (sample x))) :
    (boundaryKernel O.network (.exit population) s).map (projection O.network outside) =
      PMF.pure (projection O.network outside s) := by
  apply actual_untouched_boundary_law
  intro x hx hpop
  change copyLocation (state s) x = .edge population at hpop
  have hr : SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x) := hpop ▸ hp
  exact actual_outside_actor_location_excluded O H D hD actor s x (hout x hx) hr

/-- A retained-base original node cannot read any private active actor
coordinate. This is the actual row-level source frame used by pending fusion. -/
theorem actual_unowned_node_actor_row_silent (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (node : O.Vertex) (hn : nodeActorOwner O H D hD node = none) (actor : BridgeActor T)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (inside : Finset Copy)
    (hin : ∀ x ∈ inside, SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x)) :
    (boundaryKernel O.network (originalNodeOperation O.network H (fun h => gamma h.val) (fun h => common h.val) node) s).map
      (projection O.network inside) = PMF.pure (projection O.network inside s) := by
  apply actual_untouched_boundary_law
  intro x hx hpop
  rw [actual_node_touched_site] at hpop
  have hm : node ∈ nodeRegion O (bridgeSpan O T D actor.val actor.property) := by
    have h := hin x hx
    rw [hpop] at h
    exact h
  rw [actual_node_actor_owner_of_member O H D hD node actor hm] at hn
  cases hn

/-- A retained-base original edge exit likewise cannot change any actor
forest. Unique original population ownership supplies the separation. -/
theorem actual_base_exit_actor_row_silent (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (population : O.Edge) (hb : ¬ T.network.graph.IsBridge (populationOwner O H D hD population))
    (actor : BridgeActor T) {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (inside : Finset Copy)
    (hin : ∀ x ∈ inside, SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x)) :
    (boundaryKernel O.network (.exit population) s).map (projection O.network inside) =
      PMF.pure (projection O.network inside s) := by
  apply actual_untouched_boundary_law
  intro x hx hpop
  change copyLocation (state s) x = .edge population at hpop
  have hm : population ∈ edgeRegion O (bridgeSpan O T D actor.val actor.property) := by
    have h := hin x hx
    rw [hpop] at h
    exact h
  rw [actual_bridge_span_populations] at hm
  have ho := actual_population_owner_unique O H D hD population actor.val hm
  exact hb (ho ▸ actor.property)

#print axioms actual_owned_node_outside_row_silent
#print axioms actual_unowned_node_actor_row_silent
#print axioms actual_base_exit_actor_row_silent
end G1ActualActorBoundaryFrames
