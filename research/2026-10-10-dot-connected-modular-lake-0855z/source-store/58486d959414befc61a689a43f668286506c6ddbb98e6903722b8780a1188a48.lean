import G1ActualBeforeExitActorSupport

/-! Actual canonical closing-port support. At the original upper exit batch,
ALL original actor descendants are on its unique literal last cut. Other
same-date exits cannot disturb that panel; the actual cut delivers every
opaque original descendant subtree to its one original retained upper node. -/
namespace G1ActualCanonicalFinalCutPort
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarPhysicalSupport UnifiedLean.Source.SourceCalendarCompatibility
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1SpanRegionExitClosure G1OriginalActorTemporalFootprint
open G1OriginalSpanCalendarDecomposition G1InitializedFrontierPrefix G1ActiveCoreBridgeCohorts
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1PrivateActorLifetimeAdmission
open G1ActualBeforeExitActorSupport
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- Readiness at the actual original closing date and the literal private
region force its unique last original population. No exit-population premise
is provided by the source/application caller. -/
theorem actual_real_closing_before_exits_at_cut (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.source actor.val)))) (initialCode O.network sample register)).support) :
    ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
      copyLocation (state s) x = .edge (actorCut O H D hD actor) := by
  let upper := D.vertex (T.network.graph.source actor.val)
  have hreg := actual_real_before_exits_actor_region O H D hD actor upper
    (actual_span_dates_strict O.network O.calendar (bridgeSpan O T D actor.val actor.property)) le_rfl
    sample register gamma common r hs
  have hready := (actual_initialized_before_boundary_support O.network O.calendar sample register H
    (fun h => gamma h.val) (fun h => common h.val) r (O.calendar.age upper)
    (original_date_scheduled O.network O.calendar upper) hs).1
  intro x hx
  have hr := hreg x hx
  have hp := hready x
  cases he : copyLocation (state s) x with
  | rootPopulation v => rw [he] at hr; exact False.elim hr
  | node v =>
    rw [he] at hr hp
    have hlt := (actual_span_node_temporal_bounds O _ v hr).2
    exact False.elim ((not_le_of_gt hlt) hp)
  | edge e =>
    rw [he] at hr hp
    have hle := actual_span_edge_source_age O (bridgeSpan O T D actor.val actor.property) e hr
    have ha : O.calendar.age (O.network.graph.source e) = O.calendar.age upper := le_antisymm hle hp.2
    have hc := actual_only_last_exit_at_end_date O _ _ (actual_actor_cut_ends_at O H D hD actor) e hr ha
    exact congrArg Location.edge hc

lemma actual_other_exit_list_preserves_cut_panel (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (keep : Finset Copy) (cut : O.Edge) (processed : List O.Edge)
    (hunclosed : cut ∉ processed) (s : Code O.network sample)
    (hin : ∀ x ∈ keep, copyLocation (state s) x = .edge cut)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) s).support) :
    ∀ x ∈ keep, copyLocation (state d) x = .edge cut := by
  induction processed generalizing s with
  | nil => have he : d = s := by simpa [sourceProgram] using hd
           subst d; exact hin
  | cons e es ih =>
    have hne : e ≠ cut := by intro h; exact hunclosed (h ▸ List.mem_cons_self)
    have hd' : d ∈ (sourceProgram O.network r (es.map (fun e => .boundary (.exit e))) (exitCode O.network s e)).support := by
      simpa [sourceProgram,sourceProgramStep,boundaryKernel] using hd
    apply ih (fun hm => hunclosed (List.mem_cons_of_mem e hm)) (exitCode O.network s e) _ hd'
    intro x hx
    rw [exitCode_copyLocation,hin x hx]
    simp [exitLocation,hne.symm]

/-- All other same-date original exits remain literal and cannot prematurely
release this actor. The exact single port is derived on every such support. -/
theorem actual_real_partial_closing_batch_at_cut (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.source actor.val)))) (initialCode O.network sample register)).support)
    (processed : List O.Edge) (hunclosed : actorCut O H D hD actor ∉ processed)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) s).support) :
    ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
      copyLocation (state d) x = .edge (actorCut O H D hD actor) :=
  actual_other_exit_list_preserves_cut_panel O r _ _ processed hunclosed s
    (actual_real_closing_before_exits_at_cut O H D hD actor sample register gamma common r hs) hd

/-- Actual last cut delivery, including a root-blob upper population. Closing
must promote this output into base BEFORE that original post-cut observation. -/
theorem actual_canonical_final_cut_single_original_exit (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (keep : Finset Copy)
    (hin : ∀ x ∈ keep, copyLocation (state s) x = .edge (actorCut O H D hD actor))
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r [.boundary (.exit (actorCut O H D hD actor))] s).support) :
    ∀ x ∈ keep, copyLocation (state d) x = .node (D.vertex (T.network.graph.source actor.val)) := by
  have he : d = exitCode O.network s (actorCut O H D hD actor) := by
    simpa [sourceProgram,sourceProgramStep,boundaryKernel] using hd
  subst d
  intro x hx
  rw [exitCode_copyLocation,hin x hx]
  simp [exitLocation,actual_actor_cut_source]

#print axioms actual_real_partial_closing_batch_at_cut
#print axioms actual_canonical_final_cut_single_original_exit
end G1ActualCanonicalFinalCutPort
