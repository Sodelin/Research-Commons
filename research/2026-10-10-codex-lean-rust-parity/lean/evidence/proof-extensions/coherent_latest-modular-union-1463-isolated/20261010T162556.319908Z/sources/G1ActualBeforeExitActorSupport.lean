import G1ActualOriginalBaseAsyncStep

/-! Real ORIGINAL states immediately before/partway through an exit batch
admit every still-unclosed actor region, including actors whose upper dates
coincide. This discharges the physical support gate for runtime closing. -/
namespace G1ActualBeforeExitActorSupport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1OriginalSpanClosingPhase G1OriginalSpanCalendarDecomposition
open G1CanonicalEpochSpecialization G1CanonicalComponentSegment G1InitializedFrontierPrefix G1CanonicalThreeEpochList
open G1OriginalCrossingCalendar G1OriginalEpochPanelCompression G1OriginalDescendantCohortAgenda G1ActiveCoreBridgeCohorts
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1PrivateActorLifetimeAdmission
open G1NaturalActiveActorFrontier G1SameOriginalExteriorContinuation
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

/-- Literal source-window split stops BEFORE any exit at the upper date. -/
lemma actual_before_boundary_window_append (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (a b : O.Vertex)
    (hab : O.calendar.age a < O.calendar.age b) :
    beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age b) =
      actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age a) ++
        (nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age a) ++
          stopBeforeTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
            (O.calendar.age b) (O.calendar.age a) (afterDate O.network O.calendar (O.calendar.age a))) := by
  apply List.append_cancel_right (bs := (G1OriginalCalendarDecomposition.originalExits O.network O.calendar (O.calendar.age b)).map
    (fun e => .boundary (.exit e)))
  simpa only [actualFrontierProgram,fullSpanAgenda,canonicalEpochBlock,G1OriginalCalendarDecomposition.originalExits,List.append_assoc] using
    actual_frontier_original_window_append O H gamma common a b hab

lemma actual_stop_tail_not_after_upper_safe (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (cut : O.Edge)
    (dates : List ℝ) (ordered : dates.Pairwise (· < ·)) (stop : ℝ) (hstop : stop ∈ dates)
    (hupper : stop ≤ O.calendar.age (O.network.graph.source cut)) (a : ℝ) :
    ∀ op ∈ stopBeforeTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) stop a dates,
      EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val) {cut} op := by
  induction dates generalizing a with
  | nil => exact False.elim (List.not_mem_nil hstop)
  | cons c cs ih =>
    have hp := List.pairwise_cons.mp ordered
    intro op hop
    by_cases hc : c = stop
    · have heq : op = .interval (Real.toNNReal (c-a)) := by simpa [stopBeforeTail,hc] using hop
      exact Or.inl ⟨_,heq⟩
    · have hm : stop ∈ cs := (List.mem_cons.mp hstop).resolve_left (Ne.symm hc)
      have hop : op = .interval (Real.toNNReal (c-a)) ∨
          op ∈ boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) c ++
            stopBeforeTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) stop c cs := by
        simpa [stopBeforeTail,hc] using hop
      rcases hop with heq | hop
      · exact Or.inl ⟨_,heq⟩
      · rcases List.mem_append.mp hop with hbatch | htail
        · apply actual_earlier_boundary_edge_safe O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
            {cut} _ c ((hp.1 _ hm).trans_le hupper) _ op hbatch
          intro e he
          have he : e = cut := Finset.mem_singleton.mp he
          subst e; rfl
        · exact ih hp.2 hm c op htail

/-- At a REAL original pre-exit state, all previously opened/unclosed actor
copies are inside their actual private regions. Upper endpoints may coincide
with this date; the actor has not been released before its own cut exit. -/
theorem actual_real_before_exits_actor_region (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) (node : O.Vertex)
    (hlo : O.calendar.age (actorInput O D actor) < O.calendar.age node)
    (hhi : O.calendar.age node ≤ O.calendar.age (D.vertex (T.network.graph.source actor.val)))
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support) :
    ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
      SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x) := by
  rw [actual_before_boundary_window_append O H gamma common _ node hlo,actual_source_program_append] at hs
  obtain ⟨a,ha,hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
  apply actual_safe_program_actor_region O H D hD actor gamma common r _ _ a _ _ hs
  · intro op hop
    rcases List.mem_append.mp hop with hn | ht
    · obtain ⟨v,hv,heq⟩ := List.mem_map.mp hn
      exact Or.inr (Or.inr ⟨v,heq.symm⟩)
    · apply actual_stop_tail_not_after_upper_safe O H gamma common _ _ (original_after_ordered _ _ _)
        _ (original_after_member _ _ _ node hlo) _ _ op ht
      rw [actual_actor_cut_source]
      exact hhi
  · intro x hx
    rw [actual_initialized_all_original_descendants_at_input O H D hD sample register gamma common r actor.val actor.property ha x hx]
    exact actual_span_input_in_region O _

/-- EVERY actual partial original exit batch preserves every not-yet-closed
actor region. Completed actors are promoted to base; only their literal cut
is allowed to leave the region. No distinct closing-date premise is used. -/
theorem actual_real_partial_exit_batch_actor_region (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) (node : O.Vertex)
    (hlo : O.calendar.age (actorInput O D actor) < O.calendar.age node)
    (hhi : O.calendar.age node ≤ O.calendar.age (D.vertex (T.network.graph.source actor.val)))
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (processed : List O.Edge) (hunclosed : actorCut O H D hD actor ∉ processed)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) s).support) :
    ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
      SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state d) x) := by
  apply actual_safe_program_actor_region O H D hD actor gamma common r _ _ s _
    (actual_real_before_exits_actor_region O H D hD actor node hlo hhi sample register gamma common r hs) hd
  intro op hop
  obtain ⟨e,he,heq⟩ := List.mem_map.mp hop
  refine Or.inr (Or.inl ⟨e,?_,heq.symm⟩)
  intro hc
  have heq : e = actorCut O H D hD actor := Finset.mem_singleton.mp hc
  exact hunclosed (heq ▸ he)

#print axioms actual_real_before_exits_actor_region
#print axioms actual_real_partial_exit_batch_actor_region
end G1ActualBeforeExitActorSupport
