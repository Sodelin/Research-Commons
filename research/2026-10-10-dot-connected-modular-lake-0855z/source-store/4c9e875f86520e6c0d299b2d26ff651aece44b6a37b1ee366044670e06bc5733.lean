import G1CanonicalBatchOpeningCalendar

/-! At ANY real original date frontier, every currently active core bridge's
full original descendant cohort lies in its derived private original region.
This admits arbitrary-many concurrent actors, without supplied region support
or descendant-copy caps. -/
namespace G1NaturalActiveActorFrontier
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanRegion G1OriginatedNeutralSpanRegion
open G1OriginalSpanClosingPhase G1SpanRegionOriginalOperations G1OriginalEpochPanelCompression
open G1OriginalSpanCalendarDecomposition G1CanonicalEpochSpecialization G1CanonicalComponentSegment
open G1SameOriginalExteriorContinuation G1CanonicalThreeEpochList G1ActualJointProgram G1InitializedFrontierPrefix G1OriginalCrossingCalendar G1ActiveCoreBridgeCohorts
open G1OriginalDescendantCohortAgenda G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler
open G1PrivateActorLifetimeAdmission
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_stop_tail_before_upper_safe (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (cut : O.Edge)
    (dates : List ℝ) (ordered : dates.Pairwise (· < ·)) (stop : ℝ) (hstop : stop ∈ dates)
    (hupper : stop < O.calendar.age (O.network.graph.source cut)) (a : ℝ) :
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
            {cut} _ c ((hp.1 _ hm).trans hupper) _ op hbatch
          intro e he
          have he : e = cut := Finset.mem_singleton.mp he
          subst e; rfl
        · exact ih hp.2 hm c op htail

lemma actual_full_span_before_cut_safe (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (a stop : O.Vertex) (cut : O.Edge)
    (hstart : O.calendar.age a < O.calendar.age stop)
    (hupper : O.calendar.age stop < O.calendar.age (O.network.graph.source cut)) :
    ∀ op ∈ fullSpanAgenda O.network O.calendar H gamma common a stop,
      EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val) {cut} op := by
  intro op hop
  rcases List.mem_append.mp hop with hleft | hexit
  · rcases List.mem_append.mp hleft with hnode | htail
    · obtain ⟨v,hv,he⟩ := List.mem_map.mp hnode
      exact Or.inr (Or.inr ⟨v,he.symm⟩)
    · exact actual_stop_tail_before_upper_safe O H gamma common cut _ (original_after_ordered _ _ _)
        _ (original_after_member _ _ _ stop hstart) hupper _ op htail
  · obtain ⟨e,he,heq⟩ := List.mem_map.mp hexit
    have he := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
    have hn : e ∉ ({cut} : Finset O.Edge) := by
      intro hmem
      have hc : e = cut := Finset.mem_singleton.mp hmem
      rw [hc] at he
      exact (ne_of_lt hupper) he.symm
    exact Or.inr (Or.inl ⟨e,hn,heq.symm⟩)

lemma actual_safe_program_actor_region (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (ops : List (ProgramStep O.network))
    (safe : ∀ op ∈ ops, EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val)
      {actorCut O H D hD actor} op) (s : Code O.network sample) (inside : Finset Copy)
    (hin : ∀ x ∈ inside, SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x))
    {d : Code O.network sample} (hd : d ∈ (sourceProgram O.network r ops s).support) :
    ∀ x ∈ inside, SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state d) x) := by
  induction ops generalizing s with
  | nil => have heq : d = s := by simpa [sourceProgram] using hd
           subst d; exact hin
  | cons op ops ih =>
    obtain ⟨z,hz,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    exact ih (fun q hq => safe q (List.mem_cons_of_mem op hq)) z
      (actual_span_safe_step_support O _ _ (actual_actor_cut_ends_at O H D hD actor) H gamma common r op
        (safe op (List.mem_cons_self)) s inside hin hz) hd

/-- Actual initialized support, original calendar splitting and region closure
admit ALL simultaneously active core actors at every original before-node
frontier. This is stronger than the earlier two strict-crossing admission. -/
theorem actual_real_frontier_active_actor_region (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) (node : O.Vertex)
    (ha : T.calendar.Active (O.calendar.age node) actor.val)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support) :
    ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
      SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x) := by
  have hbounds : O.calendar.age (actorInput O D actor) ≤ O.calendar.age node ∧
      O.calendar.age node < O.calendar.age (D.vertex (T.network.graph.source actor.val)) := by
    simpa only [Calendar.Active,D.calendar,actorInput] using ha
  by_cases heq : O.calendar.age (actorInput O D actor) = O.calendar.age node
  · have hsA : s ∈ (sourceProgram O.network r
        (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
          (O.calendar.age (actorInput O D actor))) (initialCode O.network sample register)).support := by
      rw [heq]; exact hs
    intro x hx
    rw [actual_initialized_all_original_descendants_at_input O H D hD sample register gamma common r
      actor.val actor.property hsA x hx]
    exact actual_span_input_in_region O _
  · have hlt : O.calendar.age (actorInput O D actor) < O.calendar.age node := lt_of_le_of_ne hbounds.1 heq
    rw [actual_frontier_original_window_append O H gamma common (actorInput O D actor) node hlt,
      actual_source_program_append] at hs
    obtain ⟨a,ha,hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    have hin : ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
        SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state a) x) := by
      intro x hx
      rw [actual_initialized_all_original_descendants_at_input O H D hD sample register gamma common r
        actor.val actor.property ha x hx]
      exact actual_span_input_in_region O _
    have hupper : O.calendar.age node < O.calendar.age (O.network.graph.source (actorCut O H D hD actor)) := by
      rw [actual_actor_cut_source]; exact hbounds.2
    exact actual_safe_program_actor_region O H D hD actor gamma common r _
      (actual_full_span_before_cut_safe O H gamma common _ node _ hlt hupper) a _ hin hs

#print axioms actual_real_frontier_active_actor_region
end G1NaturalActiveActorFrontier
