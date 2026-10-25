import G1KOnlyActorSameCompletedFuture

/-! Source-derived K-only actor close on EVERY real original frontier,
retaining the entire original exterior checkpoint path through SAME original
future and actual completion. No single-exit/root/desired-kernel premise. -/
namespace G1CanonicalKActorCompletedHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanClosingPhase G1OriginatedClosingSourceAdmission
open G1OriginalClosingCalendarBinding G1ActualEnteringFrontier G1InitializedFrontierPrefix
open G1OriginalExteriorCohort G1CanonicalOriginatedMacroPlans
open G1OriginalOpaqueExteriorView G1OriginalExteriorHistoryProduct G1UnrankedSourceView
open G1ActualJointEpoch G1ActualJointStageHistory G1ActualKProductInsertion
open G1CanonicalOriginalKOnlyActorRow G1CanonicalKActorExteriorHistory
open G1OriginalWholeCausalView G1SourceMacroActualCompletion G1OriginalKActorWholeViewAssembly
open G1KOnlyActorSameCompletedFuture
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalKActorCompletedHistoryRow (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X} {Obs : Type*}
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (e : T.Edge) (he : T.network.graph.IsBridge e) (initial : Code O.network sample)
    (readout : UnrankedView O.Vertex O.Edge Copy → Obs) :=
  let a := D.vertex (T.network.graph.target e)
  let b := D.vertex (T.network.graph.source e)
  let inside := enteringRoots O.network initial a
  let phase := closingSpanAgenda O H gamma common a b (originatedLastCut O H D hD e he)
  let future := originalClosingFuture O H gamma common (originatedLastCut O H D hD e he)
  (independentProduct
    (actualCurrentRootK O.network r (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he))
      initial inside (Finset.filter_subset _ _))
    ((sourceStageHistory O.network r phase initial).map (originalActorOutsideHistory O a))).bind
      (fun data => (actualCompletedTerminal O.network r future initial readout
        (closeOriginalKActor (state initial) inside (.node b) data.1
          (data.2.getLastD (unrankedView (selectedView (state initial) (originalOutsideCopies O sample a)))))).map
            (fun o => (data.2,o)))

theorem actual_canonical_K_actor_same_completed_original_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {Obs : Type*}
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (initial : Code O.network sample)
    (hs : initial ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support)
    (readout : UnrankedView O.Vertex O.Edge Copy → Obs) :
    let a := D.vertex (T.network.graph.target e)
    let phase := closingSpanAgenda O H gamma common a (D.vertex (T.network.graph.source e))
      (originatedLastCut O H D hD e he)
    let future := originalClosingFuture O H gamma common (originatedLastCut O H D hD e he)
    (sourceStageHistory O.network r phase initial).bind (fun tr =>
      (((sourceProgram O.network r future (tr.getLastD initial)).bind (completionKernel O.network r)).map
        (fun z => readout (wholeOriginalView O.network z))).map
          (fun o => (originalActorOutsideHistory O a tr,o))) =
      canonicalKActorCompletedHistoryRow O H D hD gamma common r e he initial readout := by
  dsimp only
  let a := D.vertex (T.network.graph.target e)
  let b := D.vertex (T.network.graph.source e)
  let inside := enteringRoots O.network initial a
  let outside := exteriorRoots O.network initial a
  let phase := closingSpanAgenda O H gamma common a b (originatedLastCut O H D hD e he)
  let future := originalClosingFuture O H gamma common (originatedLastCut O H D hD e he)
  let plan := canonicalOriginatedPhysicalPlan O H D hD sample register gamma common r e he initial hs
  have hpart := (actual_entering_root_partition O.network initial a).1
  have hphysical : ∀ d ∈ (sourceProgram O.network r phase initial).support,
      G1JointUnrankedForestAssembly.PrunedPanelSeparated (state d) inside outside ∧
        ∀ x ∈ inside, copyLocation (state d) x = .node b := by
    simpa only [plan,canonicalOriginatedPhysicalPlan,G1ActualUnrankedKMacro.PhysicalKExit] using plan.physical
  have hrow := actual_K_only_actor_same_completed_original_future O.network r phase future initial inside outside
    (Finset.filter_subset _ _) hpart plan.separated (.node b) hphysical
    (fun d hd z hz => actual_originated_closing_future_root_support O H D hD sample register r gamma common e he hs hd hz)
    readout
  have hco := (canonicalOriginatedHistoryPlan O H D hD sample register gamma common r e he initial hs).cohort
  change originalExteriorCopies (state initial) outside = _ at hco
  have hpath : originalExteriorHistory O.network initial outside = originalActorOutsideHistory O a := by
    funext tr
    simp only [originalExteriorHistory,originalActorOutsideHistory,hco]
    rfl
  have hin : ∀ x ∈ inside, copyLocation (state initial) x = .node a := by
    intro x hx
    obtain ⟨hx,hpop⟩ := Finset.mem_filter.mp hx
    have hr := initial.property.forest.representative x hx
    change (state initial).ancestor x = x at hr
    change (state initial).location ((state initial).ancestor x) = _
    rw [hr]
    exact hpop
  have hK := actual_originated_closing_bridge_K O H D hD r gamma common e he inside initial
    (Finset.filter_subset _ _) hin
  change actualCurrentRootK O.network r phase initial inside _ = _ at hK
  rw [actualKActorCompletedHistoryRow,hpath,hco,hK] at hrow
  exact hrow

#print axioms actual_canonical_K_actor_same_completed_original_history
end G1CanonicalKActorCompletedHistory
