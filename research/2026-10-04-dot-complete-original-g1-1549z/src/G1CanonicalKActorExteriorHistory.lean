import G1KOnlyActorWholeExteriorHistory

/-! Actual OriginalSpan K-only actor row, JOINT with the complete fixed
original exterior checkpoint trajectory. All canonical physical and cohort
admissions are derived at a REAL original initialized frontier. -/
namespace G1CanonicalKActorExteriorHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanClosingPhase G1OriginatedClosingSourceAdmission
open G1ActualEnteringFrontier G1InitializedFrontierPrefix G1OriginalExteriorCohort G1CanonicalOriginatedMacroPlans
open G1OriginalOpaqueExteriorView G1OriginalExteriorHistoryProduct G1UnrankedSourceView
open G1ActualJointEpoch G1ActualJointStageHistory G1ActualKProductInsertion
open G1CanonicalOriginalKOnlyActorRow G1OriginalOpaqueKActorOutput G1KOnlyActorWholeExteriorHistory
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalActorOutsideHistory (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (node : O.Vertex) (tr : List (Code O.network sample)) :=
  tr.map (fun d => unrankedView (selectedView (state d) (originalOutsideCopies O sample node)))

theorem actual_canonical_K_actor_whole_original_exterior_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (initial : Code O.network sample)
    (hs : initial ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    let a := D.vertex (T.network.graph.target e)
    let phase := closingSpanAgenda O H gamma common a (D.vertex (T.network.graph.source e))
      (originatedLastCut O H D hD e he)
    (sourceStageHistory O.network r phase initial).map (fun tr =>
      (unrankedView (selectedView (state (tr.getLastD initial)) (originalActorInsideCopies O sample a)),
        originalActorOutsideHistory O a tr)) =
      independentProduct (canonicalOriginalKActorRow O D gamma common r e he initial)
        ((sourceStageHistory O.network r phase initial).map (originalActorOutsideHistory O a)) := by
  dsimp only
  let a := D.vertex (T.network.graph.target e)
  let b := D.vertex (T.network.graph.source e)
  let inside := enteringRoots O.network initial a
  let outside := exteriorRoots O.network initial a
  let phase := closingSpanAgenda O H gamma common a b (originatedLastCut O H D hD e he)
  let plan := canonicalOriginatedPhysicalPlan O H D hD sample register gamma common r e he initial hs
  have hpart := (actual_entering_root_partition O.network initial a).1
  have hphysical : ∀ d ∈ (sourceProgram O.network r phase initial).support,
      G1JointUnrankedForestAssembly.PrunedPanelSeparated (state d) inside outside ∧
        ∀ x ∈ inside, copyLocation (state d) x = .node b := by
    simpa only [plan,canonicalOriginatedPhysicalPlan,G1ActualUnrankedKMacro.PhysicalKExit] using plan.physical
  have hprod := actual_K_only_actor_original_outside_history_product O.network r phase initial inside outside
    (Finset.filter_subset _ _) hpart plan.separated (.node b) hphysical
  have hci := actual_canonical_original_inside_cohort O H D hD sample register gamma common r e he initial hs
  have hco := (canonicalOriginatedHistoryPlan O H D hD sample register gamma common r e he initial hs).cohort
  change originalExteriorCopies (state initial) inside = _ at hci
  change originalExteriorCopies (state initial) outside = _ at hco
  have hpath : originalExteriorHistory O.network initial outside = originalActorOutsideHistory O a := by
    funext tr
    simp only [originalExteriorHistory,originalActorOutsideHistory,hco]
    rfl
  simp only [originalExteriorHistory] at hprod
  rw [hci,hco] at hprod
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
  rw [hK] at hprod
  rw [hpath] at hprod
  exact hprod

#print axioms actual_canonical_K_actor_whole_original_exterior_history
end G1CanonicalKActorExteriorHistory
