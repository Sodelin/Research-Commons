import G1OriginalOpaqueKActorOutput

/-! Canonical actor row at a REAL original source frontier. Every physical
purity/single exit/cohort condition is derived from the accepted Originated
bridge/source admission. The exposed private label is the TRUE CURRENT-root
OriginalSpan K, grafted into all saved original descendant-labelled trees. -/
namespace G1CanonicalOriginalKOnlyActorRow
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanClosingPhase G1OriginatedClosingSourceAdmission
open G1ActualEnteringFrontier G1InitializedFrontierPrefix G1OriginalExteriorCohort G1CanonicalOriginatedMacroPlans
open G1OriginalOpaqueExteriorView G1UnrankedSourceView G1ActualKProductInsertion
open G1OriginalOpaqueKActorOutput
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalActorInsideCopies (O : Source X) {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (node : O.Vertex) : Finset Copy :=
  Finset.univ \ originalOutsideCopies O sample node

lemma actual_current_root_cohorts_complement {V E Copy : Type*} [DecidableEq V] [DecidableEq E]
    [Fintype Copy] [DecidableEq Copy] (initial : State V E Copy) (hi : Valid initial)
    (inside : Finset Copy) :
    originalExteriorCopies initial inside =
      Finset.univ \ originalExteriorCopies initial (initial.live \ inside) := by
  ext x
  have hl := hi.ancestor_live x
  simp only [originalExteriorCopies,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,hl,
    true_and,not_not]

theorem actual_canonical_original_inside_cohort (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (initial : Code O.network sample)
    (hs : initial ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    originalExteriorCopies (state initial)
      (enteringRoots O.network initial (D.vertex (T.network.graph.target e))) =
      originalActorInsideCopies O sample (D.vertex (T.network.graph.target e)) := by
  have hc := (canonicalOriginatedHistoryPlan O H D hD sample register gamma common r e he initial hs).cohort
  change originalExteriorCopies (state initial)
    (exteriorRoots O.network initial (D.vertex (T.network.graph.target e))) =
      originalOutsideCopies O sample (D.vertex (T.network.graph.target e)) at hc
  calc
    _ = Finset.univ \ originalExteriorCopies (state initial)
        (exteriorRoots O.network initial (D.vertex (T.network.graph.target e))) :=
      actual_current_root_cohorts_complement (state initial) initial.property.forest _
    _ = _ := by rw [hc]; simp only [originalActorInsideCopies]

noncomputable def canonicalOriginalKActorRow (O : Source.{u,v,w} X)
    {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (e : T.Edge) (he : T.network.graph.IsBridge e) (initial : Code O.network sample) :=
  (actualCurrentRootK O.network r
    (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he)) initial
    (enteringRoots O.network initial (D.vertex (T.network.graph.target e))) (Finset.filter_subset _ _)).map
      (originalActorKView (state initial) (enteringRoots O.network initial (D.vertex (T.network.graph.target e)))
        (.node (D.vertex (T.network.graph.source e))))

/-- The FULL original descendant-panel UNRANKED actor row is exactly the
source-derived K-only interface. No desired row equality, single exit,
cohort relation or descendant-count bound is assumed. -/
theorem actual_canonical_original_actor_row_is_K_only (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    (initial : Code O.network sample)
    (hs : initial ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    (selectedProgram O.network r (originalActorInsideCopies O sample (D.vertex (T.network.graph.target e)))
      (closingSpanAgenda O H gamma common (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e))
        (originatedLastCut O H D hD e he))
      (projection O.network (originalActorInsideCopies O sample (D.vertex (T.network.graph.target e))) initial)).map
        (fun v => unrankedView v.val) = canonicalOriginalKActorRow O D gamma common r e he initial := by
  let inside := enteringRoots O.network initial (D.vertex (T.network.graph.target e))
  let outside := exteriorRoots O.network initial (D.vertex (T.network.graph.target e))
  let phase := closingSpanAgenda O H gamma common (D.vertex (T.network.graph.target e))
    (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he)
  let hplan := canonicalOriginatedPhysicalPlan O H D hD sample register gamma common r e he initial hs
  have hpart := (actual_entering_root_partition O.network initial (D.vertex (T.network.graph.target e))).1
  have hphysical : ∀ d ∈ (sourceProgram O.network r phase initial).support,
      G1JointUnrankedForestAssembly.PrunedPanelSeparated (state d) inside outside ∧
        ∀ x ∈ inside, copyLocation (state d) x = .node (D.vertex (T.network.graph.source e)) := by
    simpa only [hplan,canonicalOriginatedPhysicalPlan,G1ActualUnrankedKMacro.PhysicalKExit] using hplan.physical
  have hrow := actual_private_original_row_is_K_graft O.network r phase initial inside outside
    (Finset.filter_subset _ _) hpart (.node (D.vertex (T.network.graph.source e))) hphysical
  have hc := actual_canonical_original_inside_cohort O H D hD sample register gamma common r e he initial hs
  change originalExteriorCopies (state initial) inside = _ at hc
  rw [hc] at hrow
  have hin : ∀ x ∈ inside, copyLocation (state initial) x = .node (D.vertex (T.network.graph.target e)) := by
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
  rw [hK] at hrow
  rw [←actual_source_program_projection,PMF.map_comp]
  exact hrow

#print axioms actual_canonical_original_actor_row_is_K_only
end G1CanonicalOriginalKOnlyActorRow
