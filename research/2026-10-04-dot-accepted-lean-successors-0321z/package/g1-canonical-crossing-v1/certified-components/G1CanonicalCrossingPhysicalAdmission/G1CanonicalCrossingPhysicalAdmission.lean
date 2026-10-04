import G1CanonicalCrossingCohortPartition
import G1CrossingHistorySameActualCompletion

/-! Canonical strict crossing dates discharge ALL physical/root premises of
the actual full exterior-history/completion theorem. Every panel is an actual
fixed ORIGINAL descendant cohort; input-root caps remain separate K metadata.
Contributor: dot, 2026-10-03. -/
namespace G1CanonicalCrossingPhysicalAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceAncestralCompletion
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanClosingPhase G1OriginalClosingCalendarBinding G1OriginatedClosingSourceAdmission
open G1InitializedFrontierPrefix G1SameOriginalExteriorContinuation G1OriginalCrossingCalendar
open G1OriginalExteriorCohort
open G1CanonicalCrossingRootAndKAdmission G1OriginalDescendantCohortAgenda
open G1CanonicalCrossingCohortPartition G1SeparatedAgendaSupportCuts
open G1ActualJointProgram G1JointSeparatedSourceGeometry G1JointUnrankedForestAssembly G1JointForestPreservation
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

structure CrossingPhysicalAdmission {V E X Copy : Type*}
    [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
    [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
    (N : RootedBinary V E X) (sample : Copy → X) (r : PositivePairRates E)
    (left right exterior : Finset Copy) (P Q R future : List (ProgramStep N)) (s : Code N sample) where
  cover : right ∪ (left ∪ exterior) = Finset.univ
  prefixSeparate : SeparatedAgenda N r left (right ∪ exterior) P s
  concurrentFirst : ∀ p ∈ (sourceProgram N r P s).support, SeparatedAgenda N r left (right ∪ exterior) Q p
  concurrentOthers : ∀ p ∈ (sourceProgram N r P s).support, SeparatedAgenda N r right exterior Q p
  suffixSeparate : ∀ p ∈ (sourceProgram N r P s).support,
    ∀ q ∈ (sourceProgram N r Q p).support, SeparatedAgenda N r right (left ∪ exterior) R q
  middlePure : ∀ p ∈ (sourceProgram N r P s).support,
    ∀ q ∈ (sourceProgram N r Q p).support, PrunedPanelSeparated (state q) left exterior
  finalPure : ∀ p ∈ (sourceProgram N r P s).support,
    ∀ q ∈ (sourceProgram N r Q p).support, ∀ z ∈ (sourceProgram N r R q).support,
      PrunedPanelSeparated (state z) right (left ∪ exterior)
  rootSupport : ∀ p ∈ (sourceProgram N r P s).support,
    ∀ q ∈ (sourceProgram N r Q p).support, ∀ z ∈ (sourceProgram N r R q).support,
    ∀ d ∈ (sourceProgram N r future z).support, AncestralRoot N d

/-- All record fields are physical support properties and are DERIVED from
actual initialized original chronology and constructed source provenance.
There is no desired kernel, source-row or completed-law equality field. -/
theorem canonicalCrossingPhysicalAdmission (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (e f : T.Edge) (he : T.network.graph.IsBridge e) (hf : T.network.graph.IsBridge f)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (hab : O.calendar.age (D.vertex (T.network.graph.target e)) < O.calendar.age (D.vertex (T.network.graph.target f)))
    (hbc : O.calendar.age (D.vertex (T.network.graph.target f)) < O.calendar.age (D.vertex (T.network.graph.source e)))
    (hcd : O.calendar.age (D.vertex (T.network.graph.source e)) < O.calendar.age (D.vertex (T.network.graph.source f)))
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (register : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e)))) (initialCode O.network sample register)).support) :
    CrossingPhysicalAdmission O.network sample r
      (crossingLeftCopies O T D sample e) (crossingRightCopies O T D sample f) (crossingExteriorCopies O T D sample e f)
      (crossingPrefix O H gamma common (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.target f)))
      (crossingConcurrent O H gamma common (D.vertex (T.network.graph.target f))
        (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he))
      (crossingSuffix O H gamma common (D.vertex (T.network.graph.source e)) (D.vertex (T.network.graph.source f))
        (originatedLastCut O H D hD e he) (originatedLastCut O H D hD f hf))
      (originalClosingFuture O H gamma common (originatedLastCut O H D hD f hf)) s := by
  let left := crossingLeftCopies O T D sample e
  let right := crossingRightCopies O T D sample f
  let exterior := crossingExteriorCopies O T D sample e f
  let P := crossingPrefix O H gamma common (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.target f))
  let Q := crossingConcurrent O H gamma common (D.vertex (T.network.graph.target f))
    (D.vertex (T.network.graph.source e)) (originatedLastCut O H D hD e he)
  let R := crossingSuffix O H gamma common (D.vertex (T.network.graph.source e)) (D.vertex (T.network.graph.source f))
    (originatedLastCut O H D hD e he) (originatedLastCut O H D hD f hf)
  have hd := actual_crossing_original_cohorts_disjoint O H D hD e f he hf hab hbc sample
  have hOutA : right ∪ exterior = originalOutsideCopies O sample (D.vertex (T.network.graph.target e)) :=
    by
      ext x
      have hx := congrArg (fun z : Finset Copy => x ∈ z) (actual_three_cohort_left_complement O T D sample e f hd)
      simpa only [left,right,exterior,originalOutsideCopies,Finset.mem_union] using Iff.of_eq hx
  have hOutB : left ∪ exterior = originalOutsideCopies O sample (D.vertex (T.network.graph.target f)) :=
    by
      ext x
      have hx := congrArg (fun z : Finset Copy => x ∈ z) (actual_three_cohort_right_complement O T D sample e f hd)
      simpa only [left,right,exterior,originalOutsideCopies,Finset.mem_union] using Iff.of_eq hx
  have hA : SeparatedAgenda O.network r left (right ∪ exterior) (P ++ Q) s := by
    rw [hOutA,←actual_first_crossing_phase O H gamma common _ _ _ _ hab hbc]
    exact actual_initialized_original_cohort_span_separator O H D hD sample register gamma common r e he hs
  have hAcuts := (actual_separated_agenda_append_iff O.network r left (right ∪ exterior) P Q s).mp hA
  have hB (p : Code O.network sample) (hp : p ∈ (sourceProgram O.network r P s).support) :
      SeparatedAgenda O.network r right (left ∪ exterior) (Q ++ R) p := by
    have hpInit := actual_crossing_second_initialized_frontier O H gamma common _ _ hab sample register r hs hp
    rw [hOutB,←actual_second_crossing_phase O H gamma common _ _ _ _ _
      (actual_originated_last_cut_source O H D hD e he) hbc hcd]
    exact actual_initialized_original_cohort_span_separator O H D hD sample register gamma common r f hf hpInit
  have hApure : PrunedPanelSeparated (state s) left (right ∪ exterior) := by
    apply population_separated_pruned_panels _ s.property.forest
    rw [hOutA]
    exact actual_original_cohort_frontier_population_separator O H D hD sample register gamma common r e he hs
  have hcover : right ∪ (left ∪ exterior) = Finset.univ := by
    ext x
    simp only [right,left,exterior,crossingExteriorCopies,Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  refine ⟨hcover,hAcuts.1,hAcuts.2,?_,?_,?_,?_,?_⟩
  · intro p hp
    have hc := ((actual_separated_agenda_append_iff O.network r right (left ∪ exterior) Q R p).mp (hB p hp)).1
    exact actual_separated_agenda_mono O.network r right (left ∪ exterior) right exterior
      (fun _ h => h) Finset.subset_union_right Q p hc
  · intro p hp q hq
    exact ((actual_separated_agenda_append_iff O.network r right (left ∪ exterior) Q R p).mp (hB p hp)).2 q hq
  · intro p hp q hq
    have hqAll : q ∈ (sourceProgram O.network r (P ++ Q) s).support := by
      rw [actual_source_program_append]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨p,hp,hq⟩
    have pureAll := actual_agenda_pruned_panel_separation O.network r left (right ∪ exterior) (P ++ Q) s hA hApure hqAll
    intro root hroot
    rcases pureAll root hroot with hl | hother
    · exact Or.inl hl
    · right
      apply (UnifiedLean.Source.SourceForestSilentPruning.prune_none_iff_no_selected_leaves exterior _).mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hm : x ∈ ((state q).genealogy root).leaves ∩ (right ∪ exterior) :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,Finset.mem_union_right _ (Finset.mem_inter.mp hx).2⟩
      rw [(UnifiedLean.Source.SourceForestSilentPruning.prune_none_iff_no_selected_leaves _ _).mp hother] at hm
      exact Finset.notMem_empty _ hm
  · intro p hp q hq z hz
    have hpInit := actual_crossing_second_initialized_frontier O H gamma common _ _ hab sample register r hs hp
    have hpureB : PrunedPanelSeparated (state p) right (left ∪ exterior) := by
      apply population_separated_pruned_panels _ p.property.forest
      rw [hOutB]
      exact actual_original_cohort_frontier_population_separator O H D hD sample register gamma common r f hf hpInit
    apply actual_agenda_pruned_panel_separation O.network r right (left ∪ exterior) (Q ++ R) p (hB p hp) hpureB
    rw [actual_source_program_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨q,hq,hz⟩
  · intro p hp q hq z hz d hd
    exact actual_canonical_crossing_same_future_root O H D hD e f he hf gamma common hab hbc hcd sample register r hs hp hq hz hd

#print axioms canonicalCrossingPhysicalAdmission
end G1CanonicalCrossingPhysicalAdmission
