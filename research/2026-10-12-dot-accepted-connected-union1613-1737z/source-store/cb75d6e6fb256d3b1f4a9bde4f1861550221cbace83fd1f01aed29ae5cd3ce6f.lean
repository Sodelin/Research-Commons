import G1OriginalClosingCalendarBinding

/-! A fixed ORIGINAL descendant-labelled exterior cohort at the actual cut
frontier, independent of hidden live root IDs. Contributor: dot, 2026-10-03. -/
namespace G1OriginalExteriorCohort
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1ActualEnteringFrontier G1InitializedFrontierPrefix
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalOutsideCopies (O : Source X) {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (D : O.Vertex) : Finset Copy :=
  Finset.univ.filter (fun x => ¬ O.network.graph.DReach D (O.network.leaf (sample x)))

/-- The SAME fixed original exterior cohort lifts the current-root outside
panel at every true naturally initialized frontier, with no descendant cap. -/
theorem actual_initialized_original_exterior_cohort (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (edge : O.Edge) (he : O.network.graph.IsBridge edge) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (O.network.graph.target edge))) (initialCode O.network sample register)).support) :
    ∀ x : Copy, x ∈ originalOutsideCopies O sample (O.network.graph.target edge) ↔
      (state s).ancestor x ∈ exteriorRoots O.network s (O.network.graph.target edge) := by
  obtain ⟨hdesc,_,_⟩ := actual_initialized_cut_frontier O.network O.calendar sample register H
    (fun h => gamma h.val) (fun h => common h.val) r edge he hs
  intro x
  have hl := s.property.forest.ancestor_live x
  change (state s).ancestor x ∈ (state s).live at hl
  have hd := hdesc x
  change O.network.graph.DReach (O.network.graph.target edge) (O.network.leaf (sample x)) ↔
    (state s).location ((state s).ancestor x) = .node (O.network.graph.target edge) at hd
  simpa only [originalOutsideCopies,Finset.mem_filter,Finset.mem_univ,true_and,
    exteriorRoots,Finset.mem_sdiff,enteringRoots,hl] using (not_congr hd)

#print axioms actual_initialized_original_exterior_cohort
end G1OriginalExteriorCohort
