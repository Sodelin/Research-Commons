import G1NestedOriginalSourceProjection

/-! A derived three-panel tensor law for the ACTUAL source agenda. Nested
original-labelled projection is constructed rather than an independence field.
Contributor: dot, 2026-10-03. -/
namespace G1ActualThreePanelSourceTensor
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceProgramTransport
open G1ActualJointEpoch G1ActualJointGenerator G1ActualJointProgram
open G1NestedOriginalSourceProjection
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def splitUnion (N : RootedBinary V E X) {sample : Copy → X}
    (left right : Finset Copy) (v : SelectedIndex N sample (left ∪ right)) :=
  (subIndex N left (left ∪ right) Finset.subset_union_left v,
    subIndex N right (left ∪ right) Finset.subset_union_right v)

lemma actual_split_union_projection (N : RootedBinary V E X) {sample : Copy → X}
    (left right : Finset Copy) (s : Code N sample) :
    splitUnion N left right (projection N (left ∪ right) s) = jointProjection N left right s := by
  simp only [splitUnion,actual_subindex_projection,jointProjection]

lemma product_map_right {A B C : Type*} (p : PMF A) (q : PMF B) (f : B → C) :
    (independentProduct p q).map (fun v => (v.1,f v.2)) = independentProduct p (q.map f) := by
  simp only [independentProduct,PMF.map_bind,PMF.map_comp,Function.comp_def]

noncomputable def tripleProjection (N : RootedBinary V E X) {sample : Copy → X}
    (first second third : Finset Copy) (s : Code N sample) :=
  (projection N first s,jointProjection N second third s)

/-- Complete labelled trees, original populations and the SAME register have
the genuine product of three actual selected program laws. Both agenda
conditions concern actual physical population separation only. -/
theorem actual_three_panel_source_program (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (first second third : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample)
    (firstSeparate : SeparatedAgenda N r first (second ∪ third) ops s)
    (otherSeparate : SeparatedAgenda N r second third ops s) :
    (sourceProgram N r ops s).map (tripleProjection N first second third) =
      independentProduct (selectedProgram N r first ops (projection N first s))
        (independentProduct (selectedProgram N r second ops (projection N second s))
          (selectedProgram N r third ops (projection N third s))) := by
  have hs : (selectedProgram N r (second ∪ third) ops (projection N (second ∪ third) s)).map
      (splitUnion N second third) =
      independentProduct (selectedProgram N r second ops (projection N second s))
        (selectedProgram N r third ops (projection N third s)) := by
    rw [←actual_source_program_projection,PMF.map_comp]
    have hfun : splitUnion N (sample := sample) second third ∘ projection N (second ∪ third) = jointProjection N second third := by
      funext d
      exact actual_split_union_projection N second third d
    rw [hfun]
    exact actual_separated_joint_program_law N r second third ops s otherSeparate
  calc
    _ = ((sourceProgram N r ops s).map (jointProjection N first (second ∪ third))).map
        (fun v => (v.1,splitUnion N second third v.2)) := by
      rw [PMF.map_comp]
      congr 1
      funext d
      simp only [Function.comp_def,jointProjection,actual_split_union_projection,tripleProjection]
    _ = _ := by
      rw [actual_separated_joint_program_law N r first (second ∪ third) ops s firstSeparate,
        product_map_right,hs]

#print axioms actual_three_panel_source_program
end G1ActualThreePanelSourceTensor
