import G1CanonicalCrossingCompletedSourceLaw

/-! Actual original-source tensor laws for ANY finite family of physically
separated panels. This is the simultaneous active-actor source primitive,
without a fixed two/three-actor cap. -/
namespace G1ActualFinitePanelProgramTensor
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceProgramTransport
open G1ActualJointEpoch G1ActualJointGenerator G1ActualJointProgram
open G1NestedOriginalSourceProjection G1ActualThreePanelSourceTensor
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def panelUnion : List (Finset Copy) → Finset Copy
  | [] => ∅
  | keep::keeps => keep ∪ panelUnion keeps

abbrev PanelIndex (N : RootedBinary V E X) (sample : Copy → X) : List (Finset Copy) → Type _
  | [] => PUnit
  | keep::keeps => SelectedIndex N sample keep × PanelIndex N sample keeps

noncomputable def panelProjection (N : RootedBinary V E X) {sample : Copy → X} :
    (keeps : List (Finset Copy)) → Code N sample → PanelIndex N sample keeps
  | [],_ => PUnit.unit
  | keep::keeps,s => (projection N keep s,panelProjection N keeps s)

noncomputable def splitPanels (N : RootedBinary V E X) {sample : Copy → X} :
    (keeps : List (Finset Copy)) → SelectedIndex N sample (panelUnion keeps) → PanelIndex N sample keeps
  | [],_ => PUnit.unit
  | keep::keeps,v => (subIndex N keep (keep ∪ panelUnion keeps) Finset.subset_union_left v,
      splitPanels N keeps (subIndex N (panelUnion keeps) (keep ∪ panelUnion keeps) Finset.subset_union_right v))

lemma actual_split_panel_projection (N : RootedBinary V E X) {sample : Copy → X}
    (keeps : List (Finset Copy)) (s : Code N sample) :
    splitPanels N keeps (projection N (panelUnion keeps) s) = panelProjection N keeps s := by
  induction keeps with
  | nil => rfl
  | cons keep keeps ih =>
      simp only [splitPanels,panelProjection,panelUnion,actual_subindex_projection,ih]

noncomputable def selectedPanelProduct (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) :
    (keeps : List (Finset Copy)) → PanelIndex N sample keeps → PMF (PanelIndex N sample keeps)
  | [],_ => PMF.pure PUnit.unit
  | keep::keeps,v => independentProduct (selectedProgram N r keep ops v.1) (selectedPanelProduct N r ops keeps v.2)

/-- Only physical source population separation is stored. The common entering
register is fixed by the actual source state; independence is a conclusion. -/
noncomputable def PanelSeparatedAgenda (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) : List (Finset Copy) → Code N sample → Prop
  | [],_ => True
  | keep::keeps,s => SeparatedAgenda N r keep (panelUnion keeps) ops s ∧ PanelSeparatedAgenda N r ops keeps s

/-- Genuine actual whole selected genealogy/population/SAME-register product
law for arbitrary many concurrent actors, conditional on their entering state. -/
theorem actual_finite_panel_source_program (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (keeps : List (Finset Copy))
    (s : Code N sample) (hsep : PanelSeparatedAgenda N r ops keeps s) :
    (sourceProgram N r ops s).map (panelProjection N keeps) =
      selectedPanelProduct N r ops keeps (panelProjection N keeps s) := by
  induction keeps with
  | nil =>
      change (sourceProgram N r ops s).map (Function.const (Code N sample) PUnit.unit) = PMF.pure PUnit.unit
      exact PMF.map_const _ _
  | cons keep keeps ih =>
      have htail : (selectedProgram N r (panelUnion keeps) ops (projection N (panelUnion keeps) s)).map
          (splitPanels N keeps) = selectedPanelProduct N r ops keeps (panelProjection N keeps s) := by
        rw [←actual_source_program_projection,PMF.map_comp]
        have hfun : splitPanels N (sample := sample) keeps ∘ projection N (panelUnion keeps) = panelProjection N keeps := by
          funext d
          exact actual_split_panel_projection N keeps d
        rw [hfun]
        exact ih hsep.2
      calc
        _ = ((sourceProgram N r ops s).map (jointProjection N keep (panelUnion keeps))).map
            (fun data => (data.1,splitPanels N keeps data.2)) := by
          rw [PMF.map_comp]
          congr 1
          funext d
          simp only [panelProjection,Function.comp_def,jointProjection,actual_split_panel_projection]
        _ = _ := by
          rw [actual_separated_joint_program_law N r keep (panelUnion keeps) ops s hsep.1,
            product_map_right,htail]
          rfl

#print axioms actual_finite_panel_source_program
end G1ActualFinitePanelProgramTensor
