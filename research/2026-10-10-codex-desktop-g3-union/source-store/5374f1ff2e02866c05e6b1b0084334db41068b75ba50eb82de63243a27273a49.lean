import G1FiniteOriginalCausalCoordinates

/-! The ACTUAL finite original source tensor descends to complete unranked
panel coordinates and reconstructs the WHOLE original causal quotient. Each
factor is the true original unrankedProgram, with SAME original register;
no desired independence or raw ordered-state product is an input. -/
namespace G1ActualFiniteOriginalQuotientTensor
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport
open G1UnrankedSourceView G1UnrankedActualGenerator G1UnrankedActualFuture
open G1OriginalWholeCausalView G1ActualFinitePanelProgramTensor G1FiniteOriginalCausalCoordinates
open G1ActualJointEpoch G1ActualJointOpaqueContext G1ContextualForestReplacement G1ActualJointProgram
open scoped Classical
universe u v w z
variable {V : Type u} {E : Type v} {X : Type w} {Copy : Type z}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

noncomputable def originalQuotientPanelProduct (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (keeps : List (Finset Copy)) → PMF (OriginalPanelViews V E Copy keeps)
  | [] => PMF.pure PUnit.unit
  | keep::keeps => independentProduct
      ((unrankedProgram N r keep ops (unrankedProjection N keep s)).map Subtype.val)
      (originalQuotientPanelProduct N r ops s keeps)

lemma actual_selected_panel_quotient_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (keep : Finset Copy) :
    (selectedProgram N r keep ops (projection N keep s)).map (fun v => unrankedView v.val) =
      (unrankedProgram N r keep ops (unrankedProjection N keep s)).map Subtype.val := by
  rw [←actual_source_program_projection,PMF.map_comp,←actual_unranked_source_program,PMF.map_comp]
  rfl

theorem actual_finite_panel_product_descends (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (keeps : List (Finset Copy)) :
    (selectedPanelProduct.{u,v,w,z,0} N r ops keeps (panelProjection.{u,v,w,z,0} N keeps s)).map (quotientPanelCoordinates N keeps) =
      originalQuotientPanelProduct N r ops s keeps := by
  induction keeps with
  | nil => simp [selectedPanelProduct,quotientPanelCoordinates,originalQuotientPanelProduct,PMF.pure_map]
  | cons keep keeps ih =>
    change (independentProduct (selectedProgram N r keep ops (projection N keep s))
      (selectedPanelProduct.{u,v,w,z,0} N r ops keeps (panelProjection.{u,v,w,z,0} N keeps s))).map
        (fun data => (unrankedView data.1.val,quotientPanelCoordinates N keeps data.2)) = _
    calc
      _ = independentProduct
          ((selectedProgram N r keep ops (projection N keep s)).map (fun v => unrankedView v.val))
          ((selectedPanelProduct.{u,v,w,z,0} N r ops keeps (panelProjection.{u,v,w,z,0} N keeps s)).map
            (quotientPanelCoordinates N keeps)) := independentProduct_map _ _ _ _
      _ = _ := by rw [actual_selected_panel_quotient_row,ih]; rfl

/-- Genuine JOINT entire original unranked panel row for ANY finite actor
family under physical separation; no two/three-actor cap or raw-index result. -/
theorem actual_finite_original_quotient_panel_source_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (keeps : List (Finset Copy))
    (hsep : PanelSeparatedAgenda N r ops keeps s) :
    (sourceProgram N r ops s).map (fun d => originalPanelViews (state d) keeps) =
      originalQuotientPanelProduct N r ops s keeps := by
  calc
    _ = ((sourceProgram N r ops s).map (panelProjection.{u,v,w,z,0} N keeps)).map (quotientPanelCoordinates N keeps) := by
      rw [PMF.map_comp]
      congr 1
      funext d
      exact (actual_quotient_panel_projection N d keeps).symm
    _ = _ := by rw [actual_finite_panel_source_program.{u,v,w,z,0,0} N r ops keeps s hsep,actual_finite_panel_product_descends]

/-- The WHOLE original source-state row is reconstructed from the true
original quotient panel tensor. Actual pure fibres/full original copy cover
are physical admissions; desired source/kernel/output equality is derived. -/
theorem actual_finite_original_quotient_whole_source_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (keeps : List (Finset Copy))
    (cover : panelUnion keeps = Finset.univ) (hsep : PanelSeparatedAgenda N r ops keeps s)
    (hp : ∀ d ∈ (sourceProgram N r ops s).support, PureOriginalPanels (state d) keeps) :
    (sourceProgram N r ops s).map (wholeOriginalView N) =
      (originalQuotientPanelProduct N r ops s keeps).map (joinOriginalPanelViews (state s).register keeps) := by
  calc
    _ = (sourceProgram N r ops s).map (fun d =>
        joinOriginalPanelViews (state s).register keeps (originalPanelViews (state d) keeps)) := by
      apply map_eq_of_eq_on_support
      intro d hd
      rw [←actual_program_register_support N r ops s hd]
      have h := actual_finite_original_panel_view_reconstruction (state d) d.property.forest keeps (hp d hd)
      rw [cover] at h
      exact h.symm
    _ = ((sourceProgram N r ops s).map (fun d => originalPanelViews (state d) keeps)).map
        (joinOriginalPanelViews (state s).register keeps) := by rw [PMF.map_comp]; rfl
    _ = _ := by rw [actual_finite_original_quotient_panel_source_row N r ops s keeps hsep]

theorem actual_active_family_whole_original_source_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (actors : List (Finset Copy))
    (hsep : PanelSeparatedAgenda N r ops (activeOriginalPanelFamily actors) s)
    (hp : ∀ d ∈ (sourceProgram N r ops s).support, PureOriginalPanels (state d) (activeOriginalPanelFamily actors)) :
    (sourceProgram N r ops s).map (wholeOriginalView N) =
      (originalQuotientPanelProduct N r ops s (activeOriginalPanelFamily actors)).map
        (joinOriginalPanelViews (state s).register (activeOriginalPanelFamily actors)) :=
  actual_finite_original_quotient_whole_source_row N r ops s _ (actual_active_original_panel_cover actors) hsep hp

/-- Hidden raw source representations cannot affect the actual quotient
product: its inputs are only the complete original unranked panel views. -/
theorem actual_original_quotient_product_row_independent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s z : Code N sample) (keeps : List (Finset Copy))
    (h : originalPanelViews (state s) keeps = originalPanelViews (state z) keeps) :
    originalQuotientPanelProduct N r ops s keeps = originalQuotientPanelProduct N r ops z keeps := by
  induction keeps with
  | nil => rfl
  | cons keep keeps ih =>
    have head := congrArg Prod.fst h
    have tail := congrArg Prod.snd h
    have he : unrankedProjection N keep s = unrankedProjection N keep z := Subtype.ext head
    simp only [originalQuotientPanelProduct,he,ih tail]

#print axioms actual_finite_original_quotient_whole_source_row
#print axioms actual_original_quotient_product_row_independent
end G1ActualFiniteOriginalQuotientTensor
