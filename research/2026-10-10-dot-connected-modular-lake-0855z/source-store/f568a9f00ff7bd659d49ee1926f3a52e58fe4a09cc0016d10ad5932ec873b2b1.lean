import G1FiniteAsyncCoordinateDraw
import G1ActualFiniteOriginalQuotientTensor
import G1ActualOriginalOpenCloseAsyncInterface

/-! The derived ACTUAL original source panel tensor is converted to finite
functional actor slots and the base. All factors are the original unranked
source rows at their original input values. Empty inactive slots retain the
SAME original register; no desired independence law is a hypothesis. -/
namespace G1OriginalPanelTensorSerialization
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceForestSilentPruning
open G1UnrankedSourceView G1UnrankedActualGenerator G1UnrankedActualFuture G1ActualJointEpoch G1ActualJointOpaqueContext
open G1ActualJointProgram G1ActualFinitePanelProgramTensor G1FiniteOriginalCausalCoordinates
open G1ActualFiniteOriginalQuotientTensor G1ActualOriginalUnrankedLocalKernel
open G1ActualOriginalPrivateAsyncStep G1ActualOriginalOpenCloseAsyncInterface
open G1PendingActorInterfaceCommutation G1FiniteAsyncCoordinateDraw
open scoped Classical
variable {V E Copy X I : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy] [DecidableEq I]

noncomputable def actorPanelDrawData (base : Finset Copy) (slots : I → Finset Copy) :
    (actors : List I) → OriginalPanelViews V E Copy (actors.map slots ++ [base]) →
      ActorDrawData (UnrankedView V E Copy) (UnrankedView V E Copy) actors
  | [],data => data.1
  | _::actors,data => (data.1,actorPanelDrawData base slots actors data.2)

omit [Fintype V] [Fintype E] [Fintype Copy] [DecidableEq V] [DecidableEq E] [DecidableEq I] in
lemma actual_panel_draw_values (s : State V E Copy) (base : Finset Copy) (slots : I → Finset Copy)
    (actors : List I) :
    actorPanelDrawData base slots actors (originalPanelViews s (actors.map slots ++ [base])) =
      actorDrawValues (fun actor => unrankedView (selectedView s (slots actor)))
        (unrankedView (selectedView s base)) actors := by
  induction actors with
  | nil => rfl
  | cons actor actors ih =>
    change (unrankedView (selectedView s (slots actor)),
      actorPanelDrawData base slots actors (originalPanelViews s (actors.map slots ++ [base]))) =
      (unrankedView (selectedView s (slots actor)),
        actorDrawValues (fun actor => unrankedView (selectedView s (slots actor)))
          (unrankedView (selectedView s base)) actors)
    rw [ih]

lemma actual_panel_product_draw_tensor (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (base : Finset Copy) (slots : I → Finset Copy) (actors : List I) :
    (originalQuotientPanelProduct N r ops s (actors.map slots ++ [base])).map
        (actorPanelDrawData base slots actors) =
      frozenDrawProduct
        (fun actor => originalLocalRow N sample r (slots actor) ops
          (unrankedView (selectedView (state s) (slots actor))))
        (originalLocalRow N sample r base ops (unrankedView (selectedView (state s) base))) actors := by
  induction actors with
  | nil =>
    change (independentProduct
      ((unrankedProgram N r base ops (unrankedProjection N base s)).map Subtype.val)
      (PMF.pure PUnit.unit)).map Prod.fst = _
    simp only [independentProduct,PMF.map_bind,PMF.pure_map,PMF.bind_pure]
    exact (actual_original_local_row_at_index N sample r base ops (unrankedProjection N base s)).symm
  | cons actor actors ih =>
    change (independentProduct
      ((unrankedProgram N r (slots actor) ops (unrankedProjection N (slots actor) s)).map Subtype.val)
      (originalQuotientPanelProduct N r ops s (actors.map slots ++ [base]))).map
      (fun data => (data.1,actorPanelDrawData base slots actors data.2)) = _
    have hmap : (independentProduct
        ((unrankedProgram N r (slots actor) ops (unrankedProjection N (slots actor) s)).map Subtype.val)
        (originalQuotientPanelProduct N r ops s (actors.map slots ++ [base]))).map
        (fun data => (data.1,actorPanelDrawData base slots actors data.2)) =
      independentProduct
        ((unrankedProgram N r (slots actor) ops (unrankedProjection N (slots actor) s)).map Subtype.val)
        ((originalQuotientPanelProduct N r ops s (actors.map slots ++ [base])).map
          (actorPanelDrawData base slots actors)) := by
      simp only [independentProduct,PMF.map_bind,PMF.map_comp,Function.comp_def]
    rw [hmap,ih]
    rw [frozenDrawProduct]
    congr 1
    exact (actual_original_local_row_at_index N sample r (slots actor) ops
      (unrankedProjection N (slots actor) s)).symm

/-- The whole actual original panel row, including the base, is converted
from the source-derived tensor. Physical separation, rather than desired
product equality, is the sole stochastic admission. -/
theorem actual_original_source_draw_tensor (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (base : Finset Copy) (slots : I → Finset Copy) (actors : List I)
    (hsep : PanelSeparatedAgenda N r ops (actors.map slots ++ [base]) s) :
    (sourceProgram N r ops s).map (fun d => actorPanelDrawData base slots actors
      (originalPanelViews (state d) (actors.map slots ++ [base]))) =
      frozenDrawProduct
        (fun actor => originalLocalRow N sample r (slots actor) ops
          (unrankedView (selectedView (state s) (slots actor))))
        (originalLocalRow N sample r base ops (unrankedView (selectedView (state s) base))) actors := by
  calc
    _ = ((sourceProgram N r ops s).map
        (fun d => originalPanelViews (state d) (actors.map slots ++ [base]))).map
          (actorPanelDrawData base slots actors) := by rw [PMF.map_comp]; rfl
    _ = _ := by rw [actual_finite_original_quotient_panel_source_row N r ops s _ hsep,
      actual_panel_product_draw_tensor]

#print axioms actual_original_source_draw_tensor
end G1OriginalPanelTensorSerialization
