import G1OriginalPanelTensorSerialization

/-! Concrete serialization of the actual original source tensor into every
active actor's actual local row and the actual base row. No raw ordered
coordinate equality or supplied desired product law enters. Empty inactive
slots retain exactly the original register. Canonical source-frontier
separation is supplied by the inherited physical admission theorem. -/
namespace G1ActualFiniteOriginalEpochAsync
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceForestSilentPruning
open G1UnrankedSourceView G1UnrankedActualGenerator G1ActualJointProgram
open G1ActualFinitePanelProgramTensor G1FiniteOriginalCausalCoordinates
open G1ActualOriginalUnrankedLocalKernel G1ActualOriginalOpenCloseAsyncInterface
open G1ContextualForestReplacement
open G1PendingActorInterfaceCommutation G1FiniteAsyncCoordinateDraw G1OriginalPanelTensorSerialization
open scoped Classical
variable {V E Copy X I : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy] [DecidableEq I]

noncomputable def finiteOriginalAsyncCoordinates (base : Finset Copy) (slots : I → Finset Copy)
    (s : State V E Copy) : UnrankedView V E Copy × (I → UnrankedView V E Copy) :=
  (unrankedView (selectedView s base),fun actor => unrankedView (selectedView s (slots actor)))

lemma actual_supported_draw_reconstruction (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (base : Finset Copy) (slots : I → Finset Copy) (actors : List I)
    (hinactive : ∀ actor ∉ actors, slots actor = ∅)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r ops s).support) :
    installFrozenDraw (finiteOriginalAsyncCoordinates base slots (state s)).2 actors
      (actorPanelDrawData base slots actors (originalPanelViews (state d) (actors.map slots ++ [base]))) =
      finiteOriginalAsyncCoordinates base slots (state d) := by
  rw [actual_panel_draw_values,install_actual_coordinate_values]
  apply Prod.ext
  · rfl
  · funext actor
    by_cases hm : actor ∈ actors
    · simp only [hm,ite_true,finiteOriginalAsyncCoordinates]
    · simp only [hm,ite_false,finiteOriginalAsyncCoordinates]
      rw [hinactive actor hm,actual_empty_original_panel,actual_empty_original_panel,
        actual_program_register_support N r ops s hd]

/-- Every active coordinate and the base are serialized from the TRUE
original source rows. Population separation is a physical premise and the
complete joint source law is derived. This includes zero active actors. -/
theorem actual_finite_original_source_async_program (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (base : Finset Copy) (slots : I → Finset Copy) (actors : List I) (hn : actors.Nodup)
    (hinactive : ∀ actor ∉ actors, slots actor = ∅)
    (hsep : PanelSeparatedAgenda N r ops (actors.map slots ++ [base]) s) :
    (sourceProgram N r ops s).map (fun d => finiteOriginalAsyncCoordinates base slots (state d)) =
      asyncProgram
        (actors.map (fun actor => AsyncOperation.localStep actor
          (originalLocalRow N sample r (slots actor) ops)) ++
            [AsyncOperation.exterior (originalLocalRow N sample r base ops)])
        (finiteOriginalAsyncCoordinates base slots (state s)) := by
  let initial := finiteOriginalAsyncCoordinates base slots (state s)
  calc
    _ = (sourceProgram N r ops s).map (fun d => installFrozenDraw initial.2 actors
        (actorPanelDrawData base slots actors (originalPanelViews (state d) (actors.map slots ++ [base])))) := by
      apply map_eq_of_eq_on_support
      intro d hd
      exact (actual_supported_draw_reconstruction N r ops s base slots actors hinactive hd).symm
    _ = ((sourceProgram N r ops s).map (fun d => actorPanelDrawData base slots actors
        (originalPanelViews (state d) (actors.map slots ++ [base])))).map
          (installFrozenDraw initial.2 actors) := by rw [PMF.map_comp]; rfl
    _ = (frozenDrawProduct
        (fun actor => originalLocalRow N sample r (slots actor) ops (initial.2 actor))
        (originalLocalRow N sample r base ops initial.1) actors).map
          (installFrozenDraw initial.2 actors) := by
      rw [actual_original_source_draw_tensor N r ops s base slots actors hsep]
      rfl
    _ = _ := (finite_tensor_is_serial_async_program actors hn
      (fun actor => originalLocalRow N sample r (slots actor) ops)
      (originalLocalRow N sample r base ops) initial).symm

#print axioms actual_finite_original_source_async_program
end G1ActualFiniteOriginalEpochAsync
