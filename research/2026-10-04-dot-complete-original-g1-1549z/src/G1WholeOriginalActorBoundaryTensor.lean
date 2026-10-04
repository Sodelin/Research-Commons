import G1CanonicalWholeOriginalActiveEpoch

/-! Every actual original boundary has the finite complete ORIGINAL quotient
coordinate tensor row. The physical family separation derives from actual
neutral original actor regions, and final forest purity is derived from the
boundary's real support. Actor-close delivery may meet base populations. -/
namespace G1WholeOriginalActorBoundaryTensor
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1ActualJointProgram G1ActualFinitePanelProgramTensor
open G1CanonicalActorLifecycleCompiler G1OriginalActorOperationOwnership G1ActiveCoreBridgeCohorts
open G1CanonicalFiniteActiveEpochAdmission G1JointUnrankedForestAssembly G1JointForestPreservation
open G1ActualFiniteOriginalQuotientTensor G1FiniteOriginalCausalCoordinates G1OriginalWholeCausalView
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_single_operation_agenda_independent {V E Copy Y : Type*}
    [Fintype V] [Fintype E] [Fintype Y] [Fintype Copy] [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
    (N : RootedBinary V E Y) {sample : Copy → Y} (r : PositivePairRates E)
    (left right : ProgramStep N) (keeps : List (Finset Copy)) (s : Code N sample) :
    PanelSeparatedAgenda N r [left] keeps s ↔ PanelSeparatedAgenda N r [right] keeps s := by
  induction keeps with
  | nil => rfl
  | cons keep keeps ih => simp [PanelSeparatedAgenda,SeparatedAgenda,ih]

lemma actual_single_boundary_pure_support {V E Copy Y : Type*}
    [Fintype V] [Fintype E] [Fintype Y] [Fintype Copy] [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
    (N : RootedBinary V E Y) {sample : Copy → Y} (r : PositivePairRates E) (op : BoundaryOperation N)
    (keeps : List (Finset Copy)) (s : Code N sample)
    (hsep : PanelSeparatedAgenda N r [.boundary op] keeps s)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r [.boundary op] s).support) :
    PureOriginalPanels (state d) keeps := by
  have hboundary : d ∈ (boundaryKernel N op s).support := by simpa [sourceProgram,sourceProgramStep] using hd
  induction keeps with
  | nil => trivial
  | cons keep keeps ih =>
    exact ⟨actual_boundary_pruned_panel_separation N op s keep (panelUnion keeps)
      (population_separated_pruned_panels (state s) s.property.forest keep (panelUnion keeps) hsep.1.1)
      hboundary,ih hsep.2⟩

/-- The whole actual original causal boundary row, without an ordered/raw
actor interface. Closing outputs may meet the base after this last boundary;
no post-close population separation restriction is imposed. -/
theorem actual_whole_original_actor_boundary_row (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actors : List (BridgeActor T))
    (hnodup : actors.Nodup) (witness : O.Vertex)
    (hactive : ∀ actor ∈ actors, T.calendar.Active (O.calendar.age witness) actor.val)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (op : BoundaryOperation O.network)
    (hregion : ∀ actor ∈ actors, ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
      SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x)) :
    (sourceProgram O.network r [.boundary op] s).map (wholeOriginalView O.network) =
      (originalQuotientPanelProduct O.network r [.boundary op] s
        (activeOriginalPanelFamily (activeOriginalPanels O D sample actors))).map
      (joinOriginalPanelViews (state s).register (activeOriginalPanelFamily (activeOriginalPanels O D sample actors))) := by
  have hsep : PanelSeparatedAgenda O.network r [.boundary op]
      (activeOriginalPanelFamily (activeOriginalPanels O D sample actors)) s := by
    apply (actual_single_operation_agenda_independent O.network r (.interval 0) (.boundary op) _ s).mp
    exact actual_finite_active_regions_epoch_admission O H D hD actors hnodup witness hactive sample r 0 s hregion
  exact actual_active_family_whole_original_source_row O.network r [.boundary op] s _ hsep
    (fun d hd => actual_single_boundary_pure_support O.network r op _ s hsep hd)

#print axioms actual_whole_original_actor_boundary_row
end G1WholeOriginalActorBoundaryTensor
