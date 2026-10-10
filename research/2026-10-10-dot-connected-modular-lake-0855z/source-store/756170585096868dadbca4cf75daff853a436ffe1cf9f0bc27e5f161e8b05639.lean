import G1OriginalUnrankedActorOpenClose
import G1PendingActorInterfaceCommutation

/-! The ACTUAL original private boundary is a genuine localStep of the
pending actor algebra on complete ORIGINAL unranked coordinates. The base
and every other actor coordinate have derived supported identity rows. -/
namespace G1ActualOriginalPrivateAsyncStep
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceBoundaryKernels
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1ActiveCoreBridgeCohorts G1OriginalActorOperationOwnership
open G1CanonicalActorLifecycleCompiler G1TaggedOriginalCalendar G1PrivateActorLifetimeAdmission
open G1ActualActorBoundaryFrames G1ExteriorBoundarySilence G1UnrankedSourceView
open G1ContextualForestReplacement G1ActualOriginalUnrankedLocalKernel G1ActualJointOpaqueContext G1PendingActorInterfaceCommutation
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalAsyncProjection (O : Source.{u,v,w} X)
    {Copy I : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (base : Finset Copy) (slots : I → Finset Copy) (s : Code O.network sample) :
    UnrankedView O.Vertex O.Edge Copy × (I → UnrankedView O.Vertex O.Edge Copy) :=
  (unrankedView (selectedView (state s) base),fun i => unrankedView (selectedView (state s) (slots i)))

lemma actual_owned_boundary_other_panel_support (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (event : OriginalEvent O) (howner : eventActor O H D hD event = some actor)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (keep : Finset Copy)
    (hdis : Disjoint (originalInsideCopies O sample (actorInput O D actor)) keep)
    {d : Code O.network sample} (hd : d ∈ (sourceProgram O.network r [eraseEvent O H gamma common event] s).support) :
    unrankedView (selectedView (state d) keep) = unrankedView (selectedView (state s) keep) := by
  have hout : ∀ x ∈ keep, ¬ O.network.graph.DReach (actorInput O D actor) (O.network.leaf (sample x)) := by
    intro x hx hdesc
    exact Finset.disjoint_left.mp hdis (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdesc⟩) hx
  have frame (op : BoundaryOperation O.network) (ha : PanelAbsent O.network op (state s) keep)
      (hb : d ∈ (boundaryKernel O.network op s).support) :
      unrankedView (selectedView (state d) keep) = unrankedView (selectedView (state s) keep) :=
    congrArg (fun v => unrankedView v.val) (actual_untouched_boundary_panel O.network op s keep ha hb)
  cases event with
  | interval _ _ => cases howner
  | node v =>
    apply frame _ _ (by simpa [sourceProgram,sourceProgramStep,eraseEvent] using hd)
    intro x hx heq
    rw [G1OriginalNodeBatchBinding.actual_node_touched_site] at heq
    exact actual_outside_actor_location_excluded O H D hD actor s x (hout x hx)
      (heq ▸ actual_owned_node_member O H D hD v actor howner)
  | exit e =>
    apply frame _ _ (by simpa [sourceProgram,sourceProgramStep,eraseEvent] using hd)
    intro x hx heq
    change copyLocation (state s) x = .edge e at heq
    exact actual_outside_actor_location_excluded O H D hD actor s x (hout x hx)
      (heq ▸ actual_owned_exit_member O H D hD e actor howner)

/-- Genuine source-to-AsyncOperation localStep binding. Physical original
cohort footprints supply all untouched coordinates; equality is derived. -/
theorem actual_original_private_boundary_async_step (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (event : OriginalEvent O) (howner : eventActor O H D hD event = some actor)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample)
    (base : Finset Copy) (slots : BridgeActor T → Finset Copy)
    (hbase : Disjoint (originalInsideCopies O sample (actorInput O D actor)) base)
    (hothers : ∀ other ≠ actor, Disjoint (originalInsideCopies O sample (actorInput O D actor)) (slots other)) :
    (sourceProgram O.network r [eraseEvent O H gamma common event] s).map (originalAsyncProjection O base slots) =
      asyncStep (.localStep actor (originalLocalRow O.network sample r (slots actor) [eraseEvent O H gamma common event]))
        (originalAsyncProjection O base slots s) := by
  let initial := originalAsyncProjection O base slots s
  calc
    _ = (sourceProgram O.network r [eraseEvent O H gamma common event] s).map (fun d =>
        (initial.1,Function.update initial.2 actor (unrankedView (selectedView (state d) (slots actor))))) := by
      apply map_eq_of_eq_on_support
      intro d hd
      apply Prod.ext
      · exact actual_owned_boundary_other_panel_support O H D hD actor event howner gamma common r s base hbase hd
      · funext other
        by_cases he : other = actor
        · subst other
          simp only [originalAsyncProjection,Function.update_self]
        · change unrankedView (selectedView (state d) (slots other)) =
            Function.update initial.2 actor (unrankedView (selectedView (state d) (slots actor))) other
          rw [Function.update_of_ne he]
          exact actual_owned_boundary_other_panel_support O H D hD actor event howner gamma common r s _ (hothers other he) hd
    _ = ((sourceProgram O.network r [eraseEvent O H gamma common event] s).map
        (fun d => unrankedView (selectedView (state d) (slots actor)))).map
      (fun value => (initial.1,Function.update initial.2 actor value)) := by rw [PMF.map_comp]; rfl
    _ = _ := by rw [actual_original_local_source_row]; rfl

#print axioms actual_original_private_boundary_async_step
end G1ActualOriginalPrivateAsyncStep
