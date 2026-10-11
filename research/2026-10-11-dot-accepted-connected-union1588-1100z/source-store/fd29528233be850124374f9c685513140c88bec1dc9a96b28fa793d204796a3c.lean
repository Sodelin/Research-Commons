import G1CanonicalFiniteActiveEpochAdmission
import G1ActualFiniteOriginalQuotientTensor

/-! The chronological core actor compiler's complete ORIGINAL causal epoch
row is the derived finite quotient tensor, at the real post-node frontier.
Actual separation/purity/cover are discharged; no raw ordered state interface
or supplied desired product/kernel law is used. -/
namespace G1CanonicalWholeOriginalActiveEpoch
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1CanonicalComponentSegment G1OriginalEpochPanelCompression
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1NaturalActiveActorFrontier
open G1CanonicalFiniteActiveEpochAdmission G1ActiveCoreBridgeCohorts G1ActualFinitePanelProgramTensor
open G1ActualJointProgram G1ActualJointEpoch G1JointUnrankedForestAssembly G1FiniteOriginalCausalCoordinates
open G1ActualFiniteOriginalQuotientTensor G1OriginalWholeCausalView G1PrivateActorLifetimeAdmission
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_real_post_node_active_actor_region (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) (node : O.Vertex)
    (ha : T.calendar.Active (O.calendar.age node) actor.val)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (G1InitializedFrontierPrefix.actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age node)) (initialCode O.network sample register)).support)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r
      (nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)) s).support) :
    ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
      SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state d) x) := by
  apply actual_safe_program_actor_region O H D hD actor gamma common r _ _ s _
    (actual_real_frontier_active_actor_region O H D hD actor node ha sample register gamma common r hs) hd
  intro op hop
  obtain ⟨v,hv,heq⟩ := List.mem_map.mp hop
  exact Or.inr (Or.inr ⟨v,heq.symm⟩)

lemma actual_finite_epoch_pure_support {V E Copy Y : Type*}
    [Fintype V] [Fintype E] [Fintype Y] [Fintype Copy] [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
    (N : RootedBinary V E Y) {sample : Copy → Y} (r : PositivePairRates E) (duration : ℝ≥0)
    (keeps : List (Finset Copy)) (s : Code N sample)
    (hsep : PanelSeparatedAgenda N r [.interval duration] keeps s)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r [.interval duration] s).support) :
    PureOriginalPanels (state d) keeps := by
  have hdTime : d ∈ (sourceTimeKernel N r duration s).support := by simpa [sourceProgram,sourceProgramStep] using hd
  induction keeps with
  | nil => trivial
  | cons keep keeps ih =>
    exact ⟨population_separated_pruned_panels (state d) d.property.forest keep (panelUnion keeps)
      (actual_epoch_separation N r keep (panelUnion keeps) duration s hsep.1.1 hdTime),ih hsep.2⟩

/-- This is the ACTUAL whole original labelled unranked state row for any
finite active actor family after one original date's exact node batch. Its
base complement and every physical tensor/purity admission are derived. -/
theorem actual_canonical_whole_original_active_epoch_row (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actors : List (BridgeActor T)) (hnodup : actors.Nodup) (node : O.Vertex)
    (hactive : ∀ actor ∈ actors, T.calendar.Active (O.calendar.age node) actor.val)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (duration : ℝ≥0) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (G1InitializedFrontierPrefix.actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age node)) (initialCode O.network sample register)).support)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r
      (nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)) s).support) :
    (sourceProgram O.network r [.interval duration] d).map (wholeOriginalView O.network) =
      (originalQuotientPanelProduct O.network r [.interval duration] d
        (activeOriginalPanelFamily (activeOriginalPanels O D sample actors))).map
      (joinOriginalPanelViews (state d).register (activeOriginalPanelFamily (activeOriginalPanels O D sample actors))) := by
  have hsep : PanelSeparatedAgenda O.network r [.interval duration]
      (activeOriginalPanelFamily (activeOriginalPanels O D sample actors)) d := by
    apply actual_finite_active_regions_epoch_admission O H D hD actors hnodup node hactive sample r duration d
    intro actor hm
    exact actual_real_post_node_active_actor_region O H D hD actor node (hactive actor hm) sample register gamma common r hs hd
  exact actual_active_family_whole_original_source_row O.network r [.interval duration] d _ hsep
    (fun z hz => actual_finite_epoch_pure_support O.network r duration _ d hsep hz)

#print axioms actual_canonical_whole_original_active_epoch_row
end G1CanonicalWholeOriginalActiveEpoch
