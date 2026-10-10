import G1SameCoreLiteralSemidirectedTargets
import UnifiedLean.Source.NativeIndependentPairMixture

/-! SAME original-class core assembly with explicit n≥4, positive ORIGINAL
edge/ancestral rates and actual strict-interior inheritance. Input/output are
faithful outer-labelled GALLED semidirected rooted partners, parallel IDs
retained. Literal complete displayed-tree cut families and Q/S are bound by
actual marked switching/deletion paths, not only a rooted target proxy.
All previous opaque CURRENT-root contextual K, SAME registers, original
root calendar history and actual unbounded completion conclusions use this
ONE witness selected before every stochastic quantifier. -/
namespace G1OriginalClassSameCoreAssembly
set_option backward.isDefEq.respectTransparency false
open G1OneSameOriginalCoreAssembly G1OneSameOuterSemidirectedCoreAssembly
open G1SameCoreLiteralSemidirectedTargets G1ExactSemidirectedPartnerAdmission
open UnifiedLean.Source.NativeIndependentPairMixture
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceForestSilentPruning
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore G1ReducedCoreCounts
open G1DecoratedRootBlobRetention G1OriginalDecoratedSpan G1ContextualForestReplacement
open G1ActualDisplayedClusterSplitTransport G1FiniteNormalizationDisplayedTargets
open G1ActualDisplayedQuartetTransport
open G1AcceptedNontrivialSplitTarget G1AcceptedAllCompatibleCircularOrders
open G1ActualDisplayedTreeFamily G1ActualWholeUnrootedCutTreeFamily G1FiniteCoreWholeDisplayedTreeFamilies
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalOriginalExitAsyncStep
open G1CanonicalInitializedWholeCalendarHistory G1CanonicalWholeCalendarSameCompletion
open G1CanonicalOwnTwoInterfaceRuntime G1CanonicalPendingTrueKExposure G1AllOriginalPromotedKLabels
open G1EveryPromotedKInputRealCurrentRoot G1CanonicalOriginalKOnlyActorRow
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open G1PendingBaseCheckpointRecorder G1PendingInterfaceEntryRecorder G1OriginalWholeCausalView G1UnrankedSourceView
open G1ActiveCoreBridgeCohorts G1InitializedFrontierPrefix G1ActualOriginalRootRecordedProgram
open scoped Classical
universe u v w c h o
variable {X : Type w} [Fintype X]

noncomputable def naturalInteriorGamma {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X) (p : HybridProbabilities N) : V → unitInterval :=
  fun v => if hh : N.graph.IsHybrid v then ⟨p.gamma ⟨v,hh⟩,(p.positive _).le,(p.below_one _).le⟩
    else ⟨1/2,by norm_num,by norm_num⟩

theorem actual_natural_gamma_is_original_interior {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X) (p : HybridProbabilities N)
    (h : UnifiedLean.Source.NativeParentRouting.Hybrid N) :
    (naturalInteriorGamma N p h.val : ℝ) = p.gamma h ∧
    0 < (naturalInteriorGamma N p h.val : ℝ) ∧ (naturalInteriorGamma N p h.val : ℝ) < 1 := by
  have he : (naturalInteriorGamma N p h.val : ℝ) = p.gamma h := by simp [naturalInteriorGamma,h.property]
  exact ⟨he,he ▸ p.positive h,he ▸ p.below_one h⟩

theorem actual_one_same_original_class_G1_assembly (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (_hn : 4 ≤ Fintype.card X) (hO : HasGalledOuterSemidirectedPartner O) :
    ∃ (T : Source X) (D : Decoration O T) (hD : Originated O H D),
      HasGalledOuterSemidirectedPartner T ∧ Steps O T ∧ Reduced T ∧ (hybrids T.network).card ≤ 2 * Fintype.card X - 2 ∧
      Fintype.card T.Vertex ≤ 6 * Fintype.card X - 5 ∧ Fintype.card T.Edge ≤ 8 * Fintype.card X - 8 ∧
      SameLiteralSemidirectedTargets O T ∧ SamePhysicalTargets O T ∧ UniformCurrentRootInterface O T D ∧
      (∀ f : O.Edge, O.network.graph.SameBlob O.network.root (O.network.graph.source f) →
        O.network.graph.SameBlob O.network.root (O.network.graph.target f) → ∃ e : T.Edge, D.recipe e = .raw f) ∧
      (∀ (Copy : Type c) [Fintype Copy] [DecidableEq Copy]
        (sample : Copy → X) (register : O.Vertex → Bool) (p : HybridProbabilities O.network)
        (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (history : List (UnrankedView O.Vertex O.Edge Copy)),
        SameCompletedOriginalHistory O H D hD sample register (naturalInteriorGamma O.network p) common r history ∧
        ActualKInputs O H D hD sample register (naturalInteriorGamma O.network p) common r history) := by
  obtain ⟨P,hgalled⟩ := hO
  obtain ⟨T,D,hD,hpartner,steps,reduced,hh,hv,he,targets,interface,raw,law⟩ :=
    actual_one_same_outer_semidirected_core_source_assembly O H ⟨P⟩
  refine ⟨T,D,hD,actual_outer_source_partner_is_galled T hpartner,steps,reduced,hh,hv,he,
    actual_same_rooted_targets_bind_literal_semidirected_targets O T targets,targets,interface,raw,?_⟩
  intro Copy _ _ sample register p common r history
  exact law Copy sample register (naturalInteriorGamma O.network p) common r history

#print axioms actual_one_same_original_class_G1_assembly
end G1OriginalClassSameCoreAssembly
