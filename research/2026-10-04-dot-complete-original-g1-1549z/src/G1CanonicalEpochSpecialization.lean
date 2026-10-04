import G1CanonicalEpochBlockBinding

/-! Derived canonical calendar blocks at original node dates. Contributor:
dot, 2026-10-03. No original source operations or demographic rates change. -/
namespace G1CanonicalEpochSpecialization
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceFiniteProjection
open G1OriginalEpochPanelSilence G1OriginalNodeBatchBinding G1OriginalExitBatchBinding
open G1CanonicalEpochBlockBinding G1CanonicalThreeEpochList G1CanonicalComponentSegment
open G1CompactSourceComposition
open G1OriginalCalendarDecomposition G1InitializedFrontierPrefix
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

noncomputable def canonicalEpochBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (D U : V) (exits : List E) : List (ProgramStep N) :=
  nodeOperations N C H gamma common (C.age D) ++
    stopBeforeTail N C H gamma common (C.age U) (C.age D) (afterDate N C (C.age D)) ++
    exits.map (fun e => .boundary (.exit e))

/-- The original date ordering, node membership and duration hypotheses are
DERIVED for the canonical block from physical original endpoints. -/
theorem actual_canonical_epoch_block_binding (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (D U : V) (hr : D ≠ N.root) (hdate : C.age D < C.age U)
    (hsource : ∀ e ∈ incomingEdges N D, N.graph.source e = U)
    (es canonical : List E) (hcover : ∀ e ∈ incomingEdges N D, e ∈ es)
    (hcanonical : ∀ e ∈ incomingEdges N D, e ∈ canonical)
    (s : Code N sample) (hs : AtNodePanel (state s) keep D) :
    (sourceProgram N r (canonicalEpochBlock N C H gamma common D U es) s).map (projection N keep) =
      (sourceProgram N r ([.boundary (originalNodeOperation N H gamma common D),
        .interval (Real.toNNReal (C.age U-C.age D))] ++
        canonical.map (fun e => .boundary (.exit e))) s).map (projection N keep) := by
  unfold canonicalEpochBlock nodeOperations
  apply actual_node_epoch_exit_block_binding N C H gamma common r keep
    (Finset.univ.filter (fun v : V => C.age v = C.age D)).toList D hr
    (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩))
    _ (original_after_ordered N C _) (C.age D) (C.age U) (original_after_member N C _ U hdate)
    _ U rfl hsource es canonical hcover hcanonical s hs
  intro c hc
  exact ((List.mem_filter.mp hc).2 |> of_decide_eq_true).le

lemma actual_original_exits_cover (N : RootedBinary V E X) (C : Calendar N.graph) (D U : V)
    (hsource : ∀ e ∈ incomingEdges N D, N.graph.source e = U) :
    ∀ e ∈ incomingEdges N D, e ∈ originalExits N C (C.age U) := by
  intro e he
  exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg C.age (hsource e he)⟩)

theorem actual_canonical_epoch_block_exit_support (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (D U : V) (hr : D ≠ N.root) (hdate : C.age D < C.age U)
    (hsource : ∀ e ∈ incomingEdges N D, N.graph.source e = U)
    (es canonical : List E) (hcover : ∀ e ∈ incomingEdges N D, e ∈ es)
    (hcanonical : ∀ e ∈ incomingEdges N D, e ∈ canonical)
    (s : Code N sample) (hs : AtNodePanel (state s) keep D)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r (canonicalEpochBlock N C H gamma common D U es) s).support) :
    AtNodePanel (state d) keep U := by
  exact actual_block_exit_support_from_row N r keep _ _ s U
    (actual_canonical_epoch_block_binding N C H gamma common r keep D U hr hdate hsource
      es canonical hcover hcanonical s hs)
    (fun z hz => actual_compact_epoch_block_exit_support N H gamma common r keep D U hr _ canonical
      hsource hcanonical s hs hz) hd

end G1CanonicalEpochSpecialization
