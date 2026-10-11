import G1CanonicalInitializedWholeCalendarHistory
import G1SourceMacroActualCompletion

/-! The concrete whole chronological original interpreter followed by SAME
actual unbounded ancestral completion. All completion admissions come from
actual initialized calendar support, and all original root checkpoints remain
joint with the full completed original unranked causal output. -/
namespace G1CanonicalWholeCalendarSameCompletion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1CanonicalOriginalExitAsyncStep G1CanonicalInitializedWholeCalendarHistory
open G1ActualOriginalRootRecordedProgram G1ActualOriginalBoundaryRootHistory
open G1PendingBaseCheckpointRecorder G1PendingActorInterfaceCommutation
open G1WholeFinitePendingPromotion G1ActualJointProgram
open G1UnrankedSourceView G1OriginalWholeCausalView G1SourceMacroActualCompletion
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- Exact source-derived continuation on the complete original base quotient.
The empty future is literal: every original calendar operation has already
run, and the inherited actual completion kernel remains unbounded. -/
noncomputable def canonicalCompletedBaseHistory (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (initial : Code O.network sample)
    (base : UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) :=
  (actualCompletedTerminal O.network r [] initial id base.1).map (fun final => (final,base.2))

/-- Full initialized original source/calendar and actual ancestral completion
equal the concrete chronological interpreter's SAME completion, JOINTLY with
EVERY old post-operation root/ancestral checkpoint. -/
theorem actual_whole_original_calendar_same_completed_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val))
      (initialCode O.network sample register) history).bind
      (fun result => (completionKernel O.network r result.1).map (fun final => (wholeOriginalView O.network final,result.2))) =
    (asyncProgram (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)
      (withBaseHistory history (canonicalExitProjection O H D hD
        (UnifiedLean.Source.SourceCalendarCompatibility.firstOriginalDate O.network O.calendar) []
        (initialCode O.network sample register)))).bind
      (fun out => canonicalCompletedBaseHistory O r (initialCode O.network sample register) out.1) := by
  let actual := originalRootRecordedProgram O r
    (compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val))
    (initialCode O.network sample register) history
  have hnext (result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy))
      (hr : result ∈ actual.support) :
      (completionKernel O.network r result.1).map (fun final => (wholeOriginalView O.network final,result.2)) =
      canonicalCompletedBaseHistory O r (initialCode O.network sample register) (wholeOriginalView O.network result.1,result.2) := by
    have hroot : AncestralRoot O.network result.1 :=
      initialized_original_calendar_ancestral_support O.network O.calendar sample register H
        (fun h => gamma h.val) (fun h => common h.val) r
        (actual_original_root_recorded_support_endpoint O r _ _ history hr)
    have hc := actual_completed_terminal_at_source O.network r [] (initialCode O.network sample register) result.1
      (fun d hd => by
        have he : d = result.1 := by simpa only [sourceProgram,PMF.mem_support_pure_iff] using hd
        subst d; exact hroot) id
    simpa only [canonicalCompletedBaseHistory,sourceProgram,PMF.pure_bind,PMF.map_comp,Function.comp_def,id_eq] using
      (congrArg (fun p => p.map (fun final => (final,result.2))) hc).symm
  calc
    _ = actual.bind (fun result => canonicalCompletedBaseHistory O r (initialCode O.network sample register)
        (wholeOriginalView O.network result.1,result.2)) := bind_eq_of_eq_on_support _ _ _ hnext
    _ = (actual.map (fun result => (wholeOriginalView O.network result.1,result.2))).bind
        (canonicalCompletedBaseHistory O r (initialCode O.network sample register)) := by rw [PMF.bind_map]; rfl
    _ = _ := by
      rw [actual_initialized_whole_original_base_history O H D hD sample register gamma common r history,PMF.bind_map]
      rfl

/-- Actual finite all-actor promotion also preserves this entire completed
joint history row. Identification of its fused blocks with each true K label
is a subsequent compiler/word binding, not a hypothesis of this theorem. -/
theorem actual_promoted_whole_original_same_completed_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val))
      (initialCode O.network sample register) history).bind
      (fun result => (completionKernel O.network r result.1).map (fun final => (wholeOriginalView O.network final,result.2))) =
    (asyncProgram (promoteEveryActor (Finset.univ.toList)
      (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r))
      (withBaseHistory history (canonicalExitProjection O H D hD
        (UnifiedLean.Source.SourceCalendarCompatibility.firstOriginalDate O.network O.calendar) []
        (initialCode O.network sample register)))).bind
      (fun out => canonicalCompletedBaseHistory O r (initialCode O.network sample register) out.1) := by
  rw [actual_whole_original_calendar_same_completed_history O H D hD sample register gamma common r history,
    actual_every_actor_promotion_row]

#print axioms actual_whole_original_calendar_same_completed_history
#print axioms actual_promoted_whole_original_same_completed_history
end G1CanonicalWholeCalendarSameCompletion
