import G1ActualOriginalBoundaryRootHistory

/-! The chronological root recorder is explicitly the readout of the
inherited ACTUAL sourceStageHistory, not a new desired endpoint/history law.
Every original post-operation checkpoint is extracted from that real trace. -/
namespace G1ActualRootRecordedStageTrace
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1ActualRootBlobPopulationFootprint G1OriginalWholeCausalView
open G1ActualOriginalRootRecordedProgram G1ActualJointStageHistory G1ActualJointProgram G1ContextualForestReplacement
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_source_stage_trace_starts_at_input (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (ops : List (ProgramStep O.network)) (s : Code O.network sample)
    {trace : List (Code O.network sample)} (ht : trace ∈ (sourceStageHistory O.network r ops s).support) :
    trace.head? = some s := by
  cases ops with
  | nil => have he : trace = [s] := by simpa only [sourceStageHistory,PMF.mem_support_pure_iff] using ht
           rw [he]; rfl
  | cons op ops =>
    obtain ⟨d,hd,ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
    obtain ⟨tail,htail,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
    rfl

noncomputable def rootStageTraceResult (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    List (Code O.network sample) → Code O.network sample × List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)
  | [] => (s,history)
  | _::tail => tail.foldl (fun acc d => (d,acc.2 ++ [originalRootBlobView O.network (wholeOriginalView O.network d)])) (s,history)

/-- Exact joint recorder law is derived from the existing actual complete
source trajectory, with every old post-operation root checkpoint retained. -/
theorem actual_original_root_recorder_is_actual_stage_trace (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (ops : List (ProgramStep O.network)) (s : Code O.network sample)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    originalRootRecordedProgram O r ops s history =
      (sourceStageHistory O.network r ops s).map (rootStageTraceResult O s history) := by
  induction ops generalizing s history with
  | nil => simp [originalRootRecordedProgram,sourceStageHistory,rootStageTraceResult,PMF.pure_map]
  | cons op ops ih =>
    simp only [originalRootRecordedProgram,sourceStageHistory,PMF.map_bind]
    apply bind_eq_of_eq_on_support
    intro d hd
    rw [ih,PMF.map_comp]
    apply map_eq_of_eq_on_support
    intro trace ht
    have hs := actual_source_stage_trace_starts_at_input O r ops d ht
    cases trace with
    | nil => cases hs
    | cons first later =>
      have he : first = d := Option.some.inj hs
      subst first
      rfl

/-- The root history readout is literally the prior history followed by the
root observations at ALL successive original source checkpoints. -/
lemma actual_root_stage_trace_history_readout (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy))
    (tail : List (Code O.network sample)) :
    (rootStageTraceResult O s history (s::tail)).2 =
      history ++ tail.map (fun d => originalRootBlobView O.network (wholeOriginalView O.network d)) := by
  induction tail generalizing s history with
  | nil => simp [rootStageTraceResult]
  | cons d tail ih =>
    change (rootStageTraceResult O d (history ++ [originalRootBlobView O.network (wholeOriginalView O.network d)]) (d::tail)).2 = _
    rw [ih]
    simp only [List.map_cons,List.append_assoc,List.singleton_append]

#print axioms actual_original_root_recorder_is_actual_stage_trace
end G1ActualRootRecordedStageTrace
