import G1ActualOriginalExitRootCheckpoint

/-! An actual source-program wrapper records every post-operation original
root-blob checkpoint, using the SAME genuine sourceProgramStep at each step.
Its unrecorded endpoint is proved to be the inherited actual sourceProgram. -/
namespace G1ActualOriginalRootRecordedProgram
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1ActualRootBlobPopulationFootprint G1OriginalWholeCausalView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalRootRecordedProgram (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) : List (ProgramStep O.network) → Code O.network sample →
      List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy) →
      PMF (Code O.network sample × List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy))
  | [],s,history => PMF.pure (s,history)
  | op::ops,s,history => (sourceProgramStep O.network r op s).bind (fun d =>
      originalRootRecordedProgram O r ops d
        (history ++ [originalRootBlobView O.network (wholeOriginalView O.network d)]))

/-- The recorder uses exactly the actual original source endpoint law;
chronological history is additional state, not an independently fitted law. -/
theorem actual_original_root_recorded_endpoint (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (ops : List (ProgramStep O.network)) (s : Code O.network sample)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r ops s history).map Prod.fst = sourceProgram O.network r ops s := by
  induction ops generalizing s history with
  | nil => simp [originalRootRecordedProgram,sourceProgram,PMF.pure_map]
  | cons op ops ih =>
    simp only [originalRootRecordedProgram,sourceProgram,PMF.map_bind]
    simp_rw [ih]

lemma actual_original_root_recorded_append (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (first last : List (ProgramStep O.network)) (s : Code O.network sample)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    originalRootRecordedProgram O r (first ++ last) s history =
      (originalRootRecordedProgram O r first s history).bind (fun next => originalRootRecordedProgram O r last next.1 next.2) := by
  induction first generalizing s history with
  | nil => simp [originalRootRecordedProgram,PMF.pure_bind]
  | cons op ops ih =>
    simp only [List.cons_append,originalRootRecordedProgram,PMF.bind_bind]
    simp_rw [ih]

#print axioms actual_original_root_recorded_endpoint
end G1ActualOriginalRootRecordedProgram
