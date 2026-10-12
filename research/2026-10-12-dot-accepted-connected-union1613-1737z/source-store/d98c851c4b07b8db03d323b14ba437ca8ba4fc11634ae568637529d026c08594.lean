import G5TaggedWordProgram
import G5CompletionPairPersistence
import G5ObservedBinHistory

/-! Exact phase reduction of the constructed original observed-bin kernel.
Contributor: dot / OpenAI,9 October2026. -/
namespace GProgram.G5.ThreePhaseCompletion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.G6.BinHistory
open GProgram.G5.SourcePairPersistence GProgram.G5.CompletionPairPersistence
open GProgram.G5.ConstantTagSource GProgram.G5.TaggedWordProgram
open GProgram.G5.TwoCutSourceWord GProgram.G5.ObservedBinHistory
open CloudG3.CompleteCalendarJointLaw
open scoped Classical NNReal
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma actual_constant_phase_then_completion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (tag : Tag)
    (s : Code N sample) (B : Copy → Copy → Tag) :
    ((sourceProgram N r ops s).map (fun d => (d,tagUpdate N s d tag B))).bind
      (jointTailKernel N r tag) =
    (sourceProgram N r ops s).bind (fun d =>
      (completionKernel N r d).map (fun e => (e,tagUpdate N s e tag B))) := by
  rw [PMF.bind_map]
  apply bind_eq_of_support
  intro d hd
  change (completionKernel N r d).map (fun e =>
    (e,tagUpdate N d e tag (tagUpdate N s d tag B))) = _
  apply map_eq_of_support
  intro e he
  congr 1
  exact same_bin_update_comp N s d e tag B
    (source_program_relation N r ops s d hd) (completion_relation N r d e he)

/-- The actual observed-bin kernel is a literal prefix state, one future
ordinary source epoch, then the original remaining program and completion.
All later tags collapse to phase2 without assuming independence. -/
theorem actual_two_cut_kernel_phases (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    let left := offset + (GProgram.G2.ChronologicalPathReadout.programDuration N pre : ℝ) + (a:ℝ)
    let right := left + (b:ℝ)
    twoCutTagKernel N r pre post a b c s offset M =
      (sourceProgram N r (pre ++ [.interval a]) s).bind (fun d =>
        (sourceProgram N r [.interval b] d).bind (fun e =>
          (sourceProgram N r (.interval c :: post) e).bind (fun f =>
            (completionKernel N r f).map (fun g =>
              tagUpdate N e g (2 : Fin 3)
                (tagUpdate N d e (1 : Fin 3)
                  (tagUpdate N s d (0 : Fin 3) (fun x y => twoCutBin left right (M x y)))))))) := by
  dsimp only
  unfold twoCutTagKernel
  dsimp only
  rw [actual_history_reader_is_wordProgram,actual_two_cut_three_phase]
  simp only [PMF.bind_bind,PMF.map_bind]
  congr 1
  funext d
  congr 1
  funext e
  rw [← PMF.map_bind,actual_constant_phase_then_completion]
  simp only [PMF.map_bind,PMF.map_comp]
  rfl

#print axioms actual_constant_phase_then_completion
#print axioms actual_two_cut_kernel_phases
end GProgram.G5.ThreePhaseCompletion
