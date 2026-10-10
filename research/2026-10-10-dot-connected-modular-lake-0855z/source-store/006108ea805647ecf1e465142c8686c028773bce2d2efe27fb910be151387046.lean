import G5ThreePhaseCompletion
import G5TwoCutProgramSupport
import G5TwoCutPartitionDecoder
import G5ActualRoutingSupport

/-! Original initialized calendar two-cut partition joint law, obtained from
its completed observed age bins. Contributor: dot / OpenAI, 9 October 2026. -/
namespace GProgram.G5.ActualTwoCutPartitionLaw
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.G6.BinHistory
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompatibility
open GProgram.G5.SourcePairPersistence GProgram.G5.CompletionPairPersistence
open GProgram.G5.ConstantTagSource GProgram.G5.ThreePhaseCompletion
open GProgram.G5.TwoCutProgramSupport GProgram.G5.TwoCutPartitionDecoder
open GProgram.G5.ObservedBinHistory GProgram.G5.EnumeratedTripleRow
open GProgram.G5.ActualRoutingSupport GProgram.G5.OriginalProgramSurvival
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The original completed two-cut observation has precisely the actual
prefix/future-epoch joint partition law. The later calendar and ancestral
completion integrate out; no conditional independence premise is supplied. -/
theorem actual_initialized_two_cut_partition_law (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (reg : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (hwhole : compiledCalendarProgram N C H gamma common = pre ++ .interval (a+(b+c)) :: post)
    (i : Fin 3 ≃ Copy) (offset : ℝ) (M : Copy → Copy → ℝ) :
    (twoCutTagKernel N r pre post a b c (initialCode N sample reg) offset M).map
      (fun B => (binPartition i 0 B,binPartition i 1 B)) =
    (sourceProgram N r (pre ++ [.interval a]) (initialCode N sample reg)).bind (fun d =>
      (sourceProgram N r [.interval b] d).map (fun e =>
        (indexedPartition N i d,indexedPartition N i e))) := by
  rw [actual_two_cut_kernel_phases]
  simp only [PMF.map_bind]
  apply bind_eq_of_support
  intro d hd
  rw [← PMF.bind_pure_comp]
  apply bind_eq_of_support
  intro e he
  have hs := singleton_ancestor_injective N (initialCode N sample reg)
    (actual_initial_singleton_selected N sample Finset.univ reg)
  have hde := source_program_relation N r [.interval b] d e he
  trans (sourceProgram N r (.interval c :: post) e).bind
    (fun _ => PMF.pure (indexedPartition N i d,indexedPartition N i e))
  · apply bind_eq_of_support
    intro f hf
    rw [PMF.map_comp]
    have hroot := actual_three_phase_ancestral_support N C sample reg H gamma common r
      pre post a b c hwhole d e f hd he hf
    trans (completionKernel N r f).map (fun _ =>
      (indexedPartition N i d,indexedPartition N i e))
    · apply map_eq_of_support
      intro g hg
      exact three_phase_partition_decoder N (initialCode N sample reg) d e g _ i
        i.injective hs hde (completion_all_pairs N r f g hroot hg)
    · exact PMF.map_const _ _
  · exact PMF.bind_const _ _

/-- Mixing retains one original register across both cuts. -/
theorem actual_natural_two_cut_partition_pmf (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (hwhole : compiledCalendarProgram N C H (originalGamma p) common =
      pre ++ .interval (a+(b+c)) :: post)
    (i : Fin 3 ≃ Copy) (offset : ℝ) (M : Copy → Copy → ℝ) :
    ((originalRegisterPMF N p).bind (fun reg =>
      twoCutTagKernel N r pre post a b c (initialCode N sample reg) offset M)).map
        (fun B => (binPartition i 0 B,binPartition i 1 B)) =
    (originalProgramLaw N sample p r (pre ++ [.interval a])).bind (fun d =>
      (sourceProgram N r [.interval b] d).map (fun e =>
        (indexedPartition N i d,indexedPartition N i e))) := by
  rw [PMF.map_bind]
  unfold originalProgramLaw
  rw [PMF.bind_bind]
  congr 1
  funext reg
  exact actual_initialized_two_cut_partition_law N C sample reg H (originalGamma p)
    common r pre post a b c hwhole i offset M

#print axioms actual_natural_two_cut_partition_pmf
#print axioms actual_initialized_two_cut_partition_law
end GProgram.G5.ActualTwoCutPartitionLaw
