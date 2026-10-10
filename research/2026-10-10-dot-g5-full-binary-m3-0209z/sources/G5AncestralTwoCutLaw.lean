import G5ObservedCompletedBins
import G5ActualTwoCutPartitionLaw

/-! The original source above its root, exposed by the inherited SAME-ancestral-
interval identity. No new population, rate, register or completion model.
Contributor: dot / OpenAI, 9 October 2026. -/
namespace GProgram.G5.AncestralTwoCutLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceCompletionHarmonic
open GProgram.G2.CalendarFirstAge GProgram.G2.ChronologicalPathReadout
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.SourceFiniteHistory
open GProgram.G5.HiddenRegisterTimedProjectivity GProgram.G5.ObservedBinHistory
open GProgram.G5.TwoCutSourceWord GProgram.G5.TwoCutPartitionDecoder
open GProgram.G5.OriginalProgramSurvival GProgram.G5.EnumeratedTripleRow
open GProgram.G5.SourcePairPersistence GProgram.G5.CompletionPairPersistence
open GProgram.G5.ConstantTagSource GProgram.G5.ThreePhaseCompletion
open GProgram.G5.TwoCutProgramSupport GProgram.G5.ActualRoutingSupport
open GProgram.G5.ObservedCompletedBins
open UnifiedLean.G6.NaturalAncestralCutExtension
open CloudG3.ActualCalendarCutContext CloudG3.ActualCalendarEndpointHistory
open CloudG3.CompleteCalendarJointLaw CloudG3.CompleteCalendarBinReadout
open CloudG3.ActualTailBinRow CloudG6.NaturalPastCompleteObservation
open CloudG6.NaturalCalendarPastAdmission
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable

/-- The previous three-phase proof needs only actual terminal ancestral
support. This exposes that precise reusable premise, then discharges it below. -/
theorem completed_two_cut_tag_kernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hroot : ∀ d ∈ (sourceProgram N r (pre ++ .interval (a+(b+c)) :: post) s).support,
      AncestralRoot N d) :
    let left := offset + (programDuration N pre : ℝ) + (a:ℝ)
    let right := left + (b:ℝ)
    (completedJoint N r (twoCutBin left right) (two_cut_bin_measurable left right)
      (pre ++ .interval (a+(b+c)) :: post) s offset
      (fun x y => twoCutBin left right (M x y))).map Prod.snd =
      twoCutTagKernel N r pre post a b c s offset M := by
  dsimp only
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ measurable_snd,completed_joint_toMeasure]
  have hoff : offset + (programDuration N pre : ℝ) + (a:ℝ) + (b:ℝ) ≤
      offset + (programDuration N (pre ++ .interval (a+(b+c)) :: post) : ℝ) := by
    simp only [program_duration_append,programDuration,NNReal.coe_add]
    have hc := c.coe_nonneg
    have hp := (programDuration N post).coe_nonneg
    linarith
  have htail : ∀ x : ℝ, offset + (programDuration N pre : ℝ) + (a:ℝ) + (b:ℝ) < x →
      twoCutBin (offset + (programDuration N pre : ℝ) + (a:ℝ))
        (offset + (programDuration N pre : ℝ) + (a:ℝ) + (b:ℝ)) x = (2 : Fin 3) := by
    intro x hx
    have hh : offset + (programDuration N pre : ℝ) + (a:ℝ) < x := by
      have hb := b.coe_nonneg
      linarith
    simp [twoCutBin,not_le_of_gt hh,not_le_of_gt hx]
  unfold completeReadout
  rw [actual_complete_joint_source_law N r _ (two_cut_bin_measurable _ _) _ _ hroot _ _
    (2 : Fin 3) hoff htail M,actual_two_cut_source_joint]
  exact PMF.toMeasure_map _ _ measurable_snd

theorem ancestral_three_phase_support (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (reg : V → Bool)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (a b c : ℝ≥0) (d e f : Code N sample)
    (hd : d ∈ (sourceProgram N r
      (compiledCalendarProgram N C H (originalGamma p) common ++ [.interval a])
      (initialCode N sample reg)).support)
    (he : e ∈ (sourceProgram N r [.interval b] d).support)
    (hf : f ∈ (sourceProgram N r [.interval c] e).support) : AncestralRoot N f := by
  have hs : f ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H (originalGamma p) common ++ [.interval a]) ++
        ([.interval b] ++ [.interval c])) (initialCode N sample reg)).support := by
    rw [sourceProgram_append]
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨d,hd,?_⟩
    rw [sourceProgram_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨e,he,hf⟩
  have hs' : f ∈ (sourceProgram N r
      (compiledCalendarProgram N C H (originalGamma p) common ++
        .interval a :: .interval b :: .interval c :: [])
      (initialCode N sample reg)).support := by simpa only [List.append_assoc,List.singleton_append] using hs
  rw [← original_two_cut_program_eq] at hs'
  exact original_extended_ancestral_support N C sample H p common r reg (a+(b+c)) hs'

theorem ancestral_two_cut_partition_row (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (reg : V → Bool)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (a b c : ℝ≥0) (i : Fin 3 ≃ Copy)
    (offset : ℝ) (M : Copy → Copy → ℝ) :
    (twoCutTagKernel N r (compiledCalendarProgram N C H (originalGamma p) common)
      [] a b c (initialCode N sample reg) offset M).map
      (fun B => (binPartition i 0 B,binPartition i 1 B)) =
    (sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) common ++ [.interval a])
      (initialCode N sample reg)).bind (fun d =>
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
  trans (sourceProgram N r [.interval c] e).bind
    (fun _ => PMF.pure (indexedPartition N i d,indexedPartition N i e))
  · apply bind_eq_of_support
    intro f hf
    rw [PMF.map_comp]
    have hroot := ancestral_three_phase_support N C sample reg H p common r a b c d e f hd he hf
    trans (completionKernel N r f).map (fun _ => (indexedPartition N i d,indexedPartition N i e))
    · apply map_eq_of_support
      intro g hg
      exact three_phase_partition_decoder N (initialCode N sample reg) d e g _ i
        i.injective hs hde (completion_all_pairs N r f g hroot hg)
    · exact PMF.map_const _ _
  · exact PMF.bind_const _ _

theorem actual_observed_ancestral_two_cut_law (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (a b : ℝ≥0) (i : Fin 3 ≃ Copy) :
    let ops := compiledCalendarProgram N C H (originalGamma p) common
    let left := firstOriginalDate N C + (programDuration N ops : ℝ) + (a:ℝ)
    let right := left + (b:ℝ)
    (naturalObservedFullLaw N C sample H p common r).map
      (fun o => let B := observedAgeBins (twoCutBin left right) o
        (binPartition i 0 B,binPartition i 1 B)) =
    ((originalProgramLaw N sample p r (ops ++ [.interval a])).bind (fun d =>
      (sourceProgram N r [.interval b] d).map (fun e =>
        (indexedPartition N i d,indexedPartition N i e)))).toMeasure := by
  dsimp only
  let ops := compiledCalendarProgram N C H (originalGamma p) common
  let left := firstOriginalDate N C + (programDuration N ops : ℝ) + (a:ℝ)
  let right := left + (b:ℝ)
  have hb := observed_age_bins_measurable (Copy := Copy) (twoCutBin left right)
    (two_cut_bin_measurable left right)
  have hr : Measurable (fun B : Copy → Copy → Fin 3 =>
      (binPartition i 0 B,binPartition i 1 B)) := measurable_of_countable _
  change (naturalObservedFullLaw N C sample H p common r).map
    ((fun B => (binPartition i 0 B,binPartition i 1 B)) ∘ observedAgeBins (twoCutBin left right)) = _
  rw [← Measure.map_map hr hb,actual_observed_completed_bins_extended N C sample H p common r
    (twoCutBin left right) (two_cut_bin_measurable left right) (a+(b+0)),PMF.toMeasure_map _ _ hr]
  congr 1
  unfold naturalCompletedJoint originalProgramLaw
  rw [PMF.map_bind,PMF.map_bind,PMF.bind_bind]
  congr 1
  funext reg
  rw [completed_two_cut_tag_kernel N r ops [] a b 0 (initialCode N sample reg)
    (firstOriginalDate N C) (leafAgeMatrix N C sample)
    (fun d hd => original_extended_ancestral_support N C sample H p common r reg (a+(b+0)) hd)]
  exact ancestral_two_cut_partition_row N C sample reg H p common r a b 0 i _ _

#print axioms completed_two_cut_tag_kernel
#print axioms ancestral_three_phase_support
#print axioms ancestral_two_cut_partition_row
#print axioms actual_observed_ancestral_two_cut_law
end GProgram.G5.AncestralTwoCutLaw
