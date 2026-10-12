import G5OriginalEpochChart
import NaturalAncestralCutExtension

/-! Physical-age and actual posterior placement for the original root and
every finite older cut. Contributor: dot / OpenAI, 9 October 2026. -/
namespace GProgram.G5.RootCutChart
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.ChronologicalPathReadout GProgram.G2.CompleteTimedSupport
open GProgram.G2.OriginalProgramSafety
open GProgram.G5.OriginalEpochChart GProgram.G5.OriginalProgramSurvival
open GProgram.G5.OriginalSelectedPosterior GProgram.G5.EnumeratedPosteriorGerm
open GProgram.G5.EnumeratedTripleRow GProgram.G5.ActualConditionalPartition
open GProgram.G5.ActualFrozenTripleRow GProgram.G5.TriplePartitionReadout
open GProgram.G5.FrozenTripleAnalyticSupport GProgram.G5.FrozenTriplePolynomialKernel
open UnifiedLean.G6.NaturalAncestralCutExtension
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma finalDate_le {a bound : ℝ} (dates : List ℝ)
    (ha : a ≤ bound) (hb : ∀ b ∈ dates, b ≤ bound) : finalDate a dates ≤ bound := by
  induction dates generalizing a with
  | nil => exact ha
  | cons b bs ih => exact ih (hb b (by simp)) (fun c hc => hb c (by simp [hc]))

/-- The finite calendar ends exactly at the ORIGINAL root age. -/
theorem original_program_end_is_root (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) :
    firstOriginalDate N C + (programDuration N (compiledCalendarProgram N C H gamma common) : ℝ) =
      C.age N.root := by
  apply le_antisymm
  · have hne : sortedOriginalDates N C ≠ [] := by
      intro he
      have hm := original_date_scheduled N C N.root
      rw [he] at hm
      exact List.not_mem_nil hm
    obtain ⟨a,dates,he⟩ := List.exists_cons_of_ne_nil hne
    have hf : a = firstOriginalDate N C := by
      simpa only [he,List.getElem_cons_zero] using first_compiled_date_is_initial_boundary N C
    have hd := duration_boundaries N (boundaryOperations N C H gamma common a)
      (original_batch_only_boundaries N C H gamma common a)
    have ho : (a::dates).Pairwise (· < ·) := by rw [←he]; exact original_dates_strict N C
    rw [compiledCalendarProgram,he,duration_append,hd,zero_add,←hf,
      calendar_tail_duration_exact N C H gamma common a dates ho]
    have hm : ∀ b ∈ a::dates, b ≤ C.age N.root := by
      intro b hb
      have hb' : b ∈ originalDates N C := by
        simpa only [←he,sortedOriginalDates,Finset.mem_sort] using hb
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hb'
      exact original_root_latest N C v
    exact finalDate_le dates (hm a (by simp)) (fun b hb => hm b (by simp [hb]))
  · exact original_program_reaches_root N C H gamma common

noncomputable def rootPast (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (t : ℝ) : List (ProgramStep N) :=
  compiledCalendarProgram N C H (originalGamma p) common ++ [.interval (Real.toNNReal (t-C.age N.root))]

theorem root_past_exact_age (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (t : ℝ) (ht : C.age N.root ≤ t) :
    firstOriginalDate N C + (programDuration N (compiledCalendarProgram N C H (originalGamma p) common) : ℝ) +
      (Real.toNNReal (t-C.age N.root) : ℝ) = t := by
  rw [original_program_end_is_root,Real.coe_toNNReal _ (sub_nonneg.mpr ht)]
  ring

theorem actual_root_past_support (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (t : ℝ) (d : Code N sample)
    (hd : d ∈ (originalProgramLaw N sample p r (rootPast N C H p common t)).support) :
    AncestralRoot N d := by
  obtain ⟨reg,_,hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact original_extended_ancestral_support N C sample H p common r reg _ hdr

theorem actual_root_posterior_support (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (t : ℝ)
    (s : ActualSeed N (originalTripleCodePosterior N sample p r (rootPast N C H p common t))) :
    AncestralRoot N s.val := by
  have hd := ((PMF.mem_support_filter_iff
    (actual_full_code_event_witness N sample p r Finset.univ (rootPast N C H p common t))).mp s.property).2
  exact actual_root_past_support N C sample H p common r t s.val hd

/-- Every posterior component uses the SAME actual original ancestral
population and the original positive ancestral rate. -/
theorem actual_root_ratio_mixture (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (t : ℝ) (u : ℝ≥0) (i : Fin 3 ≃ Copy) (gene : Fin 5) :
    let past := rootPast N C H p common t
    (((originalProgramLaw N sample p r past).bind (fun d =>
      (sourceProgram N r [.interval u] d).map (fun e =>
        (indexedPartition N i d,indexedPartition N i e)))) (0,gene) *
      ((originalProgramLaw N sample p r past).toOuterMeasure
        {d | indexedPartition N i d = 0})⁻¹).toReal =
    frozenMixture (actualSeedWeight N (originalTripleCodePosterior N sample p r past))
      (fun _ => triplePopulationRate r (fun _ => none))
      (fun _ => ancestorPartition (fun _ => (none : Option E))) (u : ℝ) gene := by
  dsimp only
  exact actual_joint_ratio_frozen_mixture N sample p r _ i (fun _ _ => none)
    (fun s x => actual_root_posterior_support N C sample H p common r t s x) u gene

#print axioms original_program_end_is_root
#print axioms root_past_exact_age
#print axioms actual_root_past_support
#print axioms actual_root_posterior_support
#print axioms actual_root_ratio_mixture
end GProgram.G5.RootCutChart
