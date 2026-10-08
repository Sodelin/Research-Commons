import NaturalOneBinForestCount
import UnifiedLean.G6.PrivateCalendarPrefixSupport

/-!
Contributor: Cloud Sol /root/source_backend_review_sol, 8 October 2026.
EXPERIMENTAL SOURCE/HAND consumer; every new body compiler UNCHECKED.
Literal initialized ORIGINAL sorted prefix THROUGH the complete guard batch,
then its actual next date interval. No desired law, physical-support field,
entering independence, removed population carrier, or Python equality input.
Outside the frozen179 compiler input; no compiler/runtime in this lane.
-/
namespace CloudG6.NaturalGuardOneBinForest
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.G6.PrivateRegisterCalendarPrefix UnifiedLean.G6.PrivateCalendarPrefixSupport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.ChronologicalPathReadout
open CloudG3.CompleteCalendarBinReadout CloudG3.CompleteCalendarJointLaw
open CloudG3.ActualCalendarCutContext
open CloudG6.TaggedSourceIteration CloudG6.NaturalCalendarPastAdmission
open CloudG6.NaturalOneBinForestCount
open scoped Classical NNReal
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

/-- An abbreviation of the actual compiler expression, not a new kernel. -/
noncomputable def guardPrefix (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (guard : ℝ) (pre : List ℝ) : List (ProgramStep N) :=
  match pre ++ [guard] with
  | [] => []
  | a :: dates => boundaryOperations N C H gamma common a ++
      calendarTail N C H gamma common a dates

private theorem boundary_list_duration (N : RootedBinary V E X) {A : Type*}
    (as : List A) (f : A → BoundaryOperation N) :
    programDuration N (as.map (fun a => .boundary (f a))) = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa only [List.map_cons, programDuration] using ih

theorem boundary_batch_duration (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) :
    programDuration N (boundaryOperations N C H gamma common a) = 0 := by
  unfold boundaryOperations
  rw [program_duration_append, boundary_list_duration, boundary_list_duration]
  rfl

theorem calendar_tail_duration (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) (dates : List ℝ)
    (hordered : (a :: dates).Pairwise (· < ·)) :
    (programDuration N (calendarTail N C H gamma common a dates) : ℝ) =
      finalDate a dates - a := by
  induction dates generalizing a with
  | nil => simp [calendarTail, programDuration, finalDate]
  | cons b bs ih =>
      have hp := List.pairwise_cons.mp hordered
      have hab : a < b := hp.1 b List.mem_cons_self
      have ht := ih b hp.2
      simp only [calendarTail, programDuration, program_duration_append,
        boundary_batch_duration, zero_add, NNReal.coe_add]
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr hab.le), ht]
      simp only [finalDate]
      ring

/-- The native accumulated interval duration reaches the physical guard
exactly, even if it is the first original date. Boundary ties cost no time. -/
theorem actual_guard_prefix_date (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (guard : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    firstOriginalDate N C +
      (programDuration N (guardPrefix N C H gamma common guard pre) : ℝ) = guard := by
  cases pre with
  | nil =>
      have heq : sortedOriginalDates N C = guard :: post := by
        simpa only [List.nil_append] using hsplit
      have hfirst : guard = firstOriginalDate N C := by
        have h := first_compiled_date_is_initial_boundary N C
        simpa only [heq, List.getElem_cons_zero] using h
      simp [guardPrefix, calendarTail, programDuration, boundary_batch_duration, hfirst]
  | cons a middle =>
      have heq : sortedOriginalDates N C = a :: (middle ++ guard :: post) := by
        simpa only [List.cons_append] using hsplit
      have hfirst : a = firstOriginalDate N C := by
        have h := first_compiled_date_is_initial_boundary N C
        simpa only [heq, List.getElem_cons_zero] using h
      have hord : (a :: (middle ++ [guard])).Pairwise (· < ·) := by
        simpa only [List.cons_append] using
          actual_prefix_dates_strict N C guard (a :: middle) post hsplit
      have ht := calendar_tail_duration N C H gamma common a (middle ++ [guard]) hord
      rw [finalDate_append_guard] at ht
      have hd : (programDuration N
          (guardPrefix N C H gamma common guard (a :: middle)) : ℝ) = guard - a := by
        change (programDuration N (boundaryOperations N C H gamma common a ++
          calendarTail N C H gamma common a (middle ++ [guard])) : ℝ) = guard - a
        rw [program_duration_append, boundary_batch_duration, zero_add]
        exact ht
      rw [hd, ← hfirst]
      ring

/-- The appended interval is literally the next interval in the original
compiled agenda. Its upper batch, including every tie, remains in the suffix. -/
theorem actual_guard_next_program_split (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (guard next : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) :
    compiledCalendarProgram N C H gamma common =
      (guardPrefix N C H gamma common guard pre ++
        [.interval (Real.toNNReal (next - guard))]) ++
      (boundaryOperations N C H gamma common next ++
        calendarTail N C H gamma common next post) := by
  have h := compiledCalendarProgram_split_at_guard N C H gamma common guard pre
    (next :: post) hsplit
  simpa only [guardPrefix, calendarTail, List.append_assoc, List.singleton_append] using h

/-- No original node date is strictly between two actual consecutive dates. -/
theorem actual_next_date_gap (N : RootedBinary V E X) (C : Calendar N.graph)
    (guard next : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) :
    guard < next ∧ ∀ v : V, guard < C.age v → next ≤ C.age v := by
  have hfull := original_dates_strict N C
  rw [hsplit] at hfull
  have ht := (List.pairwise_append.mp hfull).2.1
  have hg := List.pairwise_cons.mp ht
  have hn := List.pairwise_cons.mp hg.2
  refine ⟨hg.1 next List.mem_cons_self, ?_⟩
  intro v hv
  have hm := original_date_scheduled N C v
  rw [hsplit] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact False.elim (not_lt_of_ge
      (original_dates_prefix_le N C guard pre (next :: post) hsplit (C.age v) hm) hv)
  · rcases List.mem_cons.mp hm with he | hm
    · exact False.elim ((ne_of_gt hv) he)
    · rcases List.mem_cons.mp hm with he | hm
      · exact he.ge
      · exact (hn.1 _ hm).le

/-- The actual correlated bin history has exactly the original initialized
Code marginal. This is derived from the actual recorded calendar law. -/
theorem natural_past_code_marginal (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N)) :
    (naturalPastJoint N C sample p r bin hbin ops).map Prod.fst =
      (originalRegisterPMF N p).bind (fun register =>
        sourceProgram N r ops (initialCode N sample register)) := by
  have hrow (register : V → Bool) :
      (calendarJointPMF N r bin hbin ops (initialCode N sample register)
        (firstOriginalDate N C) (leafAgeMatrix N C sample)).map Prod.fst =
        sourceProgram N r ops (initialCode N sample register) := by
    apply PMF.toMeasure_injective
    rw [← PMF.toMeasure_map _ measurable_fst, calendar_joint_pmf_toMeasure]
    exact actual_calendar_joint_code N r bin hbin ops (initialCode N sample register)
      (firstOriginalDate N C) (leafAgeMatrix N C sample)
  unfold naturalPastJoint
  rw [PMF.map_bind]
  simp_rw [hrow]

/-- Natural initialization and COMPLETE original guard operations derive
AfterNodes for each supported entering Code jointly with its SAME old bins. -/
theorem natural_guard_past_after_nodes (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (guard : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post)
    {q : TaggedCode N sample Tag}
    (hq : q ∈ (naturalPastJoint N C sample p r bin hbin
      (guardPrefix N C H (originalGamma p) common guard pre)).support) :
    AfterNodes N C guard (state q.1) := by
  have hcode : q.1 ∈ ((naturalPastJoint N C sample p r bin hbin
      (guardPrefix N C H (originalGamma p) common guard pre)).map Prod.fst).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨q, hq, rfl⟩
  rw [natural_past_code_marginal] at hcode
  exact natural_initialized_prefix_after_nodes N C sample H p common r guard pre post
    hsplit (by simpa only [guardPrefix] using hcode)

/-- All original Locations remain physically admitted through the genuine
next gap. This does not erase an active original child edge or outside node. -/
theorem natural_guard_past_epoch (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (guard next : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    {q : TaggedCode N sample Tag}
    (hq : q ∈ (naturalPastJoint N C sample p r bin hbin
      (guardPrefix N C H (originalGamma p) common guard pre)).support) :
    AfterNodes N C guard (state q.1) ∧ EpochCompatible N C guard next (state q.1) := by
  have ha := natural_guard_past_after_nodes N C sample H p common r bin hbin guard pre
    (next :: post) hsplit hq
  exact ⟨ha, after_nodes_to_epoch N C ha (actual_next_date_gap N C guard next pre post hsplit).2⟩

/-- Every actual count row has the same physical epoch support, independently
of the count value; this is not a desired numerical transition equality. -/
theorem natural_guard_count_row_epoch (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (guard next : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    {q : TaggedCode N sample Tag}
    (hq : q ∈ (naturalPastJoint N C sample p r bin hbin
      (guardPrefix N C H (originalGamma p) common guard pre)).support)
    (k : ℕ) {d : Code N sample} (hd : d ∈ (sourceIteration N r k q.1).support) :
    EpochCompatible N C guard next (state d) := by
  exact actual_source_iteration_epoch_support N C r k q.1
    (natural_guard_past_epoch N C sample H p common r bin hbin guard next pre post hsplit hq).2 hd

/-- Actual natural ORIGINAL clock prefix, actual next-date interval and SAME
full all-Location tagged forest/register readout. The code, rates, copy cap,
current-owner routing and once-drawn COMMON register are unchanged. -/
theorem actual_guard_one_bin_forest_count [Nonempty Copy]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (guard next : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (tag : Tag) (hconst : ∀ a : ℝ, guard < a → a < next → bin a = tag) :
    (naturalPastJoint N C sample p r bin hbin
      (guardPrefix N C H (originalGamma p) common guard pre ++
        [.interval (Real.toNNReal (next - guard))])).map (forestReadout N) =
      (naturalPastJoint N C sample p r bin hbin
        (guardPrefix N C H (originalGamma p) common guard pre)).bind
          (oneBinForestCount N r tag (Real.toNNReal (next - guard))) := by
  have hdate := actual_guard_prefix_date N C H (originalGamma p) common guard pre
    (next :: post) hsplit
  have hgap := (actual_next_date_gap N C guard next pre post hsplit).1
  apply actual_natural_past_one_bin_forest_count N C sample p r bin hbin
    (guardPrefix N C H (originalGamma p) common guard pre)
    (Real.toNNReal (next - guard)) tag
  intro a ha hb
  rw [hdate] at ha hb
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hgap.le)] at hb
  apply hconst a ha
  linarith

end CloudG6.NaturalGuardOneBinForest
