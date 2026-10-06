import G2StrictClockDecoration

/-!
Derived interval-start safety of the actual original calendar program.
Contributor: dot (OpenAI), 6 October 2026.
The predicate below is discharged from the existing original boundary batch,
epoch support, sorted dates and actual initialization theorems. It is not an
admission assumption for the final physical source.
-/
namespace GProgram.G2.OriginalProgramSafety
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarPhysicalSupport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def SafeSteps (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) : ℝ → List (ProgramStep N) → Code N sample → Prop
  | _,[],_ => True
  | t,.boundary b::ops,s => ∀ d ∈ (boundaryKernel N b s).support, SafeSteps N C r t ops d
  | t,.interval h::ops,s => EpochCompatible N C t (t+(h : ℝ)) (state s) ∧
      ∀ d ∈ (sourceTimeKernel N r h s).support, SafeSteps N C r (t+(h : ℝ)) ops d

lemma safe_boundary_prefix (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ)
    (bs ops : List (ProgramStep N))
    (hbs : ∀ op ∈ bs, ∃ b, op = ProgramStep.boundary b) (s : Code N sample)
    (hnext : ∀ d ∈ (sourceProgram N r bs s).support, SafeSteps N C r t ops d) :
    SafeSteps N C r t (bs++ops) s := by
  induction bs generalizing s with
  | nil =>
      exact hnext s (by simp [sourceProgram])
  | cons op bs ih =>
      obtain ⟨b,hb⟩ := hbs op (List.mem_cons_self)
      subst op
      intro d hd
      apply ih (fun op hop => hbs op (List.mem_cons_of_mem _ hop)) d
      intro e he
      apply hnext e
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨d,hd,he⟩

lemma original_batch_only_boundaries (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) :
    ∀ op ∈ boundaryOperations N C H gamma common a, ∃ b, op = ProgramStep.boundary b := by
  intro op hop
  simp only [boundaryOperations,List.mem_append,List.mem_map] at hop
  rcases hop with ⟨e,_,he⟩ | ⟨v,_,hv⟩
  · exact ⟨_,he.symm⟩
  · exact ⟨_,hv.symm⟩

theorem original_calendar_tail_safe (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (dates : List ℝ) (a : ℝ)
    (hfuture : FutureComplete N C a dates) (hordered : dates.Pairwise (· < ·))
    (hafter : ∀ b ∈ dates, a < b) (s : Code N sample) (hs : AfterNodes N C a (state s)) :
    SafeSteps N C r a (calendarTail N C H gamma common a dates) s := by
  induction dates generalizing a s with
  | nil => trivial
  | cons b bs ih =>
      have hab : a < b := hafter b (List.mem_cons_self)
      have hbs := List.pairwise_cons.mp hordered
      have hgap : ∀ v, a < C.age v → b ≤ C.age v := by
        intro v hv
        rcases List.mem_cons.mp (hfuture v hv) with he | he
        · exact he.ge
        · exact (hbs.1 _ he).le
      have hepoch := after_nodes_to_epoch N C hs hgap
      have hdate : a+(Real.toNNReal (b-a) : ℝ) = b := by
        rw [Real.coe_toNNReal _ (sub_nonneg.mpr hab.le)]
        ring
      simp only [calendarTail,SafeSteps,hdate]
      refine ⟨hepoch,?_⟩
      intro d hd
      have hdep := actual_source_time_epoch_support N C r (Real.toNNReal (b-a)) s hepoch hd
      apply safe_boundary_prefix N C r b (boundaryOperations N C H gamma common b)
        (calendarTail N C H gamma common b bs) (original_batch_only_boundaries N C H gamma common b) d
      intro e he
      have hready := epoch_to_next_ready N C hdep hab.le
      have hafterNodes := actual_original_boundary_batch_support N C H gamma common r b d hready he
      have hfuture' : FutureComplete N C b bs := by
        intro v hv
        rcases List.mem_cons.mp (hfuture v (hab.trans hv)) with he | he
        · exact False.elim ((ne_of_gt hv) he)
        · exact he
      exact ih b hfuture' hbs.2 hbs.1 e hafterNodes

/-- Every interval in the original initialized compiled calendar starts in
its physical original populations at its exact original date. -/
theorem actual_original_program_safe (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    SafeSteps N C r (firstOriginalDate N C) (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register) := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro h
    have hm := original_date_scheduled N C N.root
    rw [h] at hm
    exact List.not_mem_nil hm
  obtain ⟨a,dates,he⟩ := List.exists_cons_of_ne_nil hne
  have hfirst : a = firstOriginalDate N C := by
    have hf := first_compiled_date_is_initial_boundary N C
    simpa only [he,List.getElem_cons_zero] using hf
  have hordered := original_dates_strict N C
  rw [he] at hordered
  have hp := List.pairwise_cons.mp hordered
  have hfuture : FutureComplete N C a dates := by
    intro v hv
    have hm := original_date_scheduled N C v
    rw [he] at hm
    rcases List.mem_cons.mp hm with hm | hm
    · exact False.elim ((ne_of_gt hv) hm)
    · exact hm
  have hready : BoundaryReady N C a (state (initialCode N sample register)) := by
    rw [hfirst]
    exact actual_initial_calendar_boundary N C sample register
  rw [compiledCalendarProgram,he,←hfirst]
  apply safe_boundary_prefix N C r a (boundaryOperations N C H gamma common a)
    (calendarTail N C H gamma common a dates) (original_batch_only_boundaries N C H gamma common a)
    (initialCode N sample register)
  intro d hd
  exact original_calendar_tail_safe N C H gamma common r dates a hfuture hp.2 hp.1 d
    (actual_original_boundary_batch_support N C H gamma common r a _ hready hd)

#print axioms actual_original_program_safe
end GProgram.G2.OriginalProgramSafety
