import UnifiedLean.Source.SourceCalendarPhysicalSupport

/-!
# Initialized ORIGINAL graph/calendar agenda has physical source support

Contributor: dot, 2026-10-02. Initializes actual original sample copies at their
original tips and executes the constructed full sorted original-date agenda.
The entire PMF support is calendar-compatible across intervals/boundaries, and
every final copy occupies the SAME original ancestral population. None of these
location/initialization facts is passed as a desired source-law field. Physical
exponential-clock path identification and final unranked/timed observation
binding remain subsequent original-source obligations.
-/
namespace UnifiedLean.Source.SourceInitializedCalendar
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceProgramTransport
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Completeness of a generated future-date tail, not a stochastic law field. -/
def FutureComplete (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) (dates : List ℝ) : Prop :=
  ∀ v : V, a < C.age v → C.age v ∈ dates

def finalDate : ℝ → List ℝ → ℝ
  | a,[] => a
  | _,b::bs => finalDate b bs

lemma after_nodes_to_epoch (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : ℝ} {s : State V E Copy} (hs : AfterNodes N C a s)
    (gap : ∀ v : V, a < C.age v → b ≤ C.age v) : EpochCompatible N C a b s := by
  intro x
  have hr := hs.1.1 x
  cases hp : copyLocation s x with
  | node v => exact gap v (hs.2 x v hp)
  | edge e =>
      rw [hp] at hr
      exact ⟨hr.1,gap (N.graph.source e) (hs.1.2 x e hp)⟩
  | rootPopulation v =>
      rw [hp] at hr
      exact hr

lemma epoch_to_next_ready (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : ℝ} {s : State V E Copy} (hs : EpochCompatible N C a b s) (hab : a ≤ b) :
    BoundaryReady N C b s := by
  intro x
  have h := hs x
  cases hp : copyLocation s x with
  | node v =>
      rw [hp] at h
      exact h
  | edge e =>
      rw [hp] at h
      exact ⟨h.1.trans hab,h.2⟩
  | rootPopulation v =>
      rw [hp] at h
      exact ⟨h.1,h.2.trans hab⟩

/-- Every whole sorted-agenda tail preserves physical calendar support.
Future completeness is obtained from the original finite date set below. -/
theorem actual_calendar_tail_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (dates : List ℝ) (a : ℝ)
    (hfuture : FutureComplete N C a dates) (hordered : dates.Pairwise (· < ·))
    (hafter : ∀ b ∈ dates, a < b) (s : Code N sample)
    (hs : AfterNodes N C a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (calendarTail N C H gamma common a dates) s).support) :
    AfterNodes N C (finalDate a dates) (state d) ∧ ∀ v : V, C.age v ≤ finalDate a dates := by
  induction dates generalizing a s with
  | nil =>
      have hds : d = s := by simpa only [calendarTail,sourceProgram,PMF.mem_support_pure_iff] using hd
      subst d
      refine ⟨hs,?_⟩
      intro v
      by_contra hv
      exact List.not_mem_nil (hfuture v (lt_of_not_ge hv))
  | cons b bs ih =>
      have hab : a < b := hafter b (by simp)
      have hbs := List.pairwise_cons.mp hordered
      have hgap : ∀ v : V, a < C.age v → b ≤ C.age v := by
        intro v hv
        rcases List.mem_cons.mp (hfuture v hv) with he | he
        · exact he.ge
        · exact (hbs.1 _ he).le
      have hepoch := after_nodes_to_epoch N C hs hgap
      change d ∈ ((sourceTimeKernel N r (Real.toNNReal (b-a)) s).bind
        (sourceProgram N r (boundaryOperations N C H gamma common b ++
          calendarTail N C H gamma common b bs))).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have hmepoch := actual_source_time_epoch_support N C r (Real.toNNReal (b-a)) s hepoch hm
      rw [sourceProgram_append] at hdm
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdm
      have hzphysical := actual_original_boundary_batch_support N C H gamma common r b m
        (epoch_to_next_ready N C hmepoch hab.le) hz
      have hnext : FutureComplete N C b bs := by
        intro v hv
        rcases List.mem_cons.mp (hfuture v (hab.trans hv)) with he | he
        · exact False.elim ((ne_of_gt hv) he)
        · exact he
      exact ih b hnext hbs.2 hbs.1 z hzphysical hdz

/-- Actual source initialization uses original sampled tip IDs and the supplied
ORIGINAL register, never a refitted/pruned physical source. -/
noncomputable def initialCode (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) : Code N sample :=
  admittedCode N sample (initial N sample register) (initial_source_valid N sample register)

/-- Exact support of the complete initialized ORIGINAL graph/calendar program.
All remaining current genealogies occupy the actual supplied root population. -/
theorem initialized_original_calendar_ancestral_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register)).support) :
    ∀ x : Copy, copyLocation (state d) x = .rootPopulation N.root := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro h
    have hm := original_date_scheduled N C N.root
    rw [h] at hm
    exact List.not_mem_nil hm
  obtain ⟨a,dates,heq⟩ := List.exists_cons_of_ne_nil hne
  have hfirst : a = firstOriginalDate N C := by
    have h := first_compiled_date_is_initial_boundary N C
    simpa only [heq,List.getElem_cons_zero] using h
  have hordered := original_dates_strict N C
  rw [heq] at hordered
  have hp := List.pairwise_cons.mp hordered
  have hfuture : FutureComplete N C a dates := by
    intro v hv
    have hm := original_date_scheduled N C v
    rw [heq] at hm
    rcases List.mem_cons.mp hm with he | he
    · exact False.elim ((ne_of_gt hv) he)
    · exact he
  have hready : BoundaryReady N C a (state (initialCode N sample register)) := by
    rw [hfirst]
    exact actual_initial_calendar_boundary N C sample register
  rw [compiledCalendarProgram,heq,sourceProgram_append] at hd
  obtain ⟨s,hs,hds⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hstart := actual_original_boundary_batch_support N C H gamma common r a _ hready hs
  have hfinal := actual_calendar_tail_support N C H gamma common r dates a hfuture hp.2 hp.1 s hstart hds
  intro x
  have hreadyFinal := hfinal.1.1.1 x
  cases hloc : copyLocation (state d) x with
  | node v => exact False.elim (not_lt_of_ge (hfinal.2 v) (hfinal.1.2 x v hloc))
  | edge e => exact False.elim (not_lt_of_ge (hfinal.2 (N.graph.source e)) (hfinal.1.1.2 x e hloc))
  | rootPopulation v =>
      rw [hloc] at hreadyFinal
      exact congrArg Location.rootPopulation hreadyFinal.1

#print axioms after_nodes_to_epoch
#print axioms actual_calendar_tail_support
#print axioms initialized_original_calendar_ancestral_support
end UnifiedLean.Source.SourceInitializedCalendar
