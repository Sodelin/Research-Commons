import UnifiedLean.G6.PrivateCalendarBoundarySupport
import UnifiedLean.G6.PrivateRegisterCalendarPrefix
import UnifiedLean.Source.SourceNaturalInitialization

/-!
UNCHECKED actual initialized native upper-prefix PHYSICAL support consumer.
CLOUD-PRIVATE-SUPPORT-SOL-2330Z, 7 October 2026. Separate draft outside165.
Uses relative deterministic agenda completeness, never the full FutureComplete
assumption for a truncated prefix. Final natural initialization supplies its
original register PMF and derives initial BoundaryReady from firstOriginalDate.
No desired kernel equality, erasure, physical-support field or history law.
-/
namespace UnifiedLean.G6.PrivateCalendarPrefixSupport
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterCalendar
open UnifiedLean.G6.PrivateRegisterCalendarPrefix
open UnifiedLean.G6.PrivateCalendarBoundarySupport
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- A deterministic date-window property, derived from the actual agenda in
the initialized theorem. It does not require dates above the stopping guard. -/
def RelativeFutureComplete (N : RootedBinary V E X) (C : Calendar N.graph)
    (a guard : ℝ) (dates : List ℝ) : Prop :=
  ∀ v : V, a < C.age v → C.age v ≤ guard → C.age v ∈ dates

/-- Actual time-kernel and COMPLETE actual boundary batches derive support
through a relatively complete strict prefix. There is no all-vertex final-age
conclusion, which would be false for a truncated agenda. -/
theorem actual_partial_calendar_tail_support (N : RootedBinary V E X)
    (C : Calendar N.graph) {sample : Copy → X} (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (dates : List ℝ) (a guard : ℝ)
    (hfuture : RelativeFutureComplete N C a guard dates)
    (hordered : dates.Pairwise (· < ·)) (hafter : ∀ b ∈ dates, a < b)
    (hbounded : ∀ b ∈ dates, b ≤ guard) (s : Code N sample)
    (hs : AfterNodes N C a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (calendarTail N C H gamma common a dates) s).support) :
    AfterNodes N C (finalDate a dates) (state d) := by
  induction dates generalizing a s with
  | nil =>
      have hds : d = s := by
        simpa only [calendarTail, sourceProgram, PMF.mem_support_pure_iff] using hd
      subst d
      exact hs
  | cons b bs ih =>
      have hab : a < b := hafter b List.mem_cons_self
      have hbs := List.pairwise_cons.mp hordered
      have hgap : ∀ v : V, a < C.age v → b ≤ C.age v := by
        intro v hv
        by_cases hguard : C.age v ≤ guard
        · rcases List.mem_cons.mp (hfuture v hv hguard) with he | he
          · exact he.ge
          · exact (hbs.1 _ he).le
        · exact (hbounded b List.mem_cons_self).trans (lt_of_not_ge hguard).le
      have hepoch := after_nodes_to_epoch N C hs hgap
      change d ∈ ((sourceTimeKernel N r (Real.toNNReal (b-a)) s).bind
        (sourceProgram N r (boundaryOperations N C H gamma common b ++
          calendarTail N C H gamma common b bs))).support at hd
      obtain ⟨m, hm, hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have hmepoch := actual_source_time_epoch_support N C r
        (Real.toNNReal (b-a)) s hepoch hm
      rw [sourceProgram_append] at hdm
      obtain ⟨z, hz, hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdm
      have hzphysical := actual_original_boundary_batch_support N C H gamma common
        r b m (epoch_to_next_ready N C hmepoch hab.le) hz
      have hnext : RelativeFutureComplete N C b guard bs := by
        intro v hv hguard
        rcases List.mem_cons.mp (hfuture v (hab.trans hv) hguard) with he | he
        · exact False.elim ((ne_of_gt hv) he)
        · exact he
      have hboundNext : ∀ t ∈ bs, t ≤ guard := by
        intro t ht
        exact hbounded t (List.mem_cons_of_mem b ht)
      exact ih b hnext hbs.2 hbs.1 hboundNext z hzphysical hdz

theorem finalDate_append_guard (a guard : ℝ) (pre : List ℝ) :
    finalDate a (pre ++ [guard]) = guard := by
  induction pre generalizing a with
  | nil => rfl
  | cons b pre ih => exact ih b

/-- Every original vertex date in the actual initial window is present; no
future completeness assumption is inserted at the truncated endpoint. -/
theorem actual_prefix_tail_relative_complete (N : RootedBinary V E X)
    (C : Calendar N.graph) (a guard : ℝ) (middle post : List ℝ)
    (hsplit : sortedOriginalDates N C = a :: (middle ++ guard :: post)) :
    RelativeFutureComplete N C a guard (middle ++ [guard]) := by
  have hsplit' : sortedOriginalDates N C = (a :: middle) ++ guard :: post := by
    simpa only [List.cons_append] using hsplit
  intro v hva hvg
  have hm := original_date_scheduled N C v
  rw [hsplit] at hm
  rcases List.mem_cons.mp hm with he | hm
  · exact False.elim ((ne_of_gt hva) he)
  · rcases List.mem_append.mp hm with hm | hm
    · exact List.mem_append.mpr (Or.inl hm)
    · rcases List.mem_cons.mp hm with he | hm
      · exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr he))
      · have hgt := original_dates_suffix_gt N C guard (a :: middle) post
          hsplit' (C.age v) hm
        exact False.elim (not_lt_of_ge hvg hgt)

theorem actual_prefix_dates_bounded (N : RootedBinary V E X)
    (C : Calendar N.graph) (guard : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    ∀ d ∈ pre ++ [guard], d ≤ guard := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact original_dates_prefix_le N C guard pre post hsplit d hd
  · have heq : d = guard := List.mem_singleton.mp hd
    subst d
    exact le_rfl

theorem actual_prefix_dates_strict (N : RootedBinary V E X)
    (C : Calendar N.graph) (guard : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    (pre ++ [guard]).Pairwise (· < ·) := by
  have hfull := original_dates_strict N C
  rw [hsplit] at hfull
  have hfull' : ((pre ++ [guard]) ++ post).Pairwise (· < ·) := by
    simpa only [List.append_assoc, List.singleton_append] using hfull
  exact (List.pairwise_append.mp hfull').1

/-- The initialized native prefix THROUGH the complete retained guard batch
has AfterNodes at that guard. Initial BoundaryReady is derived, not a premise. -/
theorem initialized_original_prefix_after_nodes (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (guard : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (match pre ++ [guard] with
       | [] => []
       | a :: dates => boundaryOperations N C H gamma common a ++
           calendarTail N C H gamma common a dates)
      (initialCode N sample register)).support) :
    AfterNodes N C guard (state d) := by
  cases pre with
  | nil =>
      have heq : sortedOriginalDates N C = guard :: post := by
        simpa only [List.nil_append] using hsplit
      have hfirst : guard = firstOriginalDate N C := by
        have h := first_compiled_date_is_initial_boundary N C
        simpa only [heq, List.getElem_cons_zero] using h
      have hready : BoundaryReady N C guard (state (initialCode N sample register)) := by
        rw [hfirst]
        exact actual_initial_calendar_boundary N C sample register
      have hb : d ∈ (sourceProgram N r
          (boundaryOperations N C H gamma common guard)
          (initialCode N sample register)).support := by
        simpa only [List.nil_append, calendarTail, List.append_nil] using hd
      exact actual_original_boundary_batch_support N C H gamma common
        r guard _ hready hb
  | cons a middle =>
      have heq : sortedOriginalDates N C = a :: (middle ++ guard :: post) := by
        simpa only [List.cons_append] using hsplit
      have hfirst : a = firstOriginalDate N C := by
        have h := first_compiled_date_is_initial_boundary N C
        simpa only [heq, List.getElem_cons_zero] using h
      have hready : BoundaryReady N C a (state (initialCode N sample register)) := by
        rw [hfirst]
        exact actual_initial_calendar_boundary N C sample register
      have hprefix : (a :: (middle ++ [guard])).Pairwise (· < ·) := by
        simpa only [List.cons_append] using
          actual_prefix_dates_strict N C guard (a :: middle) post hsplit
      have hp := List.pairwise_cons.mp hprefix
      have hfuture := actual_prefix_tail_relative_complete N C a guard middle post heq
      have hbound := actual_prefix_dates_bounded N C guard (a :: middle) post hsplit
      have htailBound : ∀ t ∈ middle ++ [guard], t ≤ guard := by
        intro t ht
        apply hbound t
        simpa only [List.cons_append] using List.mem_cons_of_mem a ht
      change d ∈ (sourceProgram N r
        (boundaryOperations N C H gamma common a ++
          calendarTail N C H gamma common a (middle ++ [guard]))
        (initialCode N sample register)).support at hd
      rw [sourceProgram_append] at hd
      obtain ⟨s, hs, hds⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have hstart := actual_original_boundary_batch_support N C H gamma common
        r a _ hready hs
      have hfinal := actual_partial_calendar_tail_support N C H gamma common r
        (middle ++ [guard]) a guard hfuture hp.2 hp.1 htailBound s hstart hds
      simpa only [finalDate_append_guard] using hfinal

/-- Actual once-drawn original finite-product register marginalization. This
is the native initialized-prefix expression, with no new law wrapper. -/
theorem natural_initialized_prefix_after_nodes (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (guard : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) {d : Code N sample}
    (hd : d ∈ ((originalRegisterPMF N p).bind (fun register =>
      sourceProgram N r
        (match pre ++ [guard] with
         | [] => []
         | a :: dates => boundaryOperations N C H (originalGamma p) common a ++
             calendarTail N C H (originalGamma p) common a dates)
        (initialCode N sample register))).support) :
    AfterNodes N C guard (state d) := by
  obtain ⟨register, _, hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact initialized_original_prefix_after_nodes N C sample register H
    (originalGamma p) common r guard pre post hsplit hdr

theorem natural_initialized_prefix_private_absence (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (guard : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post)
    (P : Finset V) (Q : Finset E) (hP : ∀ v ∈ P, C.age v ≤ guard)
    (hQ : ∀ e ∈ Q, C.age (N.graph.source e) ≤ guard) (hroot : N.root ∉ P)
    {d : Code N sample}
    (hd : d ∈ ((originalRegisterPMF N p).bind (fun register =>
      sourceProgram N r
        (match pre ++ [guard] with
         | [] => []
         | a :: dates => boundaryOperations N C H (originalGamma p) common a ++
             calendarTail N C H (originalGamma p) common a dates)
        (initialCode N sample register))).support) :
    AfterNodes N C guard (state d) ∧
      (∀ x : Copy, ∀ v ∈ P, copyLocation (state d) x ≠ .node v) ∧
      (∀ x : Copy, ∀ e ∈ Q, copyLocation (state d) x ≠ .edge e) ∧
      (∀ x : Copy, ∀ v ∈ P, copyLocation (state d) x ≠ .rootPopulation v) := by
  have hafter := natural_initialized_prefix_after_nodes N C sample H p common
    r guard pre post hsplit hd
  exact ⟨hafter, after_nodes_no_private_node N C guard P (state d) hafter hP,
    after_nodes_no_private_edge N C guard Q (state d) hafter hQ,
    after_nodes_no_private_root N C guard P (state d) hafter hroot⟩

private theorem date_split (a : ℝ) (dates : List ℝ) :
    a ∈ dates → ∃ pre post, dates = pre ++ a :: post := by
  induction dates with
  | nil => simp
  | cons d dates ih =>
      intro h
      rcases List.mem_cons.mp h with h | h
      · subst d
        exact ⟨[], dates, rfl⟩
      · obtain ⟨pre, post, heq⟩ := ih h
        exact ⟨d :: pre, post, by simp only [List.cons_append, heq]⟩

/-- A retained ORIGINAL upper vertex constructs its actual initialized prefix
and private absence, without an assumed BoundaryReady/support/kernel field. -/
theorem natural_guarded_prefix_private_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (u : V) (P : Finset V) (Q : Finset E) (hP : ∀ v ∈ P, C.age v ≤ C.age u)
    (hQ : ∀ e ∈ Q, C.age (N.graph.source e) ≤ C.age u) (hroot : N.root ∉ P) :
    ∃ pre post, sortedOriginalDates N C = pre ++ C.age u :: post ∧
      ∀ d : Code N sample, d ∈ ((originalRegisterPMF N p).bind (fun register =>
        sourceProgram N r
          (match pre ++ [C.age u] with
           | [] => []
           | a :: dates => boundaryOperations N C H (originalGamma p) common a ++
               calendarTail N C H (originalGamma p) common a dates)
          (initialCode N sample register))).support →
        AfterNodes N C (C.age u) (state d) ∧
          (∀ x : Copy, ∀ v ∈ P, copyLocation (state d) x ≠ .node v) ∧
          (∀ x : Copy, ∀ e ∈ Q, copyLocation (state d) x ≠ .edge e) ∧
          (∀ x : Copy, ∀ v ∈ P, copyLocation (state d) x ≠ .rootPopulation v) := by
  obtain ⟨pre, post, hsplit⟩ := date_split (C.age u)
    (sortedOriginalDates N C) (original_date_scheduled N C u)
  refine ⟨pre, post, hsplit, ?_⟩
  intro d hd
  exact natural_initialized_prefix_private_absence N C sample H p common r
    (C.age u) pre post hsplit P Q hP hQ hroot hd

#print axioms actual_partial_calendar_tail_support
#print axioms actual_prefix_tail_relative_complete
#print axioms initialized_original_prefix_after_nodes
#print axioms natural_initialized_prefix_after_nodes
#print axioms natural_initialized_prefix_private_absence
#print axioms natural_guarded_prefix_private_support

end UnifiedLean.G6.PrivateCalendarPrefixSupport
