import UnifiedLean.G6.PrivateRegisterCalendar

/-!
UNCHECKED lower causal ORIGINAL calendar-prefix no-private-read consumer.
CLOUD-PRIVATE-CALENDAR-SOL-2304Z, 7 October 2026. Separate new draft; imports
the namespace-only Calendar derivative a639cd69, leaving reviewed 83c intact.
Private node ages are strictly above the retained lower guard. The actual
initial sorted agenda through that guard, including every tied operation,
derives NoPrivateWordRead; no desired word/kernel law is a premise.
No physical population support, natural-factorization or marked-history claim.
Outside current frozen165; no compiler/provider/workflow/current-tree edits.
-/
namespace UnifiedLean.G6.PrivateRegisterCalendarPrefix
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterBoundary
open UnifiedLean.G6.PrivateRegisterProgram
open UnifiedLean.G6.PrivateRegisterCalendar
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

private theorem prefix_dates_le (guard : ℝ) (pre post : List ℝ) :
    (pre ++ guard :: post).Pairwise (· ≤ ·) → ∀ d ∈ pre, d ≤ guard := by
  induction pre with
  | nil =>
      intro _ d hd
      simp only [List.not_mem_nil] at hd
  | cons a pre ih =>
      intro h d hd
      have hhead := (List.pairwise_cons.mp h).1
      have htail := (List.pairwise_cons.mp h).2
      rcases List.mem_cons.mp hd with hd | hd
      · subst d
        exact hhead guard (List.mem_append.mpr (Or.inr List.mem_cons_self))
      · exact ih htail d hd

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

/-- All private original node dates are strictly later than this included
boundary. The actual node-age filter excludes private COMMON sites. -/
theorem boundaryOperations_noPrivateWordRead_of_age_gt (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (guard a : ℝ)
    (hprivate : ∀ v ∈ P, guard < C.age v) (hdate : a ≤ guard) :
    NoPrivateWordRead N P (boundaryOperations N C H gamma common a) := by
  apply boundaryOperations_noPrivateWordRead N C H gamma common P a
  intro v hv
  exact ne_of_gt (lt_of_le_of_lt hdate (hprivate v hv))

theorem calendarTail_noPrivateWordRead_of_age_gt (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (guard a : ℝ) (dates : List ℝ)
    (hprivate : ∀ v ∈ P, guard < C.age v)
    (hdates : ∀ d ∈ dates, d ≤ guard) :
    NoPrivateWordRead N P (calendarTail N C H gamma common a dates) := by
  apply calendarTail_noPrivateWordRead N C H gamma common P a dates
  intro d hd v hv
  exact ne_of_gt (lt_of_le_of_lt (hdates d hd) (hprivate v hv))

/-- The initial date window is derived from the native sorted original
agenda, rather than supplied as an arbitrary no-read operation word. -/
theorem original_dates_prefix_le (N : RootedBinary V E X) (C : Calendar N.graph)
    (guard : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    ∀ d ∈ pre, d ≤ guard := by
  apply prefix_dates_le guard pre post
  rw [← hsplit]
  exact (original_dates_ordered N C).1

/-- Literal initial compiler form on its actual date prefix through the guard.
This is an expression using existing operations, not a new source wrapper. -/
theorem actual_calendar_initial_prefix_noPrivateWordRead (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (guard : ℝ) (pre post : List ℝ)
    (hprivate : ∀ v ∈ P, guard < C.age v)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    NoPrivateWordRead N P
      (match pre ++ [guard] with
       | [] => []
       | a :: dates => boundaryOperations N C H gamma common a ++
           calendarTail N C H gamma common a dates) := by
  have hpre := original_dates_prefix_le N C guard pre post hsplit
  cases pre with
  | nil =>
      simpa only [List.nil_append, calendarTail, List.append_nil] using
        boundaryOperations_noPrivateWordRead_of_age_gt N C H gamma common
          P guard guard hprivate le_rfl
  | cons a pre =>
      have ha : a ≤ guard := hpre a List.mem_cons_self
      have hdates : ∀ d ∈ pre ++ [guard], d ≤ guard := by
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact hpre d (List.mem_cons_of_mem a hd)
        · have heq : d = guard := List.mem_singleton.mp hd
          subst d
          exact le_rfl
      have hb := boundaryOperations_noPrivateWordRead_of_age_gt N C H gamma common
        P guard a hprivate ha
      have ht := calendarTail_noPrivateWordRead_of_age_gt N C H gamma common
        P guard a (pre ++ [guard]) hprivate hdates
      change NoPrivateWordRead N P
        (boundaryOperations N C H gamma common a ++
          calendarTail N C H gamma common a (pre ++ [guard]))
      intro op hop
      rcases List.mem_append.mp hop with hop | hop
      · exact hb op hop
      · exact ht op hop

/-- The prefix above is literally the initial part of compiledCalendarProgram;
the retained guard's whole boundary is processed before the native suffix. -/
theorem compiledCalendarProgram_split_at_guard (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (guard : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    compiledCalendarProgram N C H gamma common =
      (match pre ++ [guard] with
       | [] => []
       | a :: dates => boundaryOperations N C H gamma common a ++
           calendarTail N C H gamma common a dates) ++
        calendarTail N C H gamma common guard post := by
  unfold compiledCalendarProgram
  rw [hsplit]
  cases pre with
  | nil => simp only [List.nil_append, calendarTail, List.append_nil]
  | cons a pre =>
      change boundaryOperations N C H gamma common a ++
        calendarTail N C H gamma common a (pre ++ guard :: post) =
          (boundaryOperations N C H gamma common a ++
            calendarTail N C H gamma common a (pre ++ [guard])) ++
              calendarTail N C H gamma common guard post
      rw [calendarTail_split_after_boundary N C H gamma common a guard pre post]
      simp only [List.append_assoc]

/-- A retained ORIGINAL lower-endpoint vertex gives its actual safe prefix.
Strictly later private ages include none on the completed guard boundary. -/
theorem actual_guarded_initial_prefix_exists (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (v : V) (hprivate : ∀ w ∈ P, C.age v < C.age w) :
    ∃ pre post, sortedOriginalDates N C = pre ++ C.age v :: post ∧
      NoPrivateWordRead N P
        (match pre ++ [C.age v] with
         | [] => []
         | a :: dates => boundaryOperations N C H gamma common a ++
             calendarTail N C H gamma common a dates) := by
  obtain ⟨pre, post, hsplit⟩ :=
    date_split (C.age v) (sortedOriginalDates N C) (original_date_scheduled N C v)
  exact ⟨pre, post, hsplit,
    actual_calendar_initial_prefix_noPrivateWordRead N C H gamma common
      P (C.age v) pre post hprivate hsplit⟩

#print axioms boundaryOperations_noPrivateWordRead_of_age_gt
#print axioms calendarTail_noPrivateWordRead_of_age_gt
#print axioms original_dates_prefix_le
#print axioms actual_calendar_initial_prefix_noPrivateWordRead
#print axioms compiledCalendarProgram_split_at_guard
#print axioms actual_guarded_initial_prefix_exists

end UnifiedLean.G6.PrivateRegisterCalendarPrefix
