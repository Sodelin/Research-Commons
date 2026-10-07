import UnifiedLean.G6.PrivateRegisterProgram
import UnifiedLean.Source.SourceCalendarCompiler
import Mathlib.Data.List.Nodup

/-!
UNCHECKED actual ORIGINAL calendar no-future-private-read constructor.
CLOUD-PRIVATE-CALENDAR-SOL-2304Z, 7 October 2026. Outside frozen165.

Premises are private-node physical age placement and a position in the actual
sorted original agenda, never a desired NoPrivateWordRead or kernel law. All
edge exits, ordinary/root operations and both global inheritance modes remain
the actual compiler's operations. INDEPENDENT remains the current AtNode law.
No new source wrapper, endpoint/history probability theorem or surgery lift.
-/
namespace UnifiedLean.G6.PrivateRegisterCalendar
open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterBoundary
open UnifiedLean.G6.PrivateRegisterProgram
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

private theorem pairwise_suffix {R : ℝ → ℝ → Prop} (pre post : List ℝ) :
    (pre ++ post).Pairwise R → post.Pairwise R := by
  induction pre with
  | nil => simpa
  | cons a pre ih =>
      intro h
      exact ih (List.pairwise_cons.mp h).2

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

/-- A compiled COMMON read names this same original node via original_site.
Root, ordinary and INDEPENDENT operations do not inspect a latent bit. -/
theorem originalNodeOperation_noPrivateRead (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (P : Finset V) (v : V) (hv : v ∉ P) :
    NoPrivateRead N P (originalNodeOperation N H gamma common v) := by
  rcases original_node_is_actual_operation N H gamma common v with
    hroot | hhybrid | hord
  · rw [hroot.1]
    trivial
  · obtain ⟨hy, _, hsite, hop⟩ := hhybrid
    rcases hop with hop | hop
    · rw [hop]
      change (H.parents hy).hybrid ∉ P
      simpa only [hsite] using hv
    · rw [hop]
      trivial
  · obtain ⟨e, _, hd, hop⟩ := hord
    rw [hop]
    trivial

/-- Actual age-filtered nodes are outside P at an excluded date. Every edge
exit remains in the word, in the compiler's exit-before-node order. -/
theorem boundaryOperations_noPrivateWordRead (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (a : ℝ) (hexclude : ∀ v ∈ P, C.age v ≠ a) :
    NoPrivateWordRead N P (boundaryOperations N C H gamma common a) := by
  intro op hop
  change op ∈ _ ++ _ at hop
  rcases List.mem_append.mp hop with hexit | hnode
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hexit
    trivial
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hnode
    have hage : C.age v = a :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
    change NoPrivateRead N P (originalNodeOperation N H gamma common v)
    apply originalNodeOperation_noPrivateRead N H gamma common P v
    intro hP
    exact hexclude v hP hage

/-- Intervals, including zero intervals, never read a latent register. All
scheduled boundaries are safe by their actual node-date filter. -/
theorem calendarTail_noPrivateWordRead (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (a : ℝ) (dates : List ℝ) :
    (∀ d ∈ dates, ∀ v ∈ P, C.age v ≠ d) →
      NoPrivateWordRead N P (calendarTail N C H gamma common a dates) := by
  induction dates generalizing a with
  | nil =>
      intro _ op hop
      simp only [calendarTail, List.not_mem_nil] at hop
  | cons d dates ih =>
      intro hexclude
      have hboundary := boundaryOperations_noPrivateWordRead N C H gamma common
        P d (hexclude d List.mem_cons_self)
      have htail := ih d (by
        intro t ht
        exact hexclude t (List.mem_cons_of_mem d ht))
      intro op hop
      change op ∈ .interval (Real.toNNReal (d-a)) ::
        (boundaryOperations N C H gamma common d ++
          calendarTail N C H gamma common d dates) at hop
      rcases List.mem_cons.mp hop with hinterval | hop
      · subst op
        trivial
      · rcases List.mem_append.mp hop with hboundaryMem | htailMem
        · exact hboundary op hboundaryMem
        · exact htail op htailMem

/-- Strictly younger private nodes are absent even from the guard's own
boundary. Nodes tied at the guard remain and must be outside P. -/
theorem boundaryOperations_noPrivateWordRead_of_age_lt (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (guard a : ℝ)
    (hprivate : ∀ v ∈ P, C.age v < guard) (hdate : guard ≤ a) :
    NoPrivateWordRead N P (boundaryOperations N C H gamma common a) := by
  apply boundaryOperations_noPrivateWordRead N C H gamma common P a
  intro v hv
  exact ne_of_lt (lt_of_lt_of_le (hprivate v hv) hdate)

theorem calendarTail_noPrivateWordRead_of_age_lt (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (guard a : ℝ) (dates : List ℝ)
    (hprivate : ∀ v ∈ P, C.age v < guard)
    (hdates : ∀ d ∈ dates, guard ≤ d) :
    NoPrivateWordRead N P (calendarTail N C H gamma common a dates) := by
  apply calendarTail_noPrivateWordRead N C H gamma common P a dates
  intro d hd v hv
  exact ne_of_lt (lt_of_lt_of_le (hprivate v hv) (hdates d hd))

/-- In the actual sorted, deduplicated original agenda, all dates after a
scheduled guard are strictly later. Coincident nodes share that guard boundary. -/
theorem original_dates_suffix_gt (N : RootedBinary V E X) (C : Calendar N.graph)
    (guard : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    ∀ d ∈ post, guard < d := by
  have hordered : (pre ++ guard :: post).Pairwise (· ≤ ·) := by
    rw [← hsplit]
    exact (original_dates_ordered N C).1
  have hnodup : (pre ++ guard :: post).Nodup := by
    rw [← hsplit]
    exact (original_dates_ordered N C).2
  have hpost := pairwise_suffix pre (guard :: post) hordered
  have hpostNodup : (guard :: post).Nodup := hnodup.of_append_right
  intro d hd
  have hle : guard ≤ d := (List.pairwise_cons.mp hpost).1 d hd
  have hne : guard ≠ d := by
    intro heq
    apply (List.nodup_cons.mp hpostNodup).1
    simpa only [heq] using hd
  exact lt_of_le_of_ne hle hne

/-- No desired no-read word is a premise: derive it from physical age
placement and the actual agenda suffix at a retained guard. -/
theorem actual_calendar_suffix_noPrivateWordRead (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (guard : ℝ) (pre post : List ℝ)
    (hprivate : ∀ v ∈ P, C.age v < guard)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    NoPrivateWordRead N P (calendarTail N C H gamma common guard post) := by
  apply calendarTail_noPrivateWordRead_of_age_lt N C H gamma common P
    guard guard post hprivate
  intro d hd
  exact (original_dates_suffix_gt N C guard pre post hsplit d hd).le

/-- The full guard boundary can also be retained before the suffix: private
nodes are strictly younger, and exits precede all tied original node operations. -/
theorem actual_boundary_and_suffix_noPrivateWordRead (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (guard : ℝ) (pre post : List ℝ)
    (hprivate : ∀ v ∈ P, C.age v < guard)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    NoPrivateWordRead N P
      (boundaryOperations N C H gamma common guard ++
        calendarTail N C H gamma common guard post) := by
  have hb := boundaryOperations_noPrivateWordRead_of_age_lt N C H gamma common
    P guard guard hprivate le_rfl
  have ht := actual_calendar_suffix_noPrivateWordRead N C H gamma common
    P guard pre post hprivate hsplit
  intro op hop
  rcases List.mem_append.mp hop with hop | hop
  · exact hb op hop
  · exact ht op hop

/-- A retained ORIGINAL node supplies its actual scheduled suffix; no new
calendar/source wrapper or arbitrary future operation word is introduced. -/
theorem actual_guarded_suffix_exists (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (v : V) (hprivate : ∀ w ∈ P, C.age w < C.age v) :
    ∃ pre post, sortedOriginalDates N C = pre ++ C.age v :: post ∧
      NoPrivateWordRead N P (calendarTail N C H gamma common (C.age v) post) := by
  obtain ⟨pre, post, hsplit⟩ :=
    date_split (C.age v) (sortedOriginalDates N C) (original_date_scheduled N C v)
  exact ⟨pre, post, hsplit,
    actual_calendar_suffix_noPrivateWordRead N C H gamma common
      P (C.age v) pre post hprivate hsplit⟩

/-- The native calendarTail suffix is literally the operation-word tail after
processing the guard boundary, not a newly defined source law. -/
theorem calendarTail_split_after_boundary (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (a guard : ℝ) (pre post : List ℝ) :
    calendarTail N C H gamma common a (pre ++ guard :: post) =
      calendarTail N C H gamma common a (pre ++ [guard]) ++
        calendarTail N C H gamma common guard post := by
  induction pre generalizing a with
  | nil =>
      simp only [List.nil_append, calendarTail, List.append_nil,
        List.cons_append, List.append_assoc]
  | cons d pre ih =>
      simp only [List.cons_append, calendarTail, List.cons_append, List.append_assoc]
      rw [ih d]
      simp only [List.append_assoc]

#print axioms originalNodeOperation_noPrivateRead
#print axioms boundaryOperations_noPrivateWordRead
#print axioms calendarTail_noPrivateWordRead
#print axioms original_dates_suffix_gt
#print axioms actual_calendar_suffix_noPrivateWordRead
#print axioms actual_boundary_and_suffix_noPrivateWordRead
#print axioms actual_guarded_suffix_exists
#print axioms calendarTail_split_after_boundary

end UnifiedLean.G6.PrivateRegisterCalendar
