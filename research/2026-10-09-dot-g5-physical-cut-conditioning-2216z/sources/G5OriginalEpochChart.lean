import G5ActivatedPosteriorPlacement
import UnifiedLean.G6.PrivateRegisterCalendarPrefix
import GraphLeaves
import G5CalendarRoutes
import G2CompleteTimedSupport

/-! Reuse of the existing actual compiled-calendar guard split at a physical
ordinary epoch; no new source compiler or fitted clock is introduced. -/
namespace GProgram.G5.OriginalEpochChart
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.G6.PrivateRegisterCalendarPrefix UnifiedLean.G6.PrivateRegisterCalendar
open GProgram.G2.ChronologicalPathReadout GProgram.G2.CompleteTimedSupport
open GProgram.G2.OriginalProgramSafety UnifiedLean.Source.SourceCalendarTiming
open scoped Classical NNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

lemma first_date_of_contemporaneous_tips (N : RootedBinary V E X)
    (C : Calendar N.graph) (a : ℝ) (htips : ∀ x, C.age (N.leaf x) = a) :
    firstOriginalDate N C = a := by
  apply le_antisymm
  · obtain ⟨x,_⟩ := N.every_vertex_reaches_leaf N.root
    simpa only [htips x] using firstOriginalDate_le N C (N.leaf x)
  · apply Finset.le_min'
    intro b hb
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨x,hx⟩ := N.every_vertex_reaches_leaf v
    rw [← htips x]
    exact C.age_le_of_directed hx

lemma adjacent_gap {a t : ℝ} (dates : List ℝ) (ha : a < t)
    (hne : ∀ b ∈ a :: dates, b ≠ t)
    (hfuture : ∃ b ∈ a :: dates, t < b) :
    ∃ pre left right post, a :: dates = pre ++ left :: right :: post ∧ left < t ∧ t < right := by
  induction dates generalizing a with
  | nil =>
    obtain ⟨b,hb,ht⟩ := hfuture
    have hb' : b = a := by simpa using hb
    subst b
    exact False.elim (lt_asymm ha ht)
  | cons b bs ih =>
    by_cases htb : t < b
    · exact ⟨[],a,b,bs,rfl,ha,htb⟩
    · have hbt : b < t := lt_of_le_of_ne (le_of_not_gt htb) (hne b (by simp))
      have hf : ∃ c ∈ b :: bs, t < c := by
        obtain ⟨c,hc,htc⟩ := hfuture
        rcases List.mem_cons.mp hc with hca | hc
        · subst c
          exact False.elim (lt_asymm ha htc)
        · exact ⟨c,hc,htc⟩
      obtain ⟨pre,l,r,post,he,hl,hr⟩ := ih hbt (fun c hc => hne c (by simp [hc])) hf
      exact ⟨a::pre,l,r,post,by simp only [List.cons_append,←he],hl,hr⟩

noncomputable def prefixThrough (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (pre : List ℝ) (guard : ℝ) : List (ProgramStep N) :=
  match pre ++ [guard] with
  | [] => []
  | a::dates => boundaryOperations N C H gamma common a ++ calendarTail N C H gamma common a dates

/-- The exact already-compiled original program, split at an adjacent date
pair, exhibits the ordinary interval containing the physical cut. -/
theorem actual_original_epoch_word (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (pre : List ℝ) (guard next : ℝ) (post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) :
    compiledCalendarProgram N C H gamma common =
      prefixThrough N C H gamma common pre guard ++
        .interval (Real.toNNReal (next-guard)) ::
          (boundaryOperations N C H gamma common next ++ calendarTail N C H gamma common next post) := by
  exact compiledCalendarProgram_split_at_guard N C H gamma common guard pre (next::post) hsplit

lemma calendar_tail_duration_exact (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) (dates : List ℝ)
    (horder : (a::dates).Pairwise (· < ·)) :
    a + (programDuration N (calendarTail N C H gamma common a dates) : ℝ) = finalDate a dates := by
  induction dates generalizing a with
  | nil => simp [calendarTail,programDuration,finalDate]
  | cons b bs ih =>
    have hp := List.pairwise_cons.mp horder
    have hab : a < b := hp.1 b (by simp)
    have hi := ih b hp.2
    have hd := duration_boundaries N (boundaryOperations N C H gamma common b)
      (original_batch_only_boundaries N C H gamma common b)
    simp only [calendarTail,programDuration,duration_append,hd,zero_add,NNReal.coe_add,finalDate]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hab.le)]
    linarith

#print axioms actual_original_epoch_word
#print axioms first_date_of_contemporaneous_tips
#print axioms calendar_tail_duration_exact
end GProgram.G5.OriginalEpochChart
