import G5OriginalEpochChart

namespace GProgram.G5.PhysicalCutChart
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarTiming
open GProgram.G2.ChronologicalPathReadout GProgram.G2.CompleteTimedSupport
open GProgram.G2.OriginalProgramSafety GProgram.G5.OriginalEpochChart
open scoped Classical NNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

lemma original_date_not_cut (N : RootedBinary V E X) (C : Calendar N.graph)
    (t : ℝ) (hnot : ∀ v, C.age v ≠ t) (b : ℝ) (hb : b ∈ sortedOriginalDates N C) : b ≠ t := by
  have hm : b ∈ originalDates N C := by simpa only [sortedOriginalDates,Finset.mem_sort] using hb
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hm
  exact hnot v

lemma original_gap_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (t : ℝ) (hfirst : firstOriginalDate N C < t) (hroot : t < C.age N.root)
    (hnot : ∀ v, C.age v ≠ t) :
    ∃ pre guard next post, sortedOriginalDates N C = pre ++ guard :: next :: post ∧
      guard < t ∧ t < next := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro hz
    have h := original_date_scheduled N C N.root
    rw [hz] at h
    exact List.not_mem_nil h
  obtain ⟨a,dates,heq⟩ := List.exists_cons_of_ne_nil hne
  have ha : a = firstOriginalDate N C := by
    have h := first_compiled_date_is_initial_boundary N C
    simpa only [heq,List.getElem_cons_zero] using h
  obtain ⟨pre,l,r,post,hs,hl,hr⟩ := adjacent_gap dates (ha.symm ▸ hfirst)
    (fun b hb => original_date_not_cut N C t hnot b (heq.symm ▸ hb))
    ⟨C.age N.root,heq ▸ original_date_scheduled N C N.root,hroot⟩
  exact ⟨pre,l,r,post,heq.trans hs,hl,hr⟩

lemma prefix_activation_shape (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (pre : List ℝ) (guard next : ℝ) (post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) :
    ∃ dates, prefixThrough N C H gamma common pre guard =
      boundaryOperations N C H gamma common (firstOriginalDate N C) ++
        calendarTail N C H gamma common (firstOriginalDate N C) dates := by
  have hfirst := first_compiled_date_is_initial_boundary N C
  cases pre with
  | nil =>
    have hg : guard = firstOriginalDate N C := by
      simpa only [hsplit,List.nil_append,List.getElem_cons_zero] using hfirst
    refine ⟨[],?_⟩
    simp only [prefixThrough,List.nil_append,hg,calendarTail,List.append_nil]
  | cons a pre =>
    have ha : a = firstOriginalDate N C := by
      simpa only [hsplit,List.cons_append,List.getElem_cons_zero] using hfirst
    refine ⟨pre++[guard],?_⟩
    simp only [prefixThrough,List.cons_append,ha]

lemma finalDate_append_singleton (a guard : ℝ) (dates : List ℝ) :
    finalDate a (dates ++ [guard]) = guard := by
  induction dates generalizing a with
  | nil => rfl
  | cons b bs ih => exact ih b

lemma prefix_age_is_guard (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (pre : List ℝ) (guard next : ℝ) (post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) :
    firstOriginalDate N C + (programDuration N (prefixThrough N C H gamma common pre guard) : ℝ) = guard := by
  have hfirst := first_compiled_date_is_initial_boundary N C
  have ho := original_dates_strict N C
  have ho' : ((pre++[guard]) ++ next::post).Pairwise (· < ·) := by
    simpa only [hsplit,List.append_assoc,List.singleton_append] using ho
  have hp := (List.pairwise_append.mp ho').1
  cases pre with
  | nil =>
    have hg : guard = firstOriginalDate N C := by
      simpa only [hsplit,List.nil_append,List.getElem_cons_zero] using hfirst
    have hd := duration_boundaries N (boundaryOperations N C H gamma common guard)
      (original_batch_only_boundaries N C H gamma common guard)
    simpa only [prefixThrough,List.nil_append,calendarTail,List.append_nil,hd,NNReal.coe_zero,add_zero] using hg.symm
  | cons a pre =>
    have ha : a = firstOriginalDate N C := by
      simpa only [hsplit,List.cons_append,List.getElem_cons_zero] using hfirst
    have hd := duration_boundaries N (boundaryOperations N C H gamma common a)
      (original_batch_only_boundaries N C H gamma common a)
    have hi := calendar_tail_duration_exact N C H gamma common a (pre++[guard]) hp
    rw [←ha]
    simpa only [prefixThrough,List.cons_append,duration_append,hd,zero_add,
      finalDate_append_singleton] using hi

lemma gap_three_parts {guard t next : ℝ} (hleft : guard < t) (hright : t < next)
    (u : ℝ≥0) (hu : (u : ℝ) < next-t) :
    Real.toNNReal (next-guard) = Real.toNNReal (t-guard) +
      (u + Real.toNNReal (next-t-u)) := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_add]
  rw [Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith),
    Real.coe_toNNReal _ (by linarith)]
  ring

#print axioms original_gap_exists
#print axioms prefix_activation_shape
#print axioms prefix_age_is_guard
#print axioms gap_three_parts
end GProgram.G5.PhysicalCutChart
