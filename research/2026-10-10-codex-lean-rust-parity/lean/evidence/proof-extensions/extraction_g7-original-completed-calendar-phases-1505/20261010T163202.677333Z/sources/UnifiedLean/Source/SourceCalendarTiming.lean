import UnifiedLean.Source.SourceCalendarCompiler

/-!
# Derived original agenda timing facts

Contributor: dot, 2026-10-02. Closes the compiler's arithmetic admission:
sorted deduplicated original dates are strictly increasing, every consecutive
interval uses its exact positive original age difference (not clamping), and
the original root is the maximal original boundary. These facts feed full
calendar-location preservation, not a substitute for that source obligation.
-/
namespace UnifiedLean.Source.SourceCalendarTiming
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarCompiler
open scoped Classical NNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

theorem original_dates_strict (N : RootedBinary V E X) (C : Calendar N.graph) :
    (sortedOriginalDates N C).Pairwise (· < ·) := by
  exact (Finset.sortedLT_sort (originalDates N C)).pairwise

theorem actual_consecutive_duration (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : ℝ} {pre post : List ℝ}
    (h : sortedOriginalDates N C = pre ++ a :: b :: post) :
    a < b ∧ (Real.toNNReal (b-a) : ℝ) = b-a := by
  have hp := original_dates_strict N C
  rw [h,List.pairwise_append] at hp
  have hab : a < b := (List.pairwise_cons.mp hp.2.1).1 b (by simp)
  exact ⟨hab,Real.coe_toNNReal _ (sub_nonneg.mpr hab.le)⟩

/-- No original vertex lies temporally above the original root. -/
theorem original_root_latest (N : RootedBinary V E X) (C : Calendar N.graph) (v : V) :
    C.age v ≤ C.age N.root := C.age_le_of_directed (N.rooted v)

/-- The last ORIGINAL date is the actual supplied root age, not a replacement
empty exterior or an assumed stopping age. -/
theorem last_original_date_is_root (N : RootedBinary V E X) (C : Calendar N.graph) :
    (originalDates N C).max' (originalDates_nonempty N C) = C.age N.root := by
  apply le_antisymm
  · obtain ⟨v,_,hv⟩ := Finset.mem_image.mp
      ((originalDates N C).max'_mem (originalDates_nonempty N C))
    rw [← hv]
    exact original_root_latest N C v
  · exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨N.root,Finset.mem_univ _,rfl⟩)

/-- The compiled sequence begins at the actual earliest original node age. -/
theorem first_compiled_date_is_initial_boundary (N : RootedBinary V E X) (C : Calendar N.graph) :
    (sortedOriginalDates N C)[0]'(by
      rw [sortedOriginalDates,Finset.length_sort]
      exact Finset.card_pos.mpr (originalDates_nonempty N C)) = firstOriginalDate N C := by
  exact Finset.sorted_zero_eq_min'

#print axioms original_dates_strict
#print axioms actual_consecutive_duration
#print axioms last_original_date_is_root
#print axioms first_compiled_date_is_initial_boundary
end UnifiedLean.Source.SourceCalendarTiming
