import ZeroRunGenerator
set_option warningAsError true

namespace AlexanderZeroRun

theorem arbitrarily_late_two_ones (A : Nat → Prop) (bound : Nat) :
    ∃ i, bound ≤ i ∧ twist A i = true ∧ twist A (i+1) = true := by
  refine ⟨slotStart 0 bound+1, by have h := slotStart_ge_index 0 bound; omega, ?_, ?_⟩
  · apply (twist_true_iff A _).2
    simpa only [Nat.zero_add, Nat.add_zero] using slot_after_two_ones A 0 bound 0 (by decide)
  · apply (twist_true_iff A _).2
    simpa only [Nat.zero_add] using slot_after_two_ones A 0 bound 1 (by decide)

theorem every_zero_in_maximal_run (A : Nat → Prop) (i : Nat) (hi : twist A i = false) :
    ∃ m j, A m ∧ slotStart m j ≤ i ∧ i < slotStart m j + (m+1) ∧
      IsRun A (slotStart m j) (m+1) := by
  obtain ⟨m,j,hm,hlo,hhi⟩ := (twist_false_iff A i).1 hi
  exact ⟨m,j,hm,hlo,hhi,selected_slot_is_run A hm j⟩

#print axioms arbitrarily_late_two_ones
#print axioms every_zero_in_maximal_run
end AlexanderZeroRun
