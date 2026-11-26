import SignatureDiagonal
set_option warningAsError true

namespace AlexanderZeroRun
open AlexanderOmnibus

def startIndex (k : Nat) : Nat := (k+2)*(k+2)

def slotStart (m j : Nat) : Nat := startIndex (pairCode m j)

def Zero (A : Nat → Prop) (i : Nat) : Prop :=
  ∃ m j, A m ∧ slotStart m j ≤ i ∧ i < slotStart m j + (m+1)

noncomputable def twist (A : Nat → Prop) (i : Nat) : Bool :=
  @ite Bool (Zero A i) (Classical.propDecidable _) false true

theorem twist_false_iff (A : Nat → Prop) (i : Nat) : twist A i = false ↔ Zero A i := by
  classical
  by_cases h : Zero A i <;> simp [twist, h]

theorem twist_true_iff (A : Nat → Prop) (i : Nat) : twist A i = true ↔ ¬ Zero A i := by
  classical
  by_cases h : Zero A i <;> simp [twist, h]

private theorem le_square (n : Nat) : n ≤ n*n := by
  cases n with
  | zero => decide
  | succ n =>
    have h : (n+1)*1 ≤ (n+1)*(n+1) := Nat.mul_le_mul_left _ (by omega)
    simpa only [Nat.mul_one] using h

private theorem code_bounds (m j : Nat) : m ≤ pairCode m j ∧ j ≤ pairCode m j := by
  have h := le_square (m+j)
  unfold pairCode
  omega

theorem slotStart_positive (m j : Nat) : 0 < slotStart m j := by
  unfold slotStart startIndex
  have h := le_square (pairCode m j+2)
  omega

theorem slotStart_ge_index (m j : Nat) : j ≤ slotStart m j := by
  have h := le_square (pairCode m j+2)
  have hc := (code_bounds m j).2
  unfold slotStart startIndex
  omega

private theorem square_gap (n : Nat) (hn : 1 ≤ n) :
    n*n+n+2 ≤ (n+1)*(n+1) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

theorem index_spacing {k l : Nat} (h : k < l) :
    startIndex k + k + 3 ≤ startIndex l := by
  have hb : k+2+1 ≤ l+2 := by omega
  have hm := Nat.mul_le_mul hb hb
  have hg := square_gap (k+2) (by omega)
  unfold startIndex
  omega

/-- The first two indices after a slot are guaranteed ones before any later slot. -/
theorem slot_spacing {m j p q : Nat} (h : pairCode m j < pairCode p q) :
    slotStart m j+(m+1)+2 ≤ slotStart p q := by
  have hs := index_spacing h
  have hc := (code_bounds m j).1
  unfold slotStart
  omega

theorem initial_one (A : Nat → Prop) : twist A 0 = true := by
  apply (twist_true_iff A 0).2
  rintro ⟨m,j,_,hs,_⟩
  have hp := slotStart_positive m j
  omega

theorem slot_before_one (A : Nat → Prop) (m j : Nat) :
    ¬ Zero A (slotStart m j-1) := by
  rintro ⟨p,q,_,hl,hh⟩
  have hp := slotStart_positive m j
  rcases Nat.lt_trichotomy (pairCode p q) (pairCode m j) with h|h|h
  · have hs := slot_spacing h
    omega
  · obtain ⟨rfl,rfl⟩ := pairCode_injective h
    omega
  · have hs := slot_spacing h
    omega

theorem slot_after_two_ones (A : Nat → Prop) (m j r : Nat) (hr : r < 2) :
    ¬ Zero A (slotStart m j+(m+1)+r) := by
  rintro ⟨p,q,_,hl,hh⟩
  rcases Nat.lt_trichotomy (pairCode p q) (pairCode m j) with h|h|h
  · have hs := slot_spacing h
    omega
  · obtain ⟨rfl,rfl⟩ := pairCode_injective h
    omega
  · have hs := slot_spacing h
    omega

/-- A positive maximal finite run, represented by its left index and length. -/
def IsRun (A : Nat → Prop) (s len : Nat) : Prop :=
  0 < s ∧ 0 < len ∧ ¬ Zero A (s-1) ∧
    (∀ i, s ≤ i → i < s+len → Zero A i) ∧ ¬ Zero A (s+len)

theorem selected_slot_is_run (A : Nat → Prop) {m : Nat} (hm : A m) (j : Nat) :
    IsRun A (slotStart m j) (m+1) := by
  refine ⟨slotStart_positive m j, by omega, slot_before_one A m j, ?_, ?_⟩
  · intro i hl hr
    exact ⟨m,j,hm,hl,hr⟩
  · simpa only [Nat.add_zero] using slot_after_two_ones A m j 0 (by decide)

theorem every_run_is_slot (A : Nat → Prop) {s len : Nat} (h : IsRun A s len) :
    ∃ m j, A m ∧ s = slotStart m j ∧ len = m+1 := by
  obtain ⟨hs,hlen,prev,inside,stop⟩ := h
  obtain ⟨m,j,hm,hlo,hhi⟩ := inside s (by omega) (by omega)
  have eqS : s = slotStart m j := by
    by_cases h : s = slotStart m j
    · exact h
    · exfalso
      exact prev ⟨m,j,hm,by omega,by omega⟩
  have eqL : len = m+1 := by
    rcases Nat.lt_trichotomy len (m+1) with h|h|h
    · exfalso
      exact stop ⟨m,j,hm,by omega,by omega⟩
    · exact h
    · exfalso
      have hz := inside (slotStart m j+(m+1)) (by omega) (by omega)
      exact (slot_after_two_ones A m j 0 (by decide)) (by simpa only [Nat.add_zero] using hz)
  exact ⟨m,j,hm,eqS,eqL⟩

theorem run_characterization (A : Nat → Prop) (s len : Nat) :
    IsRun A s len ↔ ∃ m j, A m ∧ s = slotStart m j ∧ len = m+1 := by
  constructor
  · exact every_run_is_slot A
  · rintro ⟨m,j,hm,rfl,rfl⟩
    exact selected_slot_is_run A hm j

theorem arbitrarily_late_run_iff (A : Nat → Prop) (m : Nat) :
    (∀ bound, ∃ s, bound ≤ s ∧ IsRun A s (m+1)) ↔ A m := by
  constructor
  · intro h
    obtain ⟨s,_,hs⟩ := h 0
    obtain ⟨p,j,hp,_,he⟩ := every_run_is_slot A hs
    have eq : m = p := by omega
    simpa only [eq] using hp
  · intro hm bound
    exact ⟨slotStart m bound, slotStart_ge_index m bound, selected_slot_is_run A hm bound⟩

theorem unselected_run_excluded (A : Nat → Prop) (m : Nat) (ha : ¬ A m) :
    ∀ s, ¬ IsRun A s (m+1) := by
  intro s h
  obtain ⟨p,j,hp,_,he⟩ := every_run_is_slot A h
  have eq : m = p := by omega
  exact ha (by simpa only [eq] using hp)

#print axioms run_characterization
#print axioms arbitrarily_late_run_iff
#print axioms unselected_run_excluded
#print axioms slot_after_two_ones
end AlexanderZeroRun
