import SamuelAlexanderResearch.FullHeight

set_option warningAsError true
open FiniteEditStability ThueMorseBits

namespace ThueMorseReuse

theorem height_zero_iff_no_first (v : Nat) :
    FullHeight.height v = 0 ↔ ¬ HasPrefix t v 1 := by
  constructor
  · intro h hp
    have le := (FullHeight.height_isMaximum v).2 1 hp
    omega
  · intro h
    by_cases h0 : FullHeight.height v = 0
    · exact h0
    · obtain ⟨path,hv,hm⟩ := (FullHeight.height_isMaximum v).1
      exfalso
      exact h ⟨path,hv,fun k hk => hm k (by omega)⟩

private theorem first_iff_edge (v : Nat) :
    HasPrefix t v 1 ↔ ∃ w, BinaryAvoidance.Edge t v w false := by
  constructor
  · rintro ⟨path, hv, hp⟩
    have he := hp 0 (by decide)
    rw [hv,t_zero] at he
    exact ⟨path 1,he⟩
  · rintro ⟨w,h⟩
    refine ⟨fun k => if k = 0 then v else w, by simp, ?_⟩
    intro k hk
    have hz : k = 0 := by omega
    subst k
    simpa using h

private theorem first_iff_bits (v : Nat) (hv : 1 ≤ v) :
    HasPrefix t v 1 ↔ t (v+1) = false ∨ t (v+2) = true := by
  rw [first_iff_edge]
  constructor
  · rintro ⟨w,h⟩
    have hh := (SharpThueMorse.binary_edge_iff v w false).mp h
    rcases hh.2 with ⟨a,b⟩ | ⟨a,b⟩
    · exact .inl (a ▸ b)
    · subst w
      cases e : t (v+2)
      · exact False.elim (b e)
      · exact .inr rfl
  · rintro (a | b)
    · exact ⟨v+1,(SharpThueMorse.binary_edge_iff _ _ _).mpr
        ⟨by omega,.inl ⟨rfl,a⟩⟩⟩
    · exact ⟨v+2,(SharpThueMorse.binary_edge_iff _ _ _).mpr
        ⟨by omega,.inr ⟨rfl,by simp [b]⟩⟩⟩

theorem height_zero_iff_descent (v : Nat) :
    FullHeight.height v = 0 ↔ t (v+1) = true ∧ t (v+2) = false := by
  rw [height_zero_iff_no_first]
  cases v with
  | zero =>
    rw [first_iff_edge]
    have h : BinaryAvoidance.Edge t 0 2 false :=
      (SharpThueMorse.binary_edge_iff _ _ _).mpr
        ⟨by decide, .inr ⟨rfl, by simp⟩⟩
    simp [show ∃ w, BinaryAvoidance.Edge t 0 w false from ⟨2,h⟩]
  | succ v =>
    rw [first_iff_bits (v+1) (by omega)]
    cases a : t (v+1+1) <;> cases b : t (v+1+2) <;> decide

theorem reused_exception_two : FullHeight.height 2 = 5 := by
  rw [FullHeight.height_from_factorization 2 0 1 (by decide)]
  simp [FullHeight.evenValue, FullHeight.bit]

theorem reused_sharp_five : FullHeight.height 5 = 13 := by
  rw [FullHeight.height_from_factorization 5 1 0 (by decide)]
  simp [FullHeight.oddValue, FullHeight.special]

theorem reused_absent_zero_to_one : FullHeight.height 0 = 1 := by
  rw [FullHeight.height_from_factorization 0 0 0 (by decide)]
  simp [FullHeight.evenValue, FullHeight.bit]

#print axioms height_zero_iff_descent
#print axioms reused_exception_two
#print axioms reused_sharp_five
#print axioms reused_absent_zero_to_one
end ThueMorseReuse
