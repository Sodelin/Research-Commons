import SamuelAlexanderResearch.ThueMorseBits
import Mathlib.Tactic

namespace ThueMorseMAP
open ThueMorseBits

/-- A monochromatic progression with the specified letter and exact list length. -/
def Run (s d L : ℕ) (c : Bool) : Prop := ∀ k < L, t (s + k * d) = c

def Mono (s d L : ℕ) : Prop := ∃ c, Run s d L c

/-- Includes a universal upper bound, not just maximality at this start. -/
def FirstMaximum (d L s : ℕ) : Prop :=
  Mono s d L ∧ (∀ a, ¬ Mono a d (L+1)) ∧ ∀ a < s, ¬ Mono a d L

/-- The scale-free neighboring-letter condition. -/
def Center (l : ℕ) : Prop := 1 ≤ l ∧ t (l-1) = !(t l) ∧ t (l+1) = !(t l)

@[simp] theorem xor_self (a : Bool) : Bool.xor a a = false := by cases a <;> rfl

theorem xor_cancel (a b c : Bool) (h : Bool.xor a c = Bool.xor b c) : a=b := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem xor_eq_iff (a b c : Bool) : Bool.xor a b = c ↔ a = Bool.xor c b := by
  cases a <;> cases b <;> cases c <;> decide

theorem xor_not (a : Bool) : Bool.xor a true = !a := by cases a <;> rfl

theorem pow_pos (m : ℕ) : 0 < 2^m := by positivity

theorem pow_ge_four {m : ℕ} (hm : 2≤m) : 4≤2^m := by
  have h := Nat.pow_le_pow_right (by omega : 0<2) hm
  norm_num at h ⊢
  exact h

theorem equal_adjacent_odd {a : ℕ} (h : t a = t (a+1)) : a % 2 = 1 := by
  by_contra hodd
  have ha : a = 2*(a/2) := by omega
  have hb : a+1 = 2*(a/2)+1 := by omega
  have h0 : t a = t (a/2) := by conv_lhs => rw [ha, t_double]
  have h1 : t (a+1) = !(t (a/2)) := by rw [hb, t_double_add_one]
  rw [h0,h1] at h
  cases ht : t (a/2) <;> simp only [ht, Bool.not_false, Bool.not_true] at h <;> contradiction

/-- Complementing all low binary digits. -/
theorem complement (m r : ℕ) (hr : r<2^m) :
    t (2^m-1-r) = Bool.xor (t r) (decide (m%2=1)) := by
  induction m generalizing r with
  | zero =>
    have hr0 : r=0 := by simpa using hr
    subst r
    simp
  | succ m ih =>
    have hp := pow_pos m
    have hr' : r/2<2^m := by rw [Nat.pow_succ] at hr; omega
    have he : decide ((m+1)%2=1) = !(decide (m%2=1)) := by
      by_cases h : m%2=1 <;> simp_all <;> omega
    rw [he]
    by_cases hpar : r%2=0
    · have heq : 2^(m+1)-1-r=2*(2^m-1-r/2)+1 := by
        rw [Nat.pow_succ]; omega
      have req : r=2*(r/2) := by omega
      rw [heq,t_double_add_one,ih (r/2) hr']
      conv_rhs => rw [req,t_double]
      cases t (r/2) <;> cases decide (m%2=1) <;> rfl
    · have heq : 2^(m+1)-1-r=2*(2^m-1-r/2) := by
        rw [Nat.pow_succ]; omega
      have req : r=2*(r/2)+1 := by omega
      rw [heq,t_double,ih (r/2) hr']
      conv_rhs => rw [req,t_double_add_one]
      cases t (r/2) <;> cases decide (m%2=1) <;> rfl

theorem center_three : Center 3 := by simp [Center]

theorem center_ge_three {l : ℕ} (h : Center l) : 3≤l := by
  rcases h with ⟨hl,h1,h2⟩
  by_contra hn
  interval_cases l <;> simp_all

theorem run_shift {s d L : ℕ} {c : Bool} (h : Run s d (L+1) c) : Run (s+d) d L c := by
  intro k hk
  have := h (k+1) (by omega)
  convert this using 1 <;> congr 1 <;> ring

end ThueMorseMAP
