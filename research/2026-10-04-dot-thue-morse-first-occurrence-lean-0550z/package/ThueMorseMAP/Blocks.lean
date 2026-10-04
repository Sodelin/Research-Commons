import ThueMorseMAP.Basic
namespace ThueMorseMAP
open ThueMorseBits

def Block (m h : ℕ) (c : Bool) : Prop := ∀ r < 2^m, t (h+r) = Bool.xor c (t r)

theorem block_zero {m h : ℕ} {c : Bool} (H : Block m h c) : t h = c := by
  simpa using H 0 (pow_pos m)

theorem block_even {m h : ℕ} {c : Bool} (hm : 2≤m) (H : Block m h c) : h%2=0 := by
  have hq := pow_ge_four hm
  have h1 := H 1 (by omega)
  have h2 := H 2 (by omega)
  have he : t (h+1)=t (h+1+1) := by
    simp only [t_one,t_two] at h1 h2
    simpa [Nat.add_assoc] using h1.trans h2.symm
  have := equal_adjacent_odd he
  omega

theorem block_desubstitute {m h : ℕ} {c : Bool}
    (hh : h%2=0) (H : Block (m+1) h c) : Block m (h/2) c := by
  intro r hr
  have hpow : 2^(m+1)=2*2^m := by ring
  have H' := H (2*r) (by rw [hpow]; omega)
  have hindex : h+2*r=2*(h/2+r) := by omega
  rw [hindex,t_double,t_double] at H'
  exact H'

theorem block_divides {m h : ℕ} {c : Bool} (hm : 1≤m) (H : Block m h c) :
    2^(m-1) ∣ h := by
  induction m generalizing h with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m=0
    · subst m; simp
    · have hm1 : 1≤m := by omega
      have heven := block_even (by omega : 2≤m+1) H
      have H' := block_desubstitute heven H
      obtain ⟨a,ha⟩ := ih hm1 H'
      have hp : 2^m=2*2^(m-1) := by
        have hstep : m=(m-1)+1 := by omega
        conv_lhs => rw [hstep,Nat.pow_succ]
        ring
      refine ⟨a, ?_⟩
      simp only [Nat.add_sub_cancel]
      rw [hp]
      have hh : h=2*(h/2) := by omega
      rw [hh,ha]
      ring

/-- Exhaustive aligned/half-aligned cases for a full Thue–Morse block. -/
theorem block_cases {m h : ℕ} {c : Bool} (hm : 2≤m) (H : Block m h c) :
    (∃ l, h=l*2^m ∧ t l=c) ∨
    (∃ l, h=l*2^m+2^(m-1) ∧ t l= !c ∧ t (l+1)= !c) := by
  have hp : 2^m=2*2^(m-1) := by
    have hstep : m=(m-1)+1 := by omega
    conv_lhs => rw [hstep,Nat.pow_succ]
    ring
  obtain ⟨j,hj⟩ := block_divides (by omega : 1≤m) H
  have H0 := block_zero H
  have hhpos := pow_pos (m-1)
  by_cases he : j%2=0
  · left
    have hej : j=2*(j/2) := by omega
    have hform : h=(j/2)*2^m := by rw [hj,hp]; nlinarith [hej]
    refine ⟨j/2,hform,?_⟩
    rw [hform,t_mul_two_pow] at H0
    exact H0
  · right
    have hoj : j=2*(j/2)+1 := by omega
    have hform : h=(j/2)*2^m+2^(m-1) := by rw [hj,hp]; nlinarith [hoj]
    have hhalf : 2^(m-1)<2^m := by rw [hp]; omega
    have hmid := H (2^(m-1)) hhalf
    rw [hform,t_dyadic_block (j/2) m (2^(m-1)) hhalf,t_two_pow,xor_not] at H0
    have hmidindex : h+2^(m-1)=(j/2+1)*2^m := by rw [hform,hp]; ring
    rw [hmidindex,t_mul_two_pow,t_two_pow,xor_not] at hmid
    refine ⟨j/2,hform,?_,hmid⟩
    simpa using congrArg Bool.not H0

end ThueMorseMAP

namespace ThueMorseMAP
open ThueMorseBits

theorem run_at {m s d L k a b : ℕ} {c : Bool}
    (H : Run s d L c) (hk : k<L) (hb : b<2^m)
    (heq : s+k*d=a*2^m+b) : t a = Bool.xor c (t b) := by
  have he := H k hk
  rw [heq,t_dyadic_block a m b hb] at he
  exact (xor_eq_iff _ _ _).mp he

theorem tail_one (m : ℕ) : t (2^m-1)=decide (m%2=1) := by
  have h := complement m 0 (pow_pos m)
  simpa using h

theorem tail_two {m : ℕ} (hm : 2≤m) : t (2^m-2)=!(t (2^m-1)) := by
  have hp := pow_ge_four hm
  have h := complement m 1 (by omega)
  have he : 2^m-1-1=2^m-2 := by omega
  rw [he,t_one] at h
  rw [tail_one]
  simpa using h

theorem tail_three {m : ℕ} (hm : 2≤m) : t (2^m-3)=!(t (2^m-1)) := by
  have hp := pow_ge_four hm
  have h := complement m 2 (by omega)
  have he : 2^m-1-2=2^m-3 := by omega
  rw [he,t_two] at h
  rw [tail_one]
  simpa using h

theorem half_tail_one {m : ℕ} (hm : 2≤m) : t (2^(m-1)-1)=!(t (2^m-1)) := by
  rw [tail_one,tail_one]
  by_cases h1 : m%2=1
  · have h0 : (m-1)%2=0 := by omega
    simp [h1,h0]
  · have h0 : (m-1)%2=1 := by omega
    simp [h1,h0]

theorem half_tail_two {m : ℕ} (hm : 2≤m) : t (2^(m-1)-2)=t (2^m-1) := by
  have hhalf : 2≤2^(m-1) := by
    have := ThueMorseBits.index_lt_two_pow (m-1)
    omega
  have h := complement (m-1) 1 (by omega)
  have he : 2^(m-1)-1-1=2^(m-1)-2 := by omega
  rw [he,t_one] at h
  rw [tail_one]
  by_cases h1 : m%2=1
  · have h0 : (m-1)%2=0 := by omega
    simpa [h1,h0] using h
  · have h0 : (m-1)%2=1 := by omega
    simpa [h1,h0] using h

end ThueMorseMAP
