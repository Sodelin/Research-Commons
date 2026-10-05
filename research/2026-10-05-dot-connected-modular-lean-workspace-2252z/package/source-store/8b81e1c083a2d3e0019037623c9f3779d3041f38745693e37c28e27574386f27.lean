import ThueMorseMAP.Basic

namespace ThueMorseMAP
open ThueMorseBits

/-- The antidiagonal witness, uniformly over every odd positive exponent. -/
theorem odd_minus_witness (m : ℕ) (hm : m%2=1) :
    Run (2^m-1) (2^m-1) (2^m) true := by
  intro k hk
  have hp := pow_pos m
  have heq : (2^m-1)+k*(2^m-1)=k*2^m+(2^m-1-k) := by
    have h1 := Nat.sub_add_cancel (by omega : 1≤2^m)
    have h2 := Nat.sub_add_cancel (by omega : k≤2^m-1)
    nlinarith
  rw [heq, t_dyadic_block k m (2^m-1-k) (by omega), complement m k hk]
  simp only [hm, decide_true]
  cases t k <;> rfl

/-- Every proposed longer progression has an opposite-parity low-block wrap. -/
theorem odd_minus_upper (m s : ℕ) (hm : m%2=1) :
    ¬ Mono s (2^m-1) (2^m+1) := by
  intro ⟨c,h⟩
  have hp := pow_pos m
  let q := 2^m
  let a := s/q
  let b := s%q
  have hq : 0<q := hp
  have hb : b<q := Nat.mod_lt s hq
  have hs : s=a*q+b := by
    dsimp [a,b]
    simpa [Nat.add_comm,Nat.mul_comm] using (Nat.mod_add_div s q).symm
  have h0 := h b (by omega)
  have h1 := h (b+1) (by omega)
  have heq0 : s+b*(q-1)=(a+b)*q := by
    have hsub := Nat.sub_add_cancel (by omega : 1≤q)
    nlinarith
  have heq1 : s+(b+1)*(q-1)=(a+b)*q+(q-1) := by
    have hsub := Nat.sub_add_cancel (by omega : 1≤q)
    nlinarith
  change t (s+b*(q-1))=c at h0
  change t (s+(b+1)*(q-1))=c at h1
  rw [heq0] at h0
  rw [heq1] at h1
  dsimp [q] at h0 h1
  rw [t_mul_two_pow] at h0
  rw [t_dyadic_block (a+b) m (2^m-1) (by omega)] at h1
  have hend := complement m 0 (by omega : 0<2^m)
  simp only [Nat.sub_zero,t_zero,Bool.false_xor,hm,decide_true] at hend
  rw [hend,xor_not,h0] at h1
  cases c <;> contradiction

/-- No smaller start can even support the claimed maximal length. -/
theorem odd_minus_earliest (m s : ℕ) (hm : m%2=1) (hs : s<2^m-1) :
    ¬ Mono s (2^m-1) (2^m) := by
  intro ⟨c,h⟩
  have hp := pow_pos m
  have h0 := h s (by omega)
  have h1 := h (s+1) (by omega)
  have heq0 : s+s*(2^m-1)=s*2^m := by
    have hsub := Nat.sub_add_cancel (by omega : 1≤2^m)
    nlinarith
  have heq1 : s+(s+1)*(2^m-1)=s*2^m+(2^m-1) := by
    have hsub := Nat.sub_add_cancel (by omega : 1≤2^m)
    nlinarith
  rw [heq0,t_mul_two_pow] at h0
  rw [heq1,t_dyadic_block s m (2^m-1) (by omega)] at h1
  have hend := complement m 0 (by omega : 0<2^m)
  simp only [Nat.sub_zero,t_zero,Bool.false_xor,hm,decide_true] at hend
  rw [hend,xor_not,h0] at h1
  cases c <;> contradiction

/-- The full earliest-global-maximum claim has no assumed length theorem. -/
theorem odd_minus_first_maximum (m : ℕ) (hm : m%2=1) :
    FirstMaximum (2^m-1) (2^m) (2^m-1) := by
  exact ⟨⟨true,odd_minus_witness m hm⟩,
    fun s => odd_minus_upper m s hm, fun s hs => odd_minus_earliest m s hm hs⟩

#print axioms odd_minus_first_maximum
end ThueMorseMAP
