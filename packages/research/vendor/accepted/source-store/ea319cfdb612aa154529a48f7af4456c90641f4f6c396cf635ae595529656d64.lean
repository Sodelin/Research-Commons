import ThueMorseMAP.OddMinus
import ThueMorseMAP.EvenMinus
import ThueMorseMAP.Plus

namespace ThueMorseMAP

/-- Global maximum progression length. On the proved families the defining set
is nonempty and bounded, and the maximum is attained. -/
noncomputable def A (d : ℕ) : ℕ := sSup {L : ℕ | ∃ s, Mono s d L}

/-- Earliest start attaining the global maximum; this is Joshi–Rust's i(d). -/
noncomputable def i (d : ℕ) : ℕ := sInf {s : ℕ | Mono s d (A d)}

theorem Mono.truncate {s d L K : ℕ} (H : Mono s d L) (h : K≤L) : Mono s d K := by
  rcases H with ⟨c,H⟩
  exact ⟨c,fun k hk => H k (by omega)⟩

theorem FirstMaximum.bindings {d L s : ℕ} (H : FirstMaximum d L s) : A d=L ∧ i d=s := by
  rcases H with ⟨Hw,Hu,He⟩
  have HL : A d=L := by
    apply IsGreatest.csSup_eq
    constructor
    · exact ⟨s,Hw⟩
    · rintro K ⟨a,HK⟩
      by_contra hnot
      exact Hu a (HK.truncate (by omega))
  refine ⟨HL,?_⟩
  unfold i
  rw [HL]
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨s,Hw⟩
  · intro a Ha
    by_contra hnot
    exact He a (by omega) Ha
  · intro w hw
    exact ⟨s,Hw,hw⟩

/-- Joshi–Rust Conjecture 3.8, first displayed family, including its exact length. -/
theorem conjecture_3_8_plus (n : ℕ) (hn : 2≤n) :
    A (2^n+1)=2^n+2 ∧ i (2^n+1)=3*2^(2*n)-2^n-1 := by
  have H := FirstMaximum.bindings (plus_first_maximum hn)
  have he : 2^(2*n)=2^n*2^n := by rw [show 2*n=n+n by omega,pow_add]
  simpa [he,Nat.mul_assoc] using H

/-- Second displayed family, with n≥1, including the prior exact length. -/
theorem conjecture_3_8_even_minus (n : ℕ) (hn : 1≤n) :
    A (2^(2*n)-1)=2^(2*n)+4 ∧
    i (2^(2*n)-1)=3*2^(4*n)-2^(2*n)+1 := by
  have H := FirstMaximum.bindings (even_minus_first_maximum (m:=2*n) (by omega) (by omega))
  have he : 2^(4*n)=2^(2*n)*2^(2*n) := by rw [show 4*n=2*n+2*n by omega,pow_add]
  simpa [he,Nat.mul_assoc] using H

/-- Third displayed family, including n=0 and its exact maximal length. -/
theorem conjecture_3_8_odd_minus (n : ℕ) :
    A (2^(2*n+1)-1)=2^(2*n+1) ∧ i (2^(2*n+1)-1)=2^(2*n+1)-1 := by
  exact FirstMaximum.bindings (odd_minus_first_maximum (2*n+1) (by omega))

#print axioms conjecture_3_8_plus
#print axioms conjecture_3_8_even_minus
#print axioms conjecture_3_8_odd_minus
#print axioms plus_classification
#print axioms even_minus_classification
end ThueMorseMAP
