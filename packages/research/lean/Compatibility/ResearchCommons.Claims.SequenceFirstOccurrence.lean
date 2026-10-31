import ThueMorseMAP.Headline

/-! Existing CB-SEQ-001: exact owner/type export join only.
No new first-occurrence proof or executable algorithm. Source A/i/Mono/Center
remain the original imported definitions. Package binding is NOT adopted. -/
set_option autoImplicit false
set_option debug.skipKernelTC false
noncomputable section
namespace ResearchCommons.Claims.SequenceFirstOccurrence
open ThueMorseMAP

theorem plus_first_occurrence (n : ℕ) (hn : 2 ≤ n) :
    A (2^n+1) = 2^n+2 ∧ i (2^n+1) = 3*2^(2*n)-2^n-1 :=
  ThueMorseMAP.conjecture_3_8_plus n hn

theorem even_minus_first_occurrence (n : ℕ) (hn : 1 ≤ n) :
    A (2^(2*n)-1) = 2^(2*n)+4 ∧
      i (2^(2*n)-1) = 3*2^(4*n)-2^(2*n)+1 :=
  ThueMorseMAP.conjecture_3_8_even_minus n hn

theorem odd_minus_first_occurrence (n : ℕ) :
    A (2^(2*n+1)-1) = 2^(2*n+1) ∧
      i (2^(2*n+1)-1) = 2^(2*n+1)-1 :=
  ThueMorseMAP.conjecture_3_8_odd_minus n

theorem plus_all_starts {m s : ℕ} (hm : 2 ≤ m) :
    Mono s (2^m+1) (2^m+2) ↔
      ∃ l, Center l ∧ s+2^m+1 = l*2^m*2^m :=
  ThueMorseMAP.plus_classification hm

theorem even_minus_all_starts {m s : ℕ} (hm : 2 ≤ m) (hp : m % 2 = 0) :
    Mono s (2^m-1) (2^m+4) ↔
      ∃ l, Center l ∧ s+2^m = l*2^m*2^m+1 :=
  ThueMorseMAP.even_minus_classification hm hp

theorem canonical_three_families :
    (∀ n : ℕ, 2 ≤ n → A (2^n+1) = 2^n+2 ∧
      i (2^n+1) = 3*2^(2*n)-2^n-1) ∧
    (∀ n : ℕ, 1 ≤ n → A (2^(2*n)-1) = 2^(2*n)+4 ∧
      i (2^(2*n)-1) = 3*2^(4*n)-2^(2*n)+1) ∧
    (∀ n : ℕ, A (2^(2*n+1)-1) = 2^(2*n+1) ∧
      i (2^(2*n+1)-1) = 2^(2*n+1)-1) :=
  ⟨plus_first_occurrence,even_minus_first_occurrence,odd_minus_first_occurrence⟩
end ResearchCommons.Claims.SequenceFirstOccurrence
