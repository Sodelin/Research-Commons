import SamuelAlexanderResearch.ThueMorseBits

set_option debug.skipKernelTC false
namespace ResearchCommons.ThueMorsePhaseAliasing
open ThueMorseBits

def PeriodFrom (p N : Nat) : Prop := ∀ n, N ≤ n → t (n+p) = t n

theorem not_eventual_period (p N : Nat) (hp : 0 < p) : ¬ PeriodFrom p N := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro h
    let q := p / 2
    by_cases even : p % 2 = 0
    · have pq : p = 2*q := by dsimp [q]; omega
      have qpos : 0 < q := by omega
      have qlt : q < p := by omega
      apply ih q qlt qpos
      intro n hn
      have hh := h (2*n) (by omega)
      have e : 2*n+p = 2*(n+q) := by omega
      rwa [e, t_double, t_double] at hh
    · have pq : p = 2*q+1 := by dsimp [q]; omega
      have adj (n : Nat) (hn : N ≤ n) : t (n+q) = t (n+q+1) := by
        have h0 := h (2*n) (by omega)
        have h1 := h (2*n+1) (by omega)
        have e0 : 2*n+p = 2*(n+q)+1 := by omega
        have e1 : 2*n+1+p = 2*(n+q+1) := by omega
        rw [e0,t_double_add_one,t_double] at h0
        rw [e1,t_double,t_double_add_one] at h1
        have h0n := congrArg Bool.not h0
        rw [Bool.not_not] at h0n
        exact h0n.trans h1.symm
      have z := adj (2*N+q) (by omega)
      have e : 2*N+q+q = 2*(N+q) := by omega
      rw [e,t_double,t_double_add_one] at z
      cases hz : t (N+q) <;> simp [hz] at z

theorem not_eventual_complement (p N : Nat) (hp : 0 < p) :
    ¬ (∀ n, N ≤ n → t (n+p) = !(t n)) := by
  intro h
  apply not_eventual_period (2*p) N (by omega)
  intro n hn
  have hh := h (n+p) (by omega)
  have e : n+2*p = (n+p)+p := by omega
  rw [e,hh,h n hn]
  cases t n <;> rfl

theorem cofinal_match_and_mismatch (a b N : Nat) (ab : a < b) :
    (∃ n, N ≤ n ∧ t (n+a) = t (n+b)) ∧
    (∃ n, N ≤ n ∧ t (n+a) ≠ t (n+b)) := by
  let p := b-a
  have hp : 0 < p := by dsimp [p]; omega
  have lift (n : Nat) (hn : N+a ≤ n) :
      N ≤ n-a ∧ n-a+a = n ∧ n-a+b = n+p := by dsimp [p]; omega
  constructor
  · apply Classical.byContradiction
    intro he
    apply not_eventual_complement p (N+a) hp
    intro n hn
    obtain ⟨hN,ha,hb⟩ := lift n hn
    have neq : t n ≠ t (n+p) := by
      intro e
      exact he ⟨n-a,hN,by rwa [ha,hb]⟩
    cases h0 : t n <;> cases h1 : t (n+p) <;> simp_all
  · apply Classical.byContradiction
    intro he
    apply not_eventual_period p (N+a) hp
    intro n hn
    obtain ⟨hN,ha,hb⟩ := lift n hn
    apply Classical.byContradiction
    intro neq
    exact he ⟨n-a,hN,by rwa [ha,hb,ne_comm]⟩

/-- At every phase, arbitrarily far phases share the requested exact prefix,
but the agreement is never permanent (indeed, both outcomes occur cofinally). -/
theorem prefix_aliases_with_cofinal_separation (a len gap : Nat) :
    ∃ b, a+gap < b ∧ (∀ i, i < len → t (i+a) = t (i+b)) ∧
      ∀ N, (∃ i, N ≤ i ∧ t (i+a) = t (i+b)) ∧
           (∃ i, N ≤ i ∧ t (i+a) ≠ t (i+b)) := by
  let m := a+len+gap+1
  let b := a+3*2^m
  have big : m < 2^m := index_lt_two_pow m
  have sumlt : a+len+gap < m := by dsimp [m]; omega
  have far : a+gap < b := by dsimp only [b]; omega
  refine ⟨b,far,?_, fun N => cofinal_match_and_mismatch a b N (by omega)⟩
  intro i hi
  have low : i+a < 2^m := by omega
  have he : i+b = 3*2^m+(i+a) := by dsimp [b]; omega
  rw [he,t_dyadic_block 3 m (i+a) low,t_three]
  cases t (i+a) <;> rfl

/-- The offset used in the alias construction has an exact first mismatch:
the two absolute words agree on the first two full dyadic blocks and
differ at the first position of the third. -/
theorem triple_dyadic_first_mismatch (m : Nat) :
    (∀ n, n < 2*2^m → t n = t (n + 3*2^m)) ∧
    t (2*2^m) ≠ t (2*2^m + 3*2^m) := by
  constructor
  · intro n hn
    by_cases lo : n < 2^m
    · have e : n+3*2^m = 3*2^m+n := by omega
      rw [e,t_dyadic_block 3 m n lo,t_three]
      cases t n <;> rfl
    · let r := n-2^m
      have hr : r < 2^m := by dsimp [r]; omega
      have h1 : n = 1*2^m+r := by dsimp [r]; omega
      have h4 : n+3*2^m = 4*2^m+r := by omega
      rw [h4,h1,t_dyadic_block 1 m r hr,t_dyadic_block 4 m r hr,t_one,t_four]
  · have e : 2*2^m+3*2^m = 5*2^m := by omega
    rw [e,t_mul_two_pow,t_mul_two_pow,t_two,t_five]
    decide

#print axioms triple_dyadic_first_mismatch
#print axioms not_eventual_period
#print axioms not_eventual_complement
#print axioms cofinal_match_and_mismatch
#print axioms prefix_aliases_with_cofinal_separation

end ResearchCommons.ThueMorsePhaseAliasing
