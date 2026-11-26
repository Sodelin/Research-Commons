import Lean
set_option warningAsError true

namespace AlexanderOmnibus

def pairCode (a b : Nat) : Nat := (a + b) * (a + b) + a

private theorem square_gap (x a : Nat) (ha : a ≤ x) :
    x * x + a < (x + 1) * (x + 1) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem pairCode_injective {a b c d : Nat} (he : pairCode a b = pairCode c d) :
    a = c ∧ b = d := by
  unfold pairCode at he
  have hsum : a+b = c+d := by
    rcases Nat.lt_trichotomy (a+b) (c+d) with h | h | h
    · have hs : a+b+1 ≤ c+d := by omega
      have hh := Nat.mul_le_mul hs hs
      have hg := square_gap (a+b) a (by omega)
      omega
    · exact h
    · have hs : c+d+1 ≤ a+b := by omega
      have hh := Nat.mul_le_mul hs hs
      have hg := square_gap (c+d) c (by omega)
      omega
  rw [hsum] at he
  exact ⟨by omega, by omega⟩

def tripleCode (a b c : Nat) : Nat := pairCode a (pairCode b c)

theorem tripleCode_injective {a b c p q r : Nat}
    (h : tripleCode a b c = tripleCode p q r) : a = p ∧ b = q ∧ c = r := by
  obtain ⟨ha, hh⟩ := pairCode_injective h
  exact ⟨ha, pairCode_injective hh⟩

/-- Entries encode a host number, its deleted-prefix cutoff, and a retained
component representative; there is no need to enumerate arbitrary finite sets. -/
def diagonal (signature : Nat → Nat → Nat → Nat → Prop) (n : Nat) : Prop :=
  ∀ a b c, tripleCode a b c = n → ¬ signature a b c n

theorem diagonal_at (signature : Nat → Nat → Nat → Nat → Prop) (a b c : Nat) :
    diagonal signature (tripleCode a b c) ↔
      ¬ signature a b c (tripleCode a b c) := by
  constructor
  · intro h
    exact h a b c rfl
  · intro h p q r hh
    obtain ⟨hp, hq, hr⟩ := tripleCode_injective hh
    rwa [hp, hq, hr]

theorem diagonal_differs (signature : Nat → Nat → Nat → Nat → Prop) (a b c : Nat) :
    ¬ ∀ n, diagonal signature n ↔ signature a b c n := by
  intro h
  let n := tripleCode a b c
  have equiv := (diagonal_at signature a b c).symm.trans (h n)
  have hn : ¬ signature a b c n := fun p => (equiv.mpr p) p
  exact hn (equiv.mp hn)

#print axioms tripleCode_injective
#print axioms diagonal_differs
end AlexanderOmnibus
