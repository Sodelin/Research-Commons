import Lean

namespace GoldbachCatalog

/-- Elementary no-proper-divisor formulation on natural numbers. -/
def Prime (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ d : Nat, 1 < d → d < n → n % d ≠ 0

def PrimePair (n : Nat) : Prop :=
  ∃ p q : Nat, Prime p ∧ Prime q ∧ n = p + q

/-- Only these possible smaller factors remain after the moving cap is below five. -/
def SmallFactorCandidate (n : Nat) : Prop :=
  ∃ p q r : Nat,
    Prime p ∧ Prime q ∧ (r = 1 ∨ r = 2 ∨ r = 3) ∧ n = p + r * q

def auditTarget (k : Nat) : Nat := 210 * k + 192

theorem primePair_implies_candidate {n : Nat}
    (h : PrimePair n) : SmallFactorCandidate n := by
  obtain ⟨p, q, hp, hq, hn⟩ := h
  exact ⟨p, q, 1, hp, hq, Or.inl rfl, by simpa using hn⟩

theorem no_factor_two (k p q : Nat)
    (hp : Prime p) (hq : Prime q) (h : auditTarget k = p + 2 * q) :
    False := by
  unfold auditTarget at h
  have hp2 : p % 2 = 0 := by omega
  have notBig : ¬ 2 < p := fun hb => hp.2 2 (by decide) hb hp2
  have peq : p = 2 := by have := hp.1; omega
  have hq5 : q % 5 = 0 := by omega
  have hqBig : 5 < q := by omega
  exact hq.2 5 (by decide) hqBig hq5

theorem no_factor_three (k p q : Nat)
    (hp : Prime p) (hq : Prime q) (h : auditTarget k = p + 3 * q) :
    False := by
  unfold auditTarget at h
  have hp3 : p % 3 = 0 := by omega
  have notBig : ¬ 3 < p := fun hb => hp.2 3 (by decide) hb hp3
  have peq : p = 3 := by have := hp.1; omega
  have hq7 : q % 7 = 0 := by omega
  have hqBig : 7 < q := by omega
  exact hq.2 7 (by decide) hqBig hq7

theorem auditCandidate_implies_primePair (k : Nat)
    (h : SmallFactorCandidate (auditTarget k)) : PrimePair (auditTarget k) := by
  obtain ⟨p, q, r, hp, hq, hr, hn⟩ := h
  rcases hr with r1 | r2 | r3
  · subst r
    exact ⟨p, q, hp, hq, by simpa using hn⟩
  · subst r
    exact False.elim (no_factor_two k p q hp hq hn)
  · subst r
    exact False.elim (no_factor_three k p q hp hq hn)

theorem auditClass_iff (k : Nat) :
    SmallFactorCandidate (auditTarget k) ↔ PrimePair (auditTarget k) :=
  ⟨auditCandidate_implies_primePair k, primePair_implies_candidate⟩

/-- The unproved candidate-supply estimate is an explicit premise, not an axiom. -/
theorem combine_at_threshold (K : Nat)
    (finite : ∀ k, k < K → PrimePair (auditTarget k))
    (supply : ∀ k, K ≤ k → SmallFactorCandidate (auditTarget k)) :
    ∀ k, PrimePair (auditTarget k) := by
  intro k
  by_cases h : k < K
  · exact finite k h
  · exact auditCandidate_implies_primePair k (supply k (by omega))

#print axioms auditClass_iff
#print axioms combine_at_threshold
end GoldbachCatalog
