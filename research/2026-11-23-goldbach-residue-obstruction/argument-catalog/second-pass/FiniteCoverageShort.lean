import FactorBoundary

namespace GoldbachCatalog

def FinCheck (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ d : Fin n, 1 < d.val → n % d.val ≠ 0

instance (n : Nat) : Decidable (FinCheck n) := by
  unfold FinCheck
  infer_instance

def firstPrimeWitness : Fin 8 → Nat :=
  fun k => ([11, 5, 5, 11, 11, 5, 5, 5, 5, 13, 5, 29, 5, 5, 11, 11, 5, 23, 5, 5, 19, 5, 11, 11] : List Nat)[k.val]?.getD 0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 20000000 in
theorem finite_checks :
    ∀ k : Fin 8, FinCheck (firstPrimeWitness k) ∧
      FinCheck (auditTarget k.val - firstPrimeWitness k) ∧
      firstPrimeWitness k ≤ auditTarget k.val := by
  decide

theorem finite_coverage_8 :
    ∀ k : Nat, k < 8 → PrimePair (auditTarget k) := by
  intro k hk
  let i : Fin 8 := ⟨k, hk⟩
  let p := firstPrimeWitness i
  obtain ⟨hp, hq, hn⟩ := finite_checks i
  exact ⟨p, auditTarget k - p, primeFromFin hp.1 hp.2,
    primeFromFin hq.1 hq.2, by
      change p ≤ auditTarget k at hn
      omega⟩

theorem conditional_from_8
    (supply : ∀ k, 8 ≤ k → SmallFactorCandidate (auditTarget k)) :
    ∀ k, PrimePair (auditTarget k) :=
  combine_at_threshold 8 finite_coverage_8 supply

#print axioms finite_coverage_8
#print axioms conditional_from_8
end GoldbachCatalog
