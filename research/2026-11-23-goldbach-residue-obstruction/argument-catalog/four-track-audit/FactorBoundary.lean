import Assembly

namespace GoldbachCatalog

theorem factorFive_family (k : Nat) :
    auditTarget k = 37 + 5 * (42 * k + 31) := by
  unfold auditTarget
  omega

theorem primeFromFin {n : Nat} (hn : 2 ≤ n)
    (check : ∀ d : Fin n, 1 < d.val → n % d.val ≠ 0) : Prime n :=
  ⟨hn, fun d h1 h2 => check ⟨d, h2⟩ h1⟩

set_option maxRecDepth 10000 in
theorem factorFive_example :
    Prime 37 ∧ Prime 31 ∧ auditTarget 0 = 37 + 5 * 31 := by
  exact ⟨primeFromFin (by decide) (by decide),
    primeFromFin (by decide) (by decide), factorFive_family 0⟩

#print axioms factorFive_family
#print axioms factorFive_example
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem reducedResidueCertificate :
    ∀ r : Fin 210, Nat.gcd r.val 6 = 1 →
      ∃ u : Fin 210, Nat.gcd u.val 210 = 1 ∧
        Nat.gcd ((192 + 210 - ((r.val * u.val) % 210)) % 210) 210 = 1 := by
  decide

#print axioms reducedResidueCertificate
def allowedResidues (r : Nat) : Nat :=
  ((List.finRange 210).filter (fun u =>
    decide (Nat.gcd u.val 210 = 1 ∧
      Nat.gcd ((192 + 210 - ((r * u.val) % 210)) % 210) 210 = 1))).length

set_option maxRecDepth 10000 in
theorem example_local_counts :
    allowedResidues 1 = 30 ∧ allowedResidues 2 = 0 ∧
    allowedResidues 3 = 0 ∧ allowedResidues 5 = 40 ∧
    allowedResidues 7 = 36 := by decide

#print axioms example_local_counts
end GoldbachCatalog
