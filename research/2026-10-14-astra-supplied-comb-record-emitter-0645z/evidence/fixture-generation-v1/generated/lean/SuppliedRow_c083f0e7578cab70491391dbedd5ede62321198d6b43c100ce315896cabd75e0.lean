import Support_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0
import Astra.SuppliedCombCertificateAssembly

/- Literal input-only certificate; generation is not compilation. -/
namespace Astra.GeneratedSuppliedRow.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0
open DotG3.CertifiedCommonBoundedWitness
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open scoped BigOperators

noncomputable def values (k : Nat) : ℝ := if k = 1 then ((1 : ℝ) / 1) else if k = 2 then ((1 : ℝ) / 1) else if k = 3 then ((1 : ℝ) / 1) else 0

noncomputable def certificate : SuppliedCombCertificates Unit where
  level _ := 3
  value _ := values
  coeff _ := Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.coefficients
  level_pos _ := by decide
  nonzero := by
    intro _ hz
    apply Astra.Generated.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.nonzero_value
    rw [Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.polynomial_identity, hz, Polynomial.eval_zero]
  nonnegative := by
    intro _ x hx
    rw [← Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.polynomial_identity]
    exact Astra.Generated.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.nonnegative x hx.1 hx.2
  annihilates := by
    intro _
    change (∑ k ∈ momentLevels 3, Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.coefficients k * values k) = 0
    calc
      _ = (((2 : ℝ) / 1) * ((1 : ℝ) / 1) + ((-3 : ℝ) / 1) * ((1 : ℝ) / 1) + ((1 : ℝ) / 1) * ((1 : ℝ) / 1)) := by
        rw [Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.levels_eq]
        norm_num [Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.coefficients, values]
      _ = 0 := Astra.Generated.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.annihilation

#check certificate
#print axioms certificate
end Astra.GeneratedSuppliedRow.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0
