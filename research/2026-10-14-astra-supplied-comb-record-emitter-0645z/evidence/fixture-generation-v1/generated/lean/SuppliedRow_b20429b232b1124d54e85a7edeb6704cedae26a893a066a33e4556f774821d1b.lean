import Support_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b
import Astra.SuppliedCombCertificateAssembly

/- Literal input-only certificate; generation is not compilation. -/
namespace Astra.GeneratedSuppliedRow.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b
open DotG3.CertifiedCommonBoundedWitness
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open scoped BigOperators

noncomputable def values (k : Nat) : ℝ := if k = 1 then ((1 : ℝ) / 1) else if k = 2 then ((1 : ℝ) / 2) else if k = 3 then ((1 : ℝ) / 8) else 0

noncomputable def certificate : SuppliedCombCertificates Unit where
  level _ := 3
  value _ := values
  coeff _ := Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.coefficients
  level_pos _ := by decide
  nonzero := by
    intro _ hz
    apply Astra.Generated.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.nonzero_value
    rw [Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.polynomial_identity, hz, Polynomial.eval_zero]
  nonnegative := by
    intro _ x hx
    rw [← Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.polynomial_identity]
    exact Astra.Generated.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.nonnegative x hx.1 hx.2
  annihilates := by
    intro _
    change (∑ k ∈ momentLevels 3, Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.coefficients k * values k) = 0
    calc
      _ = (((1 : ℝ) / 4) * ((1 : ℝ) / 1) + ((-3 : ℝ) / 4) * ((1 : ℝ) / 2) + ((1 : ℝ) / 1) * ((1 : ℝ) / 8)) := by
        rw [Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.levels_eq]
        norm_num [Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.coefficients, values]
      _ = 0 := Astra.Generated.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.annihilation

#check certificate
#print axioms certificate
end Astra.GeneratedSuppliedRow.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b
