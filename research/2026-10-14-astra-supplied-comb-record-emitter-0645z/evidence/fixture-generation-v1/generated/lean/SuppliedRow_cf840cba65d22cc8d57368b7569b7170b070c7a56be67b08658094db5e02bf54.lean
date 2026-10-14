import Support_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54
import Astra.SuppliedCombCertificateAssembly

/- Literal input-only certificate; generation is not compilation. -/
namespace Astra.GeneratedSuppliedRow.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54
open DotG3.CertifiedCommonBoundedWitness
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open scoped BigOperators

noncomputable def values (k : Nat) : ℝ := if k = 1 then ((1 : ℝ) / 1) else if k = 2 then ((0 : ℝ) / 1) else 0

noncomputable def certificate : SuppliedCombCertificates Unit where
  level _ := 2
  value _ := values
  coeff _ := Astra.GeneratedSupport.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54.coefficients
  level_pos _ := by decide
  nonzero := by
    intro _ hz
    apply Astra.Generated.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54.nonzero_value
    rw [Astra.GeneratedSupport.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54.polynomial_identity, hz, Polynomial.eval_zero]
  nonnegative := by
    intro _ x hx
    rw [← Astra.GeneratedSupport.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54.polynomial_identity]
    exact Astra.Generated.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54.nonnegative x hx.1 hx.2
  annihilates := by
    intro _
    change (∑ k ∈ momentLevels 2, Astra.GeneratedSupport.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54.coefficients k * values k) = 0
    calc
      _ = (((0 : ℝ) / 1) * ((1 : ℝ) / 1) + ((1 : ℝ) / 1) * ((0 : ℝ) / 1)) := by
        rw [Astra.GeneratedSupport.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54.levels_eq]
        norm_num [Astra.GeneratedSupport.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54.coefficients, values]
      _ = 0 := Astra.Generated.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54.annihilation

#check certificate
#print axioms certificate
end Astra.GeneratedSuppliedRow.Certificate_cf840cba65d22cc8d57368b7569b7170b070c7a56be67b08658094db5e02bf54
