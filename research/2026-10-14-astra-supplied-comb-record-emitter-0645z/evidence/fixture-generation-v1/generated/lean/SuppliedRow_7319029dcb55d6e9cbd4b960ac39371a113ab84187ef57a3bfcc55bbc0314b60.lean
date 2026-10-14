import Support_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60
import Astra.SuppliedCombCertificateAssembly

/- Literal input-only certificate; generation is not compilation. -/
namespace Astra.GeneratedSuppliedRow.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60
open DotG3.CertifiedCommonBoundedWitness
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open scoped BigOperators

noncomputable def values (k : Nat) : ℝ := if k = 1 then ((1 : ℝ) / 1) else if k = 2 then ((0 : ℝ) / 1) else if k = 3 then ((0 : ℝ) / 1) else if k = 4 then ((0 : ℝ) / 1) else if k = 5 then ((0 : ℝ) / 1) else if k = 6 then ((0 : ℝ) / 1) else if k = 7 then ((0 : ℝ) / 1) else if k = 8 then ((0 : ℝ) / 1) else 0

noncomputable def certificate : SuppliedCombCertificates Unit where
  level _ := 8
  value _ := values
  coeff _ := Astra.GeneratedSupport.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60.coefficients
  level_pos _ := by decide
  nonzero := by
    intro _ hz
    apply Astra.Generated.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60.nonzero_value
    rw [Astra.GeneratedSupport.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60.polynomial_identity, hz, Polynomial.eval_zero]
  nonnegative := by
    intro _ x hx
    rw [← Astra.GeneratedSupport.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60.polynomial_identity]
    exact Astra.Generated.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60.nonnegative x hx.1 hx.2
  annihilates := by
    intro _
    change (∑ k ∈ momentLevels 8, Astra.GeneratedSupport.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60.coefficients k * values k) = 0
    calc
      _ = (((0 : ℝ) / 1) * ((1 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((0 : ℝ) / 1) * ((0 : ℝ) / 1) + ((1 : ℝ) / 1) * ((0 : ℝ) / 1)) := by
        rw [Astra.GeneratedSupport.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60.levels_eq]
        norm_num [Astra.GeneratedSupport.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60.coefficients, values]
      _ = 0 := Astra.Generated.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60.annihilation

#check certificate
#print axioms certificate
end Astra.GeneratedSuppliedRow.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60
