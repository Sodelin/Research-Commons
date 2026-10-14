import G3CertifiedCommonBoundedWitness

/-!
A literal input-record constructor. No actual source, physical admission,
moment-to-source equality, protected count, or desired law is an input.
Source proposal: this module has not yet been compiled.
-/
namespace Astra.SuppliedCombCertificateAssembly

open DotG3.CertifiedCommonBoundedWitness

/-- Assemble heterogeneous per-row certificates without changing their fields. -/
noncomputable def assemble {Y : Type*}
    (row : Y × Y → SuppliedCombCertificates Unit) : SuppliedCombCertificates Y where
  level ij := (row ij).level ((), ())
  value ij := (row ij).value ((), ())
  coeff ij := (row ij).coeff ((), ())
  level_pos ij := (row ij).level_pos ((), ())
  nonzero ij := (row ij).nonzero ((), ())
  nonnegative ij := (row ij).nonnegative ((), ())
  annihilates ij := (row ij).annihilates ((), ())

theorem assemble_level {Y : Type*}
    (row : Y × Y → SuppliedCombCertificates Unit) (ij : Y × Y) :
    (assemble row).level ij = (row ij).level ((), ()) := rfl

theorem assemble_value {Y : Type*}
    (row : Y × Y → SuppliedCombCertificates Unit) (ij : Y × Y) (k : Nat) :
    (assemble row).value ij k = (row ij).value ((), ()) k := rfl

theorem assemble_coeff {Y : Type*}
    (row : Y × Y → SuppliedCombCertificates Unit) (ij : Y × Y) (k : Nat) :
    (assemble row).coeff ij k = (row ij).coeff ((), ()) k := rfl

#print axioms assemble
#print axioms assemble_level
#print axioms assemble_value
#print axioms assemble_coeff

end Astra.SuppliedCombCertificateAssembly
