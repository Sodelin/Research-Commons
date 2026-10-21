import AffineCertificateReceiver

/-! Literal finite-matrix certificate; no source/chart or native-origin premise.
Request SHA256: 7125725420043a221745e877b12a959824ab037992bda7f4521609669b755247
Certificate SHA256: 6686f10f623f1d12fb6d5832b371fba5e5a6ba94f1efb5941922e498f514d91b -/
namespace Astra.Generated.AffineCertificate_8b333840de5495917bda5a5f1d611cb212494f6b2e2c64c11f4f1a6192aac0ec

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness
open Astra.NativeAffineCertificates

def originalRows : Fin 0 → Row 0 :=
  ![]

def point : Fin 0 → ℚ := ![]

theorem value_checked :
    checkRationalWitness (rowsSet originalRows) point = true := by
  apply (checkRationalWitness_correct _ _).mpr
  intro row hrow
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hrow
  fin_cases a <;> norm_num [originalRows, point, Row.Holds, Row.eval,
    UnifiedLean.G6.StrictAffineElimination.Rel, Fin.sum_univ_succ]

theorem original_rows_hold :
    ∀ a, (originalRows a).Holds (fun j => (point j : ℝ)) :=
  checked_witness_real originalRows point value_checked

end Astra.Generated.AffineCertificate_8b333840de5495917bda5a5f1d611cb212494f6b2e2c64c11f4f1a6192aac0ec
