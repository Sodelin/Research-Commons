import AffineCertificateReceiver

/-! Literal finite-matrix certificate; no source/chart or native-origin premise.
Request SHA256: 95768e264140da6f814b00c5d5b0640fb614115a7b431cbb8bdc324f5baddd84
Certificate SHA256: 0dcd9165b79fc318fb90ce2929480c702e73465284bc238e8244747537e6fb4f -/
namespace Astra.Generated.AffineCertificate_861dab33cd7fb50134d98158f9086e8c27e1de6ad91be4b8191e274aca7d673c

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness
open Astra.NativeAffineCertificates

def originalRows : Fin 2 → Row 1 :=
  ![{ coeff := ![((-1 : ℚ) / 1)], bound := ((0 : ℚ) / 1), strict := true }, { coeff := ![((1 : ℚ) / 1)], bound := ((1 : ℚ) / 1), strict := true }]

def point : Fin 1 → ℚ := ![((1 : ℚ) / 2)]

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

end Astra.Generated.AffineCertificate_861dab33cd7fb50134d98158f9086e8c27e1de6ad91be4b8191e274aca7d673c
