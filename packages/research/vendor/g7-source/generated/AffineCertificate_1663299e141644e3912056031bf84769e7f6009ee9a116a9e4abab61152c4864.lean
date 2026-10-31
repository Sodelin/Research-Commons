import AffineCertificateReceiver

/-! Literal finite-matrix certificate; no source/chart or native-origin premise.
Request SHA256: f48a12fed5a1030f3a478d5fddce88af3d9c4a8b87ab929b2b4900c424e43938
Certificate SHA256: e278eae2316b467f468f11b08f2e33b68fc18733d3d18681c90446d15aa88be5 -/
namespace Astra.Generated.AffineCertificate_1663299e141644e3912056031bf84769e7f6009ee9a116a9e4abab61152c4864

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness
open Astra.NativeAffineCertificates

def originalRows : Fin 3 → Row 1 :=
  ![{ coeff := ![((0 : ℚ) / 1)], bound := ((1 : ℚ) / 1), strict := true }, { coeff := ![((-1 : ℚ) / 1)], bound := ((0 : ℚ) / 1), strict := false }, { coeff := ![((1 : ℚ) / 1)], bound := ((0 : ℚ) / 1), strict := false }]

def point : Fin 1 → ℚ := ![((0 : ℚ) / 1)]

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

end Astra.Generated.AffineCertificate_1663299e141644e3912056031bf84769e7f6009ee9a116a9e4abab61152c4864
