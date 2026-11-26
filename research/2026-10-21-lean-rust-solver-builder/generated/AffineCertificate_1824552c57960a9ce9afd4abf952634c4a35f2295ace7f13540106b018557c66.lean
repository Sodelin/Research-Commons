import AffineCertificateReceiver

/-! Literal finite-matrix certificate; no source/chart or native-origin premise.
Request SHA256: f6546bf096afc6ca96ea5bea2fed26dd7938cdff3e02f6d831a462afd3b44160
Certificate SHA256: d35b0673e6e7f1f634d080ff1ec44fda070d59fc7ef83f27a16a92a4774a8454 -/
namespace Astra.Generated.AffineCertificate_1824552c57960a9ce9afd4abf952634c4a35f2295ace7f13540106b018557c66

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness
open Astra.NativeAffineCertificates

def originalRows : Fin 3 → Row 2 :=
  ![{ coeff := ![((1 : ℚ) / 1), ((0 : ℚ) / 1)], bound := ((1 : ℚ) / 1), strict := false }, { coeff := ![((1 : ℚ) / 1), ((0 : ℚ) / 1)], bound := ((1 : ℚ) / 1), strict := false }, { coeff := ![((0 : ℚ) / 1), ((-1 : ℚ) / 1)], bound := ((0 : ℚ) / 1), strict := true }]

def point : Fin 2 → ℚ := ![((1 : ℚ) / 1), ((1 : ℚ) / 1)]

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

end Astra.Generated.AffineCertificate_1824552c57960a9ce9afd4abf952634c4a35f2295ace7f13540106b018557c66
