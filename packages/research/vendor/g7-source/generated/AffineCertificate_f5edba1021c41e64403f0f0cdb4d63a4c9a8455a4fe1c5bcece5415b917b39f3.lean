import AffineCertificateReceiver

/-! Literal finite-matrix certificate; no source/chart or native-origin premise.
Request SHA256: c97bbd5c0f99b318a86d58201313caed4d13abbe77b424ea860adff16b28074a
Certificate SHA256: b6d461081e2a7b137132d78f2e7c1f5e118c5c624b495f2a6bebfc0bc9d25c08 -/
namespace Astra.Generated.AffineCertificate_f5edba1021c41e64403f0f0cdb4d63a4c9a8455a4fe1c5bcece5415b917b39f3

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness
open Astra.NativeAffineCertificates

def originalRows : Fin 2 → Row 1 :=
  ![{ coeff := ![((-1 : ℚ) / 1)], bound := ((-1 : ℚ) / 1), strict := false }, { coeff := ![((1 : ℚ) / 1)], bound := ((0 : ℚ) / 1), strict := false }]

def multipliers : Fin 2 → ℚ := ![((1 : ℚ) / 1), ((1 : ℚ) / 1)]

theorem value_checked : checkFarkas originalRows multipliers = true := by
  norm_num [checkFarkas, originalRows, multipliers, Fin.sum_univ_succ,
    Fin.forall_fin_succ, Fin.exists_fin_succ]

theorem original_rows_infeasible :
    ¬ ∃ x : Fin 1 → ℝ, ∀ a, (originalRows a).Holds x :=
  checked_farkas_infeasible originalRows multipliers value_checked

end Astra.Generated.AffineCertificate_f5edba1021c41e64403f0f0cdb4d63a4c9a8455a4fe1c5bcece5415b917b39f3
