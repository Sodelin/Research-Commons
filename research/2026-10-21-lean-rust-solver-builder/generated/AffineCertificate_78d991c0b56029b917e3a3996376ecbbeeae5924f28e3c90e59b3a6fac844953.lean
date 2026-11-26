import AffineCertificateReceiver

/-! Literal finite-matrix certificate; no source/chart or native-origin premise.
Request SHA256: 74241e64a6d6358c321677e544df8ef22963f2036db76bccdb85e2e74f079bab
Certificate SHA256: 009685d46b5eff1719a9256722fcf9515b4b21a6d5ca5ac0e2222131b3f80642 -/
namespace Astra.Generated.AffineCertificate_78d991c0b56029b917e3a3996376ecbbeeae5924f28e3c90e59b3a6fac844953

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness
open Astra.NativeAffineCertificates

def originalRows : Fin 2 → Row 1 :=
  ![{ coeff := ![((-1 : ℚ) / 1)], bound := ((0 : ℚ) / 1), strict := true }, { coeff := ![((1 : ℚ) / 1)], bound := ((0 : ℚ) / 1), strict := false }]

def multipliers : Fin 2 → ℚ := ![((1 : ℚ) / 1), ((1 : ℚ) / 1)]

theorem value_checked : checkFarkas originalRows multipliers = true := by
  norm_num [checkFarkas, originalRows, multipliers, Fin.sum_univ_succ,
    Fin.forall_fin_succ, Fin.exists_fin_succ]

theorem original_rows_infeasible :
    ¬ ∃ x : Fin 1 → ℝ, ∀ a, (originalRows a).Holds x :=
  checked_farkas_infeasible originalRows multipliers value_checked

end Astra.Generated.AffineCertificate_78d991c0b56029b917e3a3996376ecbbeeae5924f28e3c90e59b3a6fac844953
