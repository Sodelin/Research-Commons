import AffineCertificateReceiver

/-! Authored literal controls, not an actual native execution record. -/
namespace Astra.NativeAffineCertificates.Examples

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness

def intervalRows (a : Fin 2) : Row 1 where
  coeff _ := if a.val = 0 then -1 else 1
  bound := if a.val = 0 then 0 else 1
  strict := true

def intervalPoint : Fin 1 → ℚ := fun _ => 1/2

theorem interval_checked :
    checkRationalWitness (rowsSet intervalRows) intervalPoint = true := by decide

theorem interval_real :
    ∀ a, (intervalRows a).Holds (fun j => (intervalPoint j : ℝ)) :=
  checked_witness_real intervalRows intervalPoint interval_checked

/-- x>0 and x<=0 on the SAME original coordinate. -/
def contradictoryRows (a : Fin 2) : Row 1 where
  coeff _ := if a.val = 0 then -1 else 1
  bound := 0
  strict := decide (a.val = 0)

def unitWeights : Fin 2 → ℚ := fun _ => 1

theorem contradiction_checked : checkFarkas contradictoryRows unitWeights = true := by decide

theorem contradiction_real :
    ¬ ∃ x : Fin 1 → ℝ, ∀ a, (contradictoryRows a).Holds x :=
  checked_farkas_infeasible contradictoryRows unitWeights contradiction_checked

/-- The only strict original row is 0<1 and receives multiplier ZERO.
The weak pair permits x=0; this must not be certified as an exclusion. -/
def zeroStrictRows (a : Fin 3) : Row 1 where
  coeff _ := if a.val = 0 then 0 else if a.val = 1 then -1 else 1
  bound := if a.val = 0 then 1 else 0
  strict := decide (a.val = 0)

def zeroStrictWeights (a : Fin 3) : ℚ := if a.val = 0 then 0 else 1

theorem zero_strict_not_exclusion : checkFarkas zeroStrictRows zeroStrictWeights = false := by decide

theorem zero_strict_witness :
    checkRationalWitness (rowsSet zeroStrictRows) (fun _ => 0) = true := by decide

end Astra.NativeAffineCertificates.Examples
