import SamuelAlexanderResearch.DigitRecurrence
import SamuelAlexanderResearch.PhaseHeight
import SamuelAlexanderResearch.PhaseExtremal

/-! Exact existing CB-SEQ-004 graph/height/phase/digit owner interface.
Original Samuel development and source-side work retain credit. No new
mathematics, minimal recurrence, joint phase/start logarithmic algorithm or
integer bit-complexity result. Binding pending full correspondence review. -/
namespace ResearchCommons.Claims.MatchingHeights
open ThueMorseBits BinaryAvoidance QuantitativeAvoidance FiniteEditStability
open FullHeight DigitRecurrence PhaseShift

theorem base_maximum (v : Nat) : IsMaximumPrefix t v (FullHeight.height v) :=
  FullHeight.height_isMaximum v

theorem base_closed_form (v : Nat) :
    ∃ h r, v/2+1=(2*h+1)*2^r ∧
      FullHeight.height v = if v%2=0 then evenValue h r else oddValue h r :=
  FullHeight.height_closed_form v

theorem zero_start : FullHeight.height 0 = 1 :=
  FullHeight.height_zero

theorem digit_recurrence :
    coordinates FullHeight.height 0 = initial ∧
    ∀ n, coordinates FullHeight.height (2*n) = evenStep (coordinates FullHeight.height n) ∧
      coordinates FullHeight.height (2*n+1) = oddStep (coordinates FullHeight.height n) :=
  DigitRecurrence.actual_digit_recurrence

theorem digit_maximum (n : Nat) :
    FiniteEditStability.IsMaximumPrefix ThueMorseBits.t n (DigitRecurrence.evaluate n).L.toNat :=
  DigitRecurrence.evaluate_isMaximum n

theorem phase_maximum (a v : Nat) :
    IsMaximumPrefix (shift ThueMorseBits.t a) v (PhaseHeight.height a v) :=
  PhaseHeight.height_isMaximum a v

theorem phase_extremal_classification (a v len : Nat) (hv : 1 ≤ v) :
    (FiniteEditStability.IsMaximumPrefix (PhaseShift.shift t a) v len ∧
      3*len = 8*v+5*a-1) ↔
      ∃ n, a ≤ 2^n ∧ v = 3*2^n-a-1 ∧ len = 8*2^n-a-3 :=
  PhaseExtremal.shifted_extremal_iff a v len hv

theorem base_linear_bound (v : Nat) (hv : 1 ≤ v) :
    3 * FullHeight.height v ≤ 8 * v - 1 := by
  obtain ⟨path, hz, hm⟩ := (FullHeight.height_isMaximum v).1
  have h := SharpThueMorse.binary_path_prefix_bound path (FullHeight.height v) (by omega) hm
  simpa only [hz] using h

theorem phase_linear_bound (a v : Nat) (hv : 1 ≤ v) :
    3 * PhaseHeight.height a v ≤ 8 * v + 5 * a - 1 := by
  obtain ⟨path, hz, hm⟩ := (PhaseHeight.height_isMaximum a v).1
  have h := PhaseShift.thueMorse_shift_prefix_bound a path (PhaseHeight.height a v) (by omega) hm
  simpa only [hz] using h

theorem base_extremal_classification (v : Nat) (hv : 1 ≤ v) :
    3 * FullHeight.height v = 8 * v - 1 ↔
      ∃ n, v = 3 * 2^n - 1 ∧ FullHeight.height v = 8 * 2^n - 3 := by
  have hm : IsMaximumPrefix (PhaseShift.shift t 0) v (FullHeight.height v) := by
    change IsMaximumPrefix t v (FullHeight.height v)
    exact FullHeight.height_isMaximum v
  simpa only [hm, true_and, Nat.mul_zero, Nat.add_zero, Nat.zero_le, Nat.sub_zero] using
    PhaseExtremal.shifted_extremal_iff 0 v (FullHeight.height v) hv

end ResearchCommons.Claims.MatchingHeights
