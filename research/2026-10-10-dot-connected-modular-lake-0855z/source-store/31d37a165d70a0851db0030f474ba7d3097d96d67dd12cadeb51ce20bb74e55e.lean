import UnifiedLean.Source.NativePairClockLaw
import Mathlib.Algebra.Order.Field.Basic

/-!
Codex integration G6, 2026-10-08. SOURCE draft, compiler UNCHECKED.
Original PositivePairRates carrier is unchanged. Exact fixed-rational chart
algorithm is separate Python evidence. No graph admission, original-real
rationality restriction, provider law/table equality or all-source net follows.
-/
namespace CodexIntegration.G6.FixedCalendarSharedBank

open UnifiedLean.Source.NativePairClockLaw

variable {E I : Type*}

/-- One actual original edge bank plus the separate ancestral population.
The same Option E coordinates are used in every finite profile. -/
noncomputable def sourceBank (rho : Option E → ℝ) (hp : ∀ e, 0 < rho e) :
    PositivePairRates E where
  edge e := rho (some e)
  edge_pos e := hp (some e)
  ancestral := rho none
  ancestral_pos := hp none

theorem pairRate_sourceBank (rho : Option E → ℝ) (hp : ∀ e, 0 < rho e)
    (e : Option E) : pairRate (sourceBank rho hp) e = rho e := by
  cases e <;> rfl

/-- A fixed calendar row supplies its actual positive exposure duration and
literal original population occurrence. Cell is a property, never a desired law. -/
structure ExposureCell (E : Type*) where
  population : Option E
  duration : ℝ
  duration_pos : 0 < duration
  accepts : ℝ → Prop

def Fits (r : PositivePairRates E) (cells : I → ExposureCell E) : Prop :=
  ∀ i, (cells i).accepts (pairRate r (cells i).population * (cells i).duration)

/-- Shared feasibility is exactly one original bank meeting ALL rows.
Independent row/epoch existential witnesses cannot discharge this statement. -/
theorem fits_iff_one_original_bank (cells : I → ExposureCell E) :
    (∃ r : PositivePairRates E, Fits r cells) ↔
      ∃ rho : Option E → ℝ, (∀ e, 0 < rho e) ∧
        ∀ i, (cells i).accepts (rho (cells i).population * (cells i).duration) := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨pairRate r, pairRate_pos r, hr⟩
  · rintro ⟨rho, hp, hc⟩
    refine ⟨sourceBank rho hp, ?_⟩
    intro i
    simpa only [pairRate_sourceBank] using hc i

/-- Exact cell normalization used by the rational gate, including closed
point cells. Open bounds use the corresponding strict division identities. -/
theorem closed_hazard_cell_iff (rho d lo hi : ℝ) (hd : 0 < d) :
    (lo ≤ rho * d ∧ rho * d ≤ hi) ↔ (lo / d ≤ rho ∧ rho ≤ hi / d) := by
  rw [div_le_iff₀ hd, le_div_iff₀ hd]

theorem strict_hazard_cell_iff (rho d lo hi : ℝ) (hd : 0 < d) :
    (lo < rho * d ∧ rho * d < hi) ↔ (lo / d < rho ∧ rho < hi / d) := by
  rw [div_lt_iff₀ hd, lt_div_iff₀ hd]

/-- A saturated upper-unbounded cell still constrains the SAME original rate. -/
theorem saturated_hazard_cell_iff (rho d lo : ℝ) (hd : 0 < d) :
    lo ≤ rho * d ↔ lo / d ≤ rho := by
  exact (div_le_iff₀ hd).symm

/-- Protected/cut-crossing occurrences are never rate-reset at a cut. -/
theorem equal_original_exposures_equal_hazards (r : PositivePairRates E)
    (a b : ExposureCell E) (he : a.population = b.population)
    (ht : a.duration = b.duration) :
    pairRate r a.population * a.duration = pairRate r b.population * b.duration := by
  rw [he, ht]

#print axioms pairRate_sourceBank
#print axioms fits_iff_one_original_bank
#print axioms closed_hazard_cell_iff
#print axioms strict_hazard_cell_iff
#print axioms saturated_hazard_cell_iff
#print axioms equal_original_exposures_equal_hazards

end CodexIntegration.G6.FixedCalendarSharedBank
