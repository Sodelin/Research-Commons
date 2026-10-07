import UnifiedLean.G6.BinFold
import G2MarkedTraceCuts
import G2WholeMatrixAges

/-!
UNCHECKED root derivative, 7 October 2026. Uses unchanged original clock
coordinates, literal active records, horizon bounds and fixed-cut nullity.
It does not supply refined-calendar composition or the whole observation law.
-/
namespace UnifiedLean.G6.BinClock
open MeasureTheory ProbabilityTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceMergerClockCatalogue
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceCuts
open GProgram.G2.ClockBoundaryNull UnifiedLean.G6.BinFold
open scoped Classical

variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- An active coordinate belongs to the SAME original active record list. -/
theorem active_coordinate_mem (N : RootedBinary V E X) {sample : Copy → X}
    (n : ℕ) (H : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (i : Fin n) (hi : ((literalMarkedTrace N n H s c).2 i).1 = true) :
    (literalMarkedTrace N n H s c).2 i ∈ activeTrace N n H s c := by
  change (literalMarkedTrace N n H s c).2 i ∈
    (List.ofFn (literalMarkedTrace N n H s c).2).filter (fun z => z.1)
  exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩

/-- Fixed interval boundaries are avoided on one full-measure event for all
budgets. No successful completion flag or independently sampled age is used. -/
theorem actual_active_coordinate_bounds (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (offset H : ℝ) :
    ∀ᵐ c ∂currentPairClockMeasure N r s, ∀ (n : ℕ) (i : Fin n),
      ((literalMarkedTrace N n H s c).2 i).1 = true →
      offset < offset + ((literalMarkedTrace N n H s c).2 i).2.1 ∧
      offset + ((literalMarkedTrace N n H s c).2 i).2.1 < offset + H := by
  filter_upwards [actual_clock_strictly_positive N r s,
    actual_active_times_avoid_fixed N r s H] with c hc hn
  intro n i hi
  obtain ⟨p, hp⟩ := literal_active_time_is_coordinate N n H s c i hi
  have hpos : 0 < ((literalMarkedTrace N n H s c).2 i).2.1 := by
    rw [hp]
    exact hc p
  have hle := (activeTrace_mem_bounds N n H s c
    ((literalMarkedTrace N n H s c).2 i)
    (active_coordinate_mem N n H s c i hi)).2
  have hlt : ((literalMarkedTrace N n H s c).2 i).2.1 < H :=
    lt_of_le_of_ne hle (hn n H i hi)
  constructor <;> linarith

/-- Actual clock support discharges the active-tag premise of the SAME fold.
The carried old matrix is arbitrary here; the source decoration law is a
separate attachment, and no absence sentinel is discarded. -/
theorem actual_bin_constant_fold (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (offset H : ℝ)
    (bin : ℝ → Tag) (tag : Tag)
    (hbin : ∀ a : ℝ, offset < a → a < offset + H → bin a = tag) :
    ∀ᵐ c ∂currentPairClockMeasure N r s, ∀ (n : ℕ) (M : Copy → Copy → Tag),
      foldTags N bin n s offset M (literalMarkedTrace N n H s c).2 =
      foldTags N (fun _ => tag) n s offset M (literalMarkedTrace N n H s c).2 := by
  filter_upwards [actual_active_coordinate_bounds N r s offset H] with c hc
  intro n M
  apply bin_constant_active_fold
  intro i hi
  exact hbin _ (hc n i hi).1 (hc n i hi).2

#print axioms active_coordinate_mem
#print axioms actual_active_coordinate_bounds
#print axioms actual_bin_constant_fold
end UnifiedLean.G6.BinClock
