import GeneratedNaturalChronology
import Mathlib.Algebra.Order.Floor.Semiring

namespace UnifiedLean.G6.GeneratedNaturalChronology
open NaturalCellInverseRates NaturalCellAffineCompiler
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture

/-- K finite weak cells of width d followed by the saturated ray [Kd,infinity).
Overlapping endpoints preserve coverage and require no equality oracle. -/
def meshCell (d : ℚ) (K : ℕ) (i : Fin (K+1)) : RationalInterval :=
  ⟨some ⟨(i.val : ℚ)*d,false⟩,
    if i.val < K then some ⟨((i.val : ℚ)+1)*d,false⟩ else none⟩

theorem meshCell_contains (d : ℚ) (K : ℕ) (i : Fin (K+1)) (z : ℝ) :
    (meshCell d K i).contains z ↔
    (i.val : ℝ)*(d : ℝ) ≤ z ∧
      (i.val < K → z ≤ ((i.val : ℝ)+1)*(d : ℝ)) := by
  unfold meshCell RationalInterval.contains
  split_ifs <;> simp_all

theorem mesh_covers (d : ℚ) (hd : 0 < d) (K : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    ∃ i : Fin (K+1), (meshCell d K i).contains z := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hlast : (K : ℝ)*(d : ℝ) ≤ z
  · refine ⟨Fin.last K, (meshCell_contains d K _ z).mpr ?_⟩
    constructor
    · exact hlast
    · intro hi
      exact False.elim (Nat.lt_irrefl K hi)
  · have hlt : z < (K : ℝ)*(d : ℝ) := lt_of_not_ge hlast
    have hdiv : 0 ≤ z/(d : ℝ) := div_nonneg hz hdR.le
    have hfloor : ⌊z/(d : ℝ)⌋₊ < K :=
      (Nat.floor_lt hdiv).mpr ((div_lt_iff₀ hdR).mpr hlt)
    let i : Fin (K+1) := ⟨⌊z/(d : ℝ)⌋₊, Nat.lt_trans hfloor (Nat.lt_succ_self K)⟩
    refine ⟨i, (meshCell_contains d K i z).mpr ⟨?_,?_⟩⟩
    · exact (le_div_iff₀ hdR).mp (Nat.floor_le hdiv)
    · intro _
      exact le_of_lt ((div_lt_iff₀ hdR).mp (Nat.lt_floor_add_one (z/(d : ℝ))))

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]
variable (N : RootedBinary V E X)

/-- Fully supplied rational grids remove the abstract one-dimensional coverage
premises from the finite original-source chronology/exposure producer. -/
theorem rational_grid_source_coverage {n j : ℕ} (layout : BankVar N ≃ Fin n)
    (cuts : Fin j → ℚ) (d e : ℚ) (hd : 0 < d) (he : 0 < e) (K L : ℕ)
    (c : Calendar N.graph) (r : PositivePairRates E) (g : HybridProbabilities N)
    (ht : ∀ x, c.age (N.leaf x) = 0) :
    ∃ ch ∈ viableCharts N layout cuts (meshCell d K) (meshCell e L),
      Realizes cuts ch.1 c.age ∧
      (∀ h, (meshCell e L (ch.2.2 h)).contains (g.gamma h)) ∧
      (∀ p, PhysicalActive N cuts c.age p → (meshCell d K (ch.2.1 p)).contains
        (pairRate r p.1 * (value cuts c.age p.2.2 - value cuts c.age p.2.1))) := by
  apply viableCharts_cover_source N layout (0 : Fin (K+1)) cuts
    (meshCell d K) (meshCell e L) (mesh_covers d hd K)
    (fun z hz _ => mesh_covers e he L z hz.le) c r g ht

end UnifiedLean.G6.GeneratedNaturalChronology
