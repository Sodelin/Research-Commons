import RationalNaturalGrid
import RationalNaturalCellWitness

namespace UnifiedLean.G6.GeneratedNaturalChronology
open NaturalCellInverseRates NaturalCellAffineCompiler RationalNaturalCellWitness
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]
variable (N : RootedBinary V E X)

/-- Every accepted GENERATED chart admits one genuine rational source in that
same chart. This composes the prior rational-witness theorem; it is existential,
not a witness-returning implementation, and asserts no observation-TV bound. -/
theorem generated_chart_rational_source {n j K L : ℕ} (layout : BankVar N ≃ Fin n)
    (cuts : Fin j → ℚ) (hazardGrid : Fin K → RationalInterval)
    (coinGrid : Fin L → RationalInterval) (ch : Chart N j K L)
    (hc : ch ∈ viableCharts N layout cuts hazardGrid coinGrid) :
    ∃ (c : Calendar N.graph) (r : PositivePairRates E) (g : HybridProbabilities N),
      (∀ x, c.age (N.leaf x) = 0) ∧ Realizes cuts ch.1 c.age ∧
      (∀ h, (coinGrid (ch.2.2 h)).contains (g.gamma h)) ∧
      (∀ p, PhysicalActive N cuts c.age p → (hazardGrid (ch.2.1 p)).contains
        (pairRate r p.1 * (value cuts c.age p.2.2 - value cuts c.age p.2.1))) ∧
      (∀ v, ∃ a : ℚ, c.age v = a) ∧
      (∀ e, ∃ a : ℚ, pairRate r e = a) ∧
      (∀ h, ∃ a : ℚ, g.gamma h = a) := by
  have hf := (decideOriginalCell_correct N layout _ _ _).mp
    (Finset.mem_filter.mp hc).2
  obtain ⟨c,r,g,ht,hs,hg,hp,ha,hr,hgamma⟩ :=
    rational_original_source N layout (constraint cuts ch.1)
      (exposure N cuts ch.1 (fun p => hazardGrid (ch.2.1 p)))
      (fun h => coinGrid (ch.2.2 h)) hf
  have hs' := (constraint_iff cuts ch.1 c.age).mp hs
  exact ⟨c,r,g,ht,hs',hg,(exposure_rows_iff N hs' r _).mp hp,ha,hr,hgamma⟩

end UnifiedLean.G6.GeneratedNaturalChronology
