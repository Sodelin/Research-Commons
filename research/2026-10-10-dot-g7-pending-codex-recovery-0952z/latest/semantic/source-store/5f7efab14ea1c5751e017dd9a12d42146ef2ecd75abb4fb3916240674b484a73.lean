import G1ActualJointProgram

/-! Source-derived population panels for one actual boundary-free epoch.
Reuses the accepted G1 conditional joint law. One entering Code, including its
original register, is fixed in each factorization; natural mixing stays outside
the product. No source rate independence or saturated-cell TV is asserted here.
Contributor: dot, 2026-10-09. -/
namespace DotG6.ActualPopulationPanelSplit
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open G1JointSeparatedSourceGeometry G1ActualJointGenerator G1ActualJointEpoch G1ActualJointProgram
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Every original label is grouped by its CURRENT actual owner's population;
not by its tip species or an independently invented lineage label. -/
noncomputable def populationPanel (s : State V E Copy) (place : Location V E) : Finset Copy :=
  Finset.univ.filter (fun x => copyLocation s x = place)

noncomputable def exteriorPanel (s : State V E Copy) (place : Location V E) : Finset Copy :=
  Finset.univ \ populationPanel s place

@[simp] theorem mem_populationPanel (s : State V E Copy) (place : Location V E) (x : Copy) :
    x ∈ populationPanel s place ↔ copyLocation s x = place := by
  simp [populationPanel]

@[simp] theorem mem_exteriorPanel (s : State V E Copy) (place : Location V E) (x : Copy) :
    x ∈ exteriorPanel s place ↔ copyLocation s x ≠ place := by
  simp [exteriorPanel]

/-- Physical source separation is derived from literal copyLocation, not
provided as an independence or desired-kernel premise. -/
theorem actual_population_separated (s : State V E Copy) (place : Location V E) :
    PopulationSeparated s (populationPanel s place) (exteriorPanel s place) := by
  intro x hx y hy he
  have hx' := (mem_populationPanel s place x).mp hx
  have hy' := (mem_exteriorPanel s place y).mp hy
  exact hy' (he.symm.trans hx')

/-- The existing source agenda condition for an actual single interval follows
from the constructed physical population panels, including zero duration. -/
theorem actual_population_epoch_agenda (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) (place : Location V E) :
    SeparatedAgenda N r (populationPanel (state s) place) (exteriorPanel (state s) place)
      [.interval t] s := by
  refine ⟨actual_population_separated (state s) place, ?_⟩
  intro d hd
  trivial

/-- Both entire selected genealogy/population/register states factor only
CONDITIONALLY on the same actual entering Code. -/
theorem actual_population_epoch_product (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) (place : Location V E) :
    (sourceTimeKernel N r t s).map
      (jointProjection N (populationPanel (state s) place) (exteriorPanel (state s) place)) =
      independentProduct
        ((sourceTimeKernel N r t s).map (projection N (populationPanel (state s) place)))
        ((sourceTimeKernel N r t s).map (projection N (exteriorPanel (state s) place))) :=
  actual_separated_joint_epoch_law N r _ _ t s (actual_population_separated (state s) place)

/-- A naturally correlated entering law is mixed ONCE outside the conditional
products. This explicitly preserves shared-register dependence. -/
theorem actual_population_mixture {O : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0)
    (initial : PMF (Code N sample)) (place : Location V E)
    (readout : ∀ s : Code N sample,
      SelectedIndex N sample (populationPanel (state s) place) ×
        SelectedIndex N sample (exteriorPanel (state s) place) → O) :
    initial.bind (fun s => ((sourceTimeKernel N r t s).map
      (jointProjection N (populationPanel (state s) place) (exteriorPanel (state s) place))).map
        (readout s)) =
    initial.bind (fun s => (independentProduct
      ((sourceTimeKernel N r t s).map (projection N (populationPanel (state s) place)))
      ((sourceTimeKernel N r t s).map (projection N (exteriorPanel (state s) place)))).map
        (readout s)) := by
  apply congrArg (PMF.bind initial)
  funext s
  rw [actual_population_epoch_product N r t s place]

#print axioms actual_population_separated
#print axioms actual_population_epoch_agenda
#print axioms actual_population_epoch_product
#print axioms actual_population_mixture
end DotG6.ActualPopulationPanelSplit
