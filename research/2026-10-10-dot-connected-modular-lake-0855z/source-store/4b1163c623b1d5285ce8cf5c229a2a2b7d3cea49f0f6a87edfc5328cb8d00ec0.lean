import OriginalBigonProgramDiagonal
import G1ExtractedComponentProgram
import G7SinglePopulationPolynomialKernel

/-! Actual original ordinary connector, including entry and exit. The rate
identity reuses the reviewed G7 single-population provider. dot, 9 October 2026. -/
namespace DotG34.OriginalOrdinaryConnector
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G5.ActualNoMergerReadout GProgram.G7.SinglePopulationPolynomialKernel
open G1NonrootBigonKernel G1ExtractedComponentProgram DotG34.ActualSerialSurvival
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_connector_entry_population (N : RootedBinary V E X) {sample : Copy → X}
    (e : E) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node (N.graph.target e)) :
    CoLocated N (ordinaryCode N s e) (some e) := by
  intro x
  rw [ordinaryCode_copyLocation]
  have hx : copyLocation (state s) x = .node (N.graph.target e) :=
    hall _ (s.property.forest.ancestor_live x)
  simp [hx, ordinaryLocation, originalPlace]

theorem actual_connector_count_law (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (e : E)
    (degree : N.graph.inDegree (N.graph.target e) = 1) (s : Code N sample) :
    (sourceProgram N r (edgeProgram N C e degree) s).map liveCard =
      (sourceTimeKernel N r (edgeDuration N C e) (ordinaryCode N s e)).map liveCard := by
  rw [actual_original_edge_program, PMF.map_comp]
  rfl

theorem actual_connector_no_loss (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (e : E)
    (degree : N.graph.inDegree (N.graph.target e) = 1) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node (N.graph.target e)) :
    (((sourceProgram N r (edgeProgram N C e degree) s).map liveCard)
      (liveCard s)).toReal =
    Real.exp (-(pairRate r (some e) * ((liveCard s).choose 2 : ℝ) *
      (edgeDuration N C e : ℝ))) := by
  rw [actual_connector_count_law]
  change (((sourceTimeKernel N r (edgeDuration N C e) (ordinaryCode N s e)).map
    liveCard) (liveCard (ordinaryCode N s e))).toReal = _
  rw [actual_kernel_live_card_mass, actual_holding_weight,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    actual_population_holding_rate N r (ordinaryCode N s e) (some e)
      (actual_connector_entry_population N e s hall)]
  rfl

#print axioms actual_connector_entry_population
#print axioms actual_connector_count_law
#print axioms actual_connector_no_loss
end DotG34.OriginalOrdinaryConnector
