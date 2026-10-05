import Lake
open Lake DSL
package actualNanuqSource where
  moreLeanArgs := #["-j1", "-M4096"]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib OriginalSourceProviders where
  srcDir := "providers"
  roots := #[`AnchorComposition, `AnchorPortCounts, `AnchorPortFibers, `AnchorPortPatterns, `G2LiveLineageRouting, `G5MinimalGraphInterface, `G6BridgeCannotEnterHybrid, `GraphBlobLeaves, `GraphBlobMedian, `GraphBlobOrientation, `GraphBlobPorts, `GraphBlobs, `GraphBridgeSplits, `GraphCuts, `GraphGalls, `GraphLeaves, `GraphMedianUnique, `GraphPortConsequences, `GraphPortFibers, `GraphPortTransport, `GraphPorts, `GraphQuartetBridge, `GraphQuartetExistence, `GraphSwitching, `GraphSwitchingCuts, `GraphSwitchingDegree, `GraphSwitchingExistence, `GraphSwitchingFinite, `GraphTreePorts, `QuartetComposition, `QuartetCompositionDependent, `QuartetSemantics, `RawSourceAnchorLocalization, `SourceCompositionBridge, `SourceNetwork, `SourceQuartetRelation, `SourceResolve, `WeightedAnchor, `WeightedCoefficients, `WeightedOrderedPairs, `WeightedSource]
@[default_target] lean_lib ActualNanuqSource where
  srcDir := "src"
  roots := #[`NanuqActualBridgeQuartetResolution, `NanuqActualQuartetPortBranching, `NanuqCutWalkLocality, `NanuqActualPortCutFibre, `NanuqActualQuartetCutLocality, `NanuqActualQuartetCutLocalization, `NanuqActualFourPortInvariance]
