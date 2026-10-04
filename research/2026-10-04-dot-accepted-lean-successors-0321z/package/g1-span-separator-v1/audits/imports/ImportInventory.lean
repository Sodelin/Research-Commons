import G1CanonicalOriginatedCompletedHistory
import G1CanonicalOriginatedHistoryPlanner
import G1CanonicalOriginatedMacroPlans
import G1ClosingSpanSafeSyntax
import G1DerivedSpanSeparatedAgenda
import G1InitializedOriginatedSpanSeparator
import G1OriginalSpanRegion
import G1OriginatedNeutralSpanRegion
import G1OriginatedTaxonReachTransport
import G1SpanRegionExitClosure
import G1SpanRegionOriginalOperations
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
