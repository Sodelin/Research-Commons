import G1CanonicalCompactCompletedReplacement
import G1CanonicalCompactComponentRow
import G1CanonicalCompactExteriorHistory
import G1CanonicalEpochBlockBinding
import G1CanonicalEpochSpecialization
import G1CanonicalSingleExitSupport
import G1CanonicalThreeEpochList
import G1CompactComponentBlockRows
import G1CompactSourceComposition
import G1OriginalComponentNodeIdentity
import G1OriginalEpochPanelCompression
import G1OriginalEpochPanelSilence
import G1OriginalExitBatchBinding
import G1OriginalNodeBatchBinding
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
