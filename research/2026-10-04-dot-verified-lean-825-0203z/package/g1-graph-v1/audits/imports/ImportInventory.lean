import G1ActualTwoPortBlob
import G1BigonFootprint
import G1BigonSpliceGraph
import G1BlobDegreeBalance
import G1CutChildPorts
import G1ExtractedComponentProgram
import G1SpliceCutTransport
import G1SpliceDegrees
import G1SpliceLSA
import G1SpliceRootBlob
import G1SplicedSourceAdmission
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
