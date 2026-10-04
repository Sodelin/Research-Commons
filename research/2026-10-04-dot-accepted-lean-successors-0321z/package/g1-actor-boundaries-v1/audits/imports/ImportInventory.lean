import G1ActualOriginalBaseAsyncStep
import G1ActualOriginalPrivateAsyncStep
import G1ActualOriginalUnrankedLocalKernel
import G1ActualPrivateOriginalWordExtraction
import G1CanonicalExtractedPrivateKWord
import G1OriginalActorPrivateWordKernel
import G1OriginalActorUnrankedBoundaryFrames
import G1OriginalUnrankedActorOpenClose
import G1WholeOriginalActorBoundaryTensor
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
