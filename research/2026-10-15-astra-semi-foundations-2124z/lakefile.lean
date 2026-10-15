import Lake
open Lake DSL

package semiFoundations

/-!
UNEXECUTED narrow serial build configuration. No dependency acquisition.
External objects and the explicit compiler path must be authenticated by a
separate desktop admission. This script is not a resource/identity supervisor.
-/

@[test_driver]
script verify (args) do
  unless args.isEmpty do throw <| IO.userError "no extra targets are admitted by this source profile"
  let workspace ← getWorkspace
  let root := workspace.dir
  let some lean ← IO.getEnv "SEMI_LEAN_BIN"
    | throw <| IO.userError "SEMI_LEAN_BIN must bind the explicitly admitted compiler"
  if ← (root / "build").pathExists then
    throw <| IO.userError "build must be absent in the fresh admitted leaf"
  let modules := #[
    "SamuelAlexanderResearch/ObservationPrediction",
    "Semi/Core/Observation",
    "Semi/Core/FiniteOrbit",
    "Semi/Diffraction/CyclicGrid",
    "Semi/Diffraction/FourierIntensity",
    "Semi/Diffraction/OrbitHamming",
    "Semi/Statistics/FiniteDecision",
    "Semi/Statistics/CyclicRecovery",
    "Semi/Certificates/FoundationAudit"]
  for name in modules do
    let object := root / "build" / (name ++ ".olean")
    let info := root / "build" / (name ++ ".ilean")
    let some parent := object.parent
      | throw <| IO.userError "selected output has no parent"
    IO.FS.createDirAll parent
    let child ← IO.Process.spawn {
      cmd := lean
      args := #["-R", (root / "source").toString, "-o", object.toString, "-i", info.toString,
        (root / "source" / (name ++ ".lean")).toString]
      cwd := some root
      stdout := .inherit
      stderr := .inherit }
    let code ← child.wait
    unless code == 0 do return code
  return 0
