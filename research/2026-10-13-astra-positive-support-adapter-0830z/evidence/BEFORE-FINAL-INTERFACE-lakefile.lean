import Lake
open Lake DSL

package astraPositiveSupportIntegration

def runSupportPython (pkg : Package) (args : Array String) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := "python3", args := #["-B"] ++ args, cwd := some pkg.dir,
    stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  unless code == 0 do throw <| IO.userError s!"support integration failed (exit {code})"

def supportBuildArgs : IO (Array String) := do
  let mut args := #["build_support.py"]
  for (option, envName) in #[("--source-root", "ASTRA_SUPPORT_SOURCES"),
      ("--external-state", "ASTRA_SUPPORT_EXTERNAL_STATE"),
      ("--state", "ASTRA_SUPPORT_STATE"), ("--mathlib-root", "ASTRA_MATHLIB_ROOT"),
      ("--lean-bin", "ASTRA_LEAN_BIN")] do
    let some value ← IO.getEnv envName
      | throw <| IO.userError s!"missing required environment variable {envName}"
    args := args ++ #[option, value]
  return args

/-- Fresh adapter compilation after exact provider preparation. Completion
requires all selected module receipts and every required theorem axiom audit. -/
@[default_target]
target adapter pkg : Unit := do
  Job.async do
    let args ← supportBuildArgs
    runSupportPython pkg (args ++ #["--require-complete"])

/-- A bounded preparation batch. Success does not mean the provider is complete. -/
target provider_batch pkg : Unit := do
  Job.async do
    let args ← supportBuildArgs
    runSupportPython pkg (args ++ #["--prepare-provider", "--batch", "16"])

/-- Full source integration, with no assertion of a fresh combined build. -/
target materialize pkg : Unit := do
  Job.async do
    let some out ← IO.getEnv "ASTRA_SUPPORT_SOURCES"
      | error "ASTRA_SUPPORT_SOURCES must name a fresh directory"
    runSupportPython pkg #["materialize_support.py", "--out", out]
