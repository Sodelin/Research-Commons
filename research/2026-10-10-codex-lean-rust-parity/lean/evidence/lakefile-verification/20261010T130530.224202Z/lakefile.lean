import Lake
open Lake DSL

package gParity where
  moreLeanArgs := #["-t0", "-Ddebug.skipKernelTC=false"]

lean_lib GParity

@[default_target]
lean_exe gparity where
  root := `GParity.Main

/-- Exact public G1-G7 source union; historical versions remain separate. -/
target formal pkg : Unit := do
  Job.async do
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := #["scripts/build_connected.py", "current/connected"]
      cwd := some pkg.dir
      stdout := .inherit
      stderr := .inherit }
    let code ← child.wait
    unless code == 0 do
      error s!"The formal target preserved a failed or blocked attempt (exit {code})."

/-- Latest compatible1433 public union, replayed from its frozen exact sources. -/
target latestFormal pkg : Unit := do
  Job.async do
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := #["scripts/replay_latest_union.py"]
      cwd := some pkg.dir
      stdout := .inherit
      stderr := .inherit }
    let code ← child.wait
    unless code == 0 do
      error s!"The latest public replay preserved a failed or blocked attempt (exit {code})."

@[test_driver]
script verify (args) do
  let result ← IO.Process.output {
    cmd := "python3"
    args := #["scripts/build_connected.py"] ++ args.toArray }
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode
