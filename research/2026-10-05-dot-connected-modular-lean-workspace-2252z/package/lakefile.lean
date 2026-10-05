import Lake
open Lake DSL
package connectedResearch

/-- Modular named groups first, then a separately bounded compatible check. -/
@[default_target]
target connected pkg : Unit := do
  Job.async do
    let child ← IO.Process.spawn { cmd := "python3", args := #["scripts/build_connected.py", "all"], cwd := some pkg.dir, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    unless code == 0 do error s!"Connected build has preserved failed/blocked targets (exit {code})."

@[test_driver]
script verify (args) do
  let result ← IO.Process.output { cmd := "python3", args := #["scripts/build_connected.py"] ++ args.toArray }
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode
