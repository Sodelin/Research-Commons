import Lake
open Lake DSL

package recoveredUnifiedLean

@[test_driver]
script verify (args) do
  let result ← IO.Process.output {
    cmd := "python3"
    args := #["scripts/build_profiles.py", "all"] ++ args.toArray
  }
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode
