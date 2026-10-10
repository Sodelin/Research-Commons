import GParity.Protocol

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let raw ← try stdin.readToEnd catch _ => pure ""
  let (response, status) := GParity.Protocol.execute raw
  stdout.putStr response
  return status
