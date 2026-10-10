import G6RationalCompressionCertificateFixture

open GProgram.G6.RationalCompressionCertificateFixture

def main : IO Unit := do
  for (name, actual, expected) in checks do
    IO.println s!"{name}: {actual} (expected {expected})"
  if !allChecksPass then
    throw (IO.userError "typed rational certificate example failed")
