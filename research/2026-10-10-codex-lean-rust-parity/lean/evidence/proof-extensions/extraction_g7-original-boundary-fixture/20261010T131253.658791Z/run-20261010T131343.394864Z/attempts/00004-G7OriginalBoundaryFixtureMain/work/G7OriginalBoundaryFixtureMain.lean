import G7OriginalBoundaryFixture

/-! Isolated entrypoint for the twelve original conditional boundary controls. -/
def main (args : List String) : IO UInt32 :=
  UnifiedLean.G7.OriginalBoundaryFixture.run args
