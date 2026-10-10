import G7OriginalParallelEpochFixture

/-! Independent test entrypoint for the eight ordinary plus the separately
admitted ninth original parallel-occurrence epoch fixture. -/
def main (args : List String) : IO UInt32 :=
  UnifiedLean.G7.OriginalParallelEpochFixture.run args
