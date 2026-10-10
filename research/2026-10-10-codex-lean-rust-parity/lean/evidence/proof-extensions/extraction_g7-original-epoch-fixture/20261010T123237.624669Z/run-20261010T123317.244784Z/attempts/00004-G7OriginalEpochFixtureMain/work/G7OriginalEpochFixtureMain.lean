import G7OriginalEpochFixture

/-! Separate test entrypoint: the modular scientific fixture keeps its run
function in its own namespace and introduces no global main. -/
def main (args : List String) : IO UInt32 :=
  UnifiedLean.G7.OriginalEpochFixture.run args
