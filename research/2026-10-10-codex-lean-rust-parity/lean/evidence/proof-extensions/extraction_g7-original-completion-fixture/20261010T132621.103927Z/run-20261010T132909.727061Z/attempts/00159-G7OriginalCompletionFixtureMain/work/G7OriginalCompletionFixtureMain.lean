import G7OriginalCompletionFixture

/-! Separate evaluator entrypoint; the scientific data module has no global main. -/
def main (args : List String) : IO UInt32 :=
  UnifiedLean.G7.OriginalCompletionFixture.run args
