import Lake
open Lake DSL
package originalG2Criterion where
  moreLeanArgs := #["-j1", "-M4096"]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
@[default_target] lean_lib G2Criterion where
  srcDir := "src"
  roots := #[`G2UniversalTransitionCriterion, `G2ActualSourceTransitionCriterion]
