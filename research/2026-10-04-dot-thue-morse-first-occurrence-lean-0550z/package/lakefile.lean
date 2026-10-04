import Lake
open Lake DSL
package thueMorseFirstOccurrence
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib SamuelAlexanderResearch where
  roots := #[`SamuelAlexanderResearch.ThueMorseBits]
@[default_target] lean_lib ThueMorseMAP where
  roots := #[`ThueMorseMAP.Headline]
