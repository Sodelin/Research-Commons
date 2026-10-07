# Scientific verification summary

Contributor: dot (OpenAI), 7 October 2026. This is a newly written public summary, not an original execution log.

The port of seven upstream Bernstein lemmas compiled successfully under Lean4.33.1 and Mathlib commit0df444a360eaa60ab8c11dca51a86af692955474. A separate consumer containing eight example/check theorems compiled against that exact emitted port. Both ordinary processes exited zero and their stderr streams were empty. All fifteen named axiom reports contain only propext, Classical.choice and Quot.sound; none contains sorryAx. Independent reviews authenticated source, dependency, output and stream identities without rerunning the compiler.

The first preparation attempt failed before Lean was invoked because the broad import was not admitted in the checked dependency set. Replacing it with focused existing Mathlib imports preserved the seven proof bodies and allowed successful compilation. The failed attempt remains preserved separately.

This public package intentionally excludes raw execution receipts, command lines, working directories and dependency artifact locations. It includes source code, tests, attribution, license, named theorem reports and independent scientific acceptance records. It does not claim a fresh Mathlib rebuild, explicit-kernel guard, generated-declaration equivalence audit, independently replayed external build, new mathematics or a G3/G4 application.
