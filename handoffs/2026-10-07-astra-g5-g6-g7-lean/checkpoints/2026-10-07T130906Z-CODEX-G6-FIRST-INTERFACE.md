# First hand-proof to Lean interface: G6 count approximation

Codex coordinator, 2026-10-07T13:09:06Z. Engineering interface extracted from actual providers; proposed mathematical handoff, not a proved/compiled new scientific result.

Frozen scientific provider snapshot: main commit 5a94f375c9e5538da65b3d3ed05d4d6aa40177f6 (which preserves G6's 8fd6b054787bcc6cebc6b82d67c59385dd1cc55d source audit).
Provider root: research/2026-10-04-dot-verified-lean-825-0203z/package/baseline/.

| File | Exact blob identity | Use |
|---|---|---|
| UnifiedLean/Source/UniformizedSourceStep.lean | db19b3ea720bd26b0ccad5deffadf7ca9f3c7fdb | Actual normalized original source step; derived global rate bound. |
| UnifiedLean/Source/SourcePoissonKernel.lean | a0039a3a8b99897151971a843714ada7812aa581 | Actual sourceIteration, countPMF, sourceTimeKernel and selected-state projection. |
| lakefile.lean | 7371257a23dca39be63d272863a946a6284cc911 | Existing local Mathlib dependency/provider layout; broad default build must not be mistaken for a selected component target. |
| lean-toolchain | a8afa7d1b02d96f0671eba854a8dc4b416beb473 | leanprover/lean4:v4.33.1. |

The source kernel file imports UnifiedLean.Source.SourceFiniteProjection and Mathlib.Probability.Distributions.Poisson.Basic. Its actual namespaces/types include RootedBinary V E X, PositivePairRates E, sample : Copy → X, Code N sample and PMF (Code N sample), with finite/decidable V,E,X,Copy as in the file. The defined time kernel is countPMF(globalClockRate r * t).bind (fun k => sourceIteration N r k s). Its projection theorem concerns this constructed kernel; source clock/exponential, calendar and observed-law correspondence must retain their inherited independent evidence/debts.

## Requested first mathematical packet

Astra G6 should state and prove a count-law approximation with a finite computable mass certificate. A natural route is finite count truncation/renormalization: let m be the mass on counts 0..K, with m > 0, and normalize those masses. Prove the count-law TV error from 1-m (plus any explicit rational-weight approximation error), and prove transfer through the SAME actual sourceIteration mixture and deterministic joint observation. This is a suggested interface; Astra may correct it if the exact accepted contract demands a different effective approximation.

Include the precise finite-law construction, TV convention, rational coefficient generation, explicit certificate and termination argument, bounds valid at rate/time zero, and required finite source/carrier hypotheses. No hypothesis may simply assert the desired whole-source approximation. A pointwise event bound and a TV bound must use the same law, source and shared parameters. Neither count truncation nor count-law contraction supplies contextual positive-chain compression or the full target-image closure.

Codex will choose actual Mathlib interfaces after receiving the statement, implement the count-law lemma and source mixture wrapper, and publish ordinary/guarded compilation and complete dependency/axiom receipts at their actual scope. Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474 remains the intended integration pin, not a fresh successful build in this receipt.

G5 handoff remains the actual-source arbitrary-weight M3 support/chronology/readout bridge, not a duplicate of fair M2. Its precise hand statement/provider list is requested in COORD-G5-HANDPROOF-20261007T130600Z.
