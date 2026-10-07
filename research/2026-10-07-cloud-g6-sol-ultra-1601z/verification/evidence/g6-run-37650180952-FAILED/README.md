# G6 second-run failure and finite component PASS

Actual observed run [37650180952](https://github.com/Sodelin/Research-Commons/actions/runs/37650180952), job 112893728326, source `63daba9b4fcdde8fb2eb8d52645c870f0f3b5a1f`.
The job ran 2026-10-07 16:17:59–16:20:08 UTC and concluded FAILURE.
Full workflow stdout and metadata are preserved. Input graph and command receipts were recovered from the logged structured lines, not inferred.

The pinned runtime authenticated, Mathlib cache retrieval passed, and `UnifiedLean.G6.FiniteProbability` compiled successfully at 16:20:00 UTC. Its seven printed theorem reports contain only `propext`, `Classical.choice` and `Quot.sound`. This establishes the scoped finite probability algebra at these exact source bytes, not a full source bridge or master theorem.

`Conditioning.lean` then failed: the `ℝ≥0∞` notation at line 13 required the ENNReal scope, and the old `mul_le_mul_right'` identifier at line 53 is unavailable in the pinned Mathlib. The subsequent `sorryAx` reports are elaboration-error artifacts, not accepted mathematical proofs. SourcePrefix was not reached; ProgramPrefix was not in this frozen target list.

Superseding implementation fixes enable `open scoped ENNReal`, use `mul_le_mul'` with reflexive second factor, cancel the positive exponential explicitly in normalized coefficients, and add the same-initial-distribution program proof. They remain UNCHECKED until a later successful exact-source run. The historical first failure remains in the parent packet.
