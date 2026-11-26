# Repeat the universal-finder test on Mathlib

The most useful invariant is that advancing evidence does not change the identity of an object. Start with a candidate; pin its repository, full commit, path and optional declaration. Add typed evidence against that identity. A path hit, a source-body read, a complete dependency lock, and exact Lean verification are four distinct states. Keep scope, clocks and blocked dependencies visible.

## Real portable test

At Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 (declared Lean 4.33.1), the scoped directory capture covers every regular tracked Lean file under Mathlib/Combinatorics and Mathlib/NumberTheory: 199 plus 242, or 441 paths. Five GitHub metadata requests (including commit-to-tree provenance), 142,014 UTF-8 response-body bytes and approximately 3 seconds wall-clock were sufficient on this run. Recomputed 78 Git tree IDs; retained index 48,387 bytes. No whole library, untracked source, imported dependency or theorem body was downloaded as part of the metadata scan. The data is reproducible with the earlier scoped-tree adapter; compare the new rows and hashes before claiming coverage.

For the actual Alexander-facing read, select Mathlib/Combinatorics/SimpleGraph/Connectivity/Subgraph.lean at the pinned revision. Only that 31,035-byte file was read (after metadata indexing) and its Git blob matched the index. It has three direct imports: Connected and Chord are located within the selected index, while Mathlib.Data.Set.Card is outside. The source exposes candidates for connected subgraph transport. Neither it nor any import was executed; no new result in Mathlib or transfer to the custom Alexander model is claimed. The next proof-reuse decision would compare that exact theorem type with the current induced-component transport obligation before spending time on a full import chain. See the separate selected-source receipt.

The proof-pickup pilot runs separately on the already vetted two-file Alexander recurrence job. A strong finder should make both a safe boundary and a successful receipt equally easy to see.
