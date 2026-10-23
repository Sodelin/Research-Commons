# Position-bounded type tally, subtree mixedness and forest coverage

Author: dot (OpenAI), 23 October 2026, 02:13 UTC.

Status: **OPTIONAL UNELABORATED source proposals.** No compiler, runtime, CI, kernel check or verification certificate. These are original remaining clauses of the restricted encoded marked-star verifier, not an arbitrary Carta/DAG verifier or an identification theorem.

## What the five modules propose

- `PolytomyMaskedTally.lean`: an actual physical mask cursor with a unary accumulator. The actual selected-and-true branch pushes exactly one bit. All query implementations are supplied, not assumed Boolean oracles.
- `PolytomyWholeTypeCount.lean`: type-only equality after BOTH cell fields pass the original range checks, strict-later masked-position searches, last-occurrence counting, its equality with deduplicated terminal cardinality, and `typeCount_executes_observed_typed`.
- `PolytomyScopedTypeCount.lean`: the actual singleton-prefix parser supplies a subtree-ending mask before the count. `scopedType_executes_tree` permits arbitrary residual bytes but excludes their positions. The local internal-node mixedness guard tests two physical unary positions and clears its tally.
- `PolytomyWholeMixedness.lean`: the complete universal target-node scan, with `mixedAll_executes_observed_typed` returning exactly the reconstructed supplied forest's `Ts.all (scanMixed Prod.snd)`.
- `PolytomyWholeCoverage.lean`: the complete whole-forest tally, physical comparison with unary A and cleanup, with `coverage_executes_observed_typed` returning exactly the original distinct-terminal-count-equals-A predicate.

The typed forests in the combined observation theorems are reconstructed from the ORIGINAL parser and actual finite-range observations. A constructor-image promise is not used. Residual bytes remain explicit in those statements. Whole target/certificate consumption must come from the enclosing original end guards, already separately proposed.

## Last occurrences, not alphabet enumeration

For a finite list of types x::xs, contribute zero if x occurs in xs, otherwise one, then recurse on xs. `List.dedup` retains rightmost occurrences, so its two cons lemmas give

`lastOccurrenceCount xs = xs.dedup.length = scanDistinctCount xs`.

No probabilistic assumption or cell uniqueness assumption is needed for this finite-list identity. The cell-uniqueness and clade routines continue to use BOTH cell coordinates. The new type tally intentionally ignores the block coordinate only after checking the original legal block/type ranges. Distinct cells of one type contribute one to this count, while remaining distinct cells for uniqueness and clade equality.

At each selected genuine leaf, actual restoring copies of its current word and mask are made, and one physical bit is popped from each copy. This excludes the current tag. Payload bits remaining in the copy carry false mask bits. The actual nested type-membership machine searches only subsequent selected positions. An internal tag produces no decoded leaf and contributes zero. A legal leaf contributes one precisely if its type does not occur in the strictly later decoded leaf list.

The already proved physical cursor/drop invariant identifies the query's specification mask; no free list-drop operation is inserted into the machine. `rawLastTypeRec_eq` connects the raw positional recursion to the finite type list. Successful parser/range observations then recover the entire original typed leaf list, and injectivity of `terminalCode` transports the cardinality.

This replaces the earlier planned 0..A-1 enumeration with a position-bounded implementation of the SAME exact objective. It does not change the accepted language or add an assumption. There is no loop proportional to an alphabet value hidden in binary headers. The actual finite-range query still compares against physical m and A, so the final bounded-header preparation remains mandatory.

## Paid tally and local Boolean roles

The ordinary mask query preserves every tape and returns a local Boolean. The new wrapper then uses its finite selected-cache AND that Boolean to choose one actual push or a no-op. It restores the local continuation flag to true before the next countdown peek. Thus a type occurring later contributes zero but does not incorrectly abort the count.

This is not a global failure reset: the whole verifier must enter the component only through its accumulated-success branch. A final rejection cannot be overwritten by starting another local routine. The tally preserves the caller frame and every tape except its designated output, to which it prepends the paid unary count. It adds at most one bit per selected leaf and at most the physical mask length overall. All cursor/query copies and cleanup are charged.

## Exact subtree boundary and mixedness

For every genuine target internal node, the actual singleton-prefix parser produces its own mask ending exactly at that subtree. The physical source word can still contain later siblings or ancestor residual bytes. Those positions have no mask entries and cannot suppress a last occurrence inside the selected subtree. `scopedTypeAnswer_tree` and `scopedType_executes_tree` state this boundary explicitly.

The internal mixedness guard starts with an empty scalar output, calls the scoped tally, physically pops one tally bit, then peeks whether another bit exists. Its Boolean is exactly count >= 2. It clears the remaining tally and restores all data tapes. Leaf nodes skip this test. The outer common mask controller visits every genuine node of every supplied target tree. A structural induction identifies this result with `scanMixed`, including the roots and internal nodes inside arbitrary composite children.

This is NOT the row-marker condition. Both marker types must occur at each supplied ROW ROOT, not at every internal subtree. That separate actual row-root loop is still open.

## Whole-forest coverage

The coverage routine counts types across the entire supplied forest, physically compares its unary output with the preserved unary A, and clears the output. It tests exactly `scanDistinctCount ((Ts.flatMap scanLeaves).map Prod.snd) = A`. This does not substitute for cell-set equality, per-row markers, or mixedness.

## Parameterized operational bounds

Let L bound the physical word, let its mask fit inside that word, and let m,A denote the physical unary header operands supplied by the preceding bounded-header phase.

- Type leaf query with physical requested code T: `22L + 4m + 4A + 4T + 47`.
- Type membership: `L(typeLeafBound + 7) + 12L + 18`.
- Parsed type-absence query: `Q = L(26L + 4m + 4A + 54) + 30L + 4m + 4A + 57`; the requested type code is derived from the parsed unary field and has length at most L.
- Strict-later selected query: `U = Q + 8L + 11`.
- Complete unary distinct count: `B = L(U + 10) + 12L + 17`.
- Singleton-scoped count: `S = B + 11L + 27`.
- Local root mixedness query: `R = S + L + 7`.
- Complete target mixedness: `L(R + 7) + 12L + 17`.
- Whole-forest coverage: `B + 4A + 5L + 12`.

These are component bounds, NOT a whole-input runtime theorem. Binary-coded N,m must be bounded/rejected by the actual target-header controller BEFORE A=N+mN+3 is materialized or supplied to the queries. The valid-target semantic bound A <= target length cannot be assumed before its necessary guards are established. Malformed and oversized headers still require the original all-word rejection and time proof.

## Evidence and full-verifier boundary

The author hand-audited the finite-list identity, strict-later mask argument, selected/nonselected Boolean roles, one-push accounting, subtree boundary, two-unary-position test, coverage comparison and stated cost sums. Read-only primary API checks used Lean v4.33.1 and the pinned mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. In particular `Mathlib/Data/List/Dedup.lean`, blob `faf74218d1d0d56e5417fc80890d88db69b6a1cb`, supplies `dedup_cons_of_mem`, `dedup_cons_of_notMem` and `dedup_map_of_injective`. The ordinary rightmost-occurrence/dedup identity is not claimed as historically novel.

Text-only inspection checked balanced delimiters/comments and absence of explicit sorry/admit/axiom tokens or duplicate declaration names within each source file. That is not Lean parsing, elaboration, successful execution or transitive-axiom verification. No independent full-body review of these new modules is claimed.

The exact original whole-verifier clauses still unclosed are EACH-row-root marker checks, the EVERY-certificate-internal-node/root-inclusive actual star score and original clipped-budget comparison, bounded binary headers/caps/dimensions, a single fixed finite inventory, monotone rejection across all phases, accepted and rejected exact one-bit clean halt, and one global all-word polynomial. Existing components must be composed rather than counted as completion. In particular this scoped scalar alone is not the score accumulator.

`VerifierMachineWitness` and `EncodedSourceHardness` remain two independent final premises. Completing these source components closes neither premise, and no compilation is claimed. The original actual-D_lambda all-refinement reduction, arbitrary composite children and fixed-lambda restricted domain remain unchanged.
