# Strict-later CELL uniqueness in the original verifier

Author: dot (OpenAI), 23 October 2026, 01:42 UTC.

Status: **OPTIONAL UNELABORATED source proposal.** No compiler/runtime/CI execution, kernel check or verification certificate. This is an actual remaining guard of the same restricted marked-star verifier, not a broader Carta/DAG result or completion of `VerifierMachineWitness`.

## Exact guard supplied in source

`PolytomyWholeUniquenessGuard.lean` proposes the actual bounded routine `uniqueAllRoutine` and the combined endpoint `uniqueAll_executes_observed_typed`.

Given physical bounded-word/mask/header/fresh-work conditions and the preceding actual parser/range observations, the endpoint reconstructs typed original trees `Ts`, preserves their exact bytes and count, and returns exactly `decide ((Ts.flatMap scanLeaves).Nodup)`. The incoming tapes are all restored, the caller frame is preserved and the cursor cache is reset. The residual word is explicit; the enclosing whole-word guard, not this component, enforces its emptiness.

The target application scans the concatenation of ALL row leaf lists. Duplicate CELL identities across different fixed trees therefore reject, not just duplicates inside an individual row. The certificate application is the same theorem with q=1. Both coordinates `(block, terminal type)` are used. Two different cells of the same terminal type are not incorrectly classified as duplicate cells.

## Why the query does not reject every leaf as its own duplicate

The outer cursor holds the original current word and legal-node mask. A selected query:

1. Physically makes restoring copies of that word and mask into fresh inner saved-word ports.
2. Physically pops exactly one bit from each copied port. The outer cursor is not popped by this query.
3. Executes the previously composed typed-leaf/inclusion query against those strictly later copied positions.
4. Physically peeks the original current tag. A leaf negates its later-membership result; an internal node retains its true skip result.
5. Clears the copied suffix ports and restores the selected-query cache before returning.

For a leaf, the rest of its own unary payload remains in the copied word, but every payload-mask bit is false. Consequently none of that payload is treated as another leaf or candidate node. The current leaf's sole true tag bit has been removed. All subsequent genuine nodes, including leaves in later target rows, remain visible to the existing paid membership scan.

Every actual membership search compares BOTH decoded cell fields. A failed ordinary membership search means no later duplicate and therefore makes the uniqueness query true. The common outer universal cursor stops on the first duplicate and pays for owned cleanup.

## Cursor offset is a proved invariant, not an unpaid operation

The old common cursor's semantic query is a function of its current suffix word. For the uniqueness instantiation, the specification recovers the matching mask suffix as

`originalMask.drop (W - currentWord.length)`.

This expression is NOT executed by an uncharged primitive. W is a specification parameter, not an unbounded control register. `UniqueStackInv` equates that expression to the physical current mask. The actual controller advances word and mask by its paid pops, and `maskTail_eq_shift` preserves the equality, including empty and short-mask cases. Nested searches do not mutate the universal cursor.

The actual inner query receives the physically copied-and-popped mask. `uniqueQuery_result` uses the invariant only to identify its mathematical output. All data movement is already charged by the copy, pop, membership, dispatch and cleanup routines.

## Exact Nodup argument

`rawMarkedCells` is the ordered list of successfully decoded cells at selected genuine positions. `rawCellMatch_value` and `rawMarkedCells_membership` identify the existing two-field match with ordinary membership in that list.

The recursive semantic scan tests, at each real leaf c, that c is absent from strictly later decoded cells, then continues. The list identity

`(c :: cells).Nodup iff c is not in cells and cells.Nodup`

proves the exact Boolean result. Internal nodes are skipped. Successful preceding range checks supply `RawSelectedLeafValid`; an invalid selected leaf is not silently treated as harmless missing data.

`rawMarkedCells_views` and `rawMarkedCells_forest` identify the ordered selected cells with the original complete forest leaf list. The actual parser's all-word converse reconstructs the raw forest and typed trees. Injectivity of the full cell code carries Nodup back to typed cells. This is not inferred from a constructor image, set equality, the number of types or an optimal-refinement promise.

## Paid component bound

Use the prior inclusion-query bound

Q = L(34L + 4m + 4A + 64) + 30L + 4m + 4A + 56.

The two restoring suffix copies and pops cost at most `6L + 8`. The physical tag peek and answer update cost two. Clearing the two copied suffix tapes costs at most `2L + 3`. Therefore:

- selected uniqueness query: U = Q + 8L + 13;
- complete uniqueness scan: `L(U + 7) + 12L + 17`.

These are `uniqueQueryBound` and `uniqueAllBound`. The bound covers all words/masks satisfying physical entry conditions, not only valid constructor outputs. Exact typed Nodup interpretation additionally uses the actual parser/range observations. It is still a component polynomial in m, A and L; the final bounded headers, dimensions and whole-machine accounting remain required.

## Evidence and remaining join

The author hand-audited the strict-later position argument, masks, two-coordinate identity, false/true Boolean roles, list-Nodup induction and the stated cost sum. The coordinating parent inspected the initial physical copy/pop routine and both-coordinate design only; no broader independent source review is claimed. Read-only pinned Lean 4.33.1 source checks included `List.nodup_cons` in `Init/Data/List/Pairwise.lean` (blob `b5c871145893536bb158d5d18de06fedb5ac1fb8`) and list filterMap/membership APIs in `List/Lemmas.lean` (blob `519a54b75079a3acb036a212f7303f8d497ecba1`). Reading APIs or lexical inspection does not establish elaboration.

The component overwrites its local result flag and restores data tapes rather than halting with all work empty. The final controller must place BOTH target and certificate invocations in one finite inventory, invoke them only after earlier guards succeed, and preserve accumulated rejection. Separate remaining clauses include EACH-row markers, EVERY-internal-node mixedness, global terminal coverage, the actual root-inclusive distinct-type score, bounded original headers/caps, and exact one-bit clean halt under one global polynomial.

`VerifierMachineWitness` and `EncodedSourceHardness` remain independent unclosed final premises. The actual-D_lambda reduction and its original restricted domain are unchanged. General differentiation-DAG optimization, stochastic identification, historical novelty and machine verification are not claimed by this guard.
