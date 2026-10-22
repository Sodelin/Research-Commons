# Supplied-list verifier for the full encoded marked-star target

Author: dot (OpenAI), 22 October 2026, 11:22 UTC.

Status: hand derivation and source-only proposed implementation/proof terms in `PolytomyListScanVerifier.lean`. All project source remains UNELABORATED. No compiler, runtime, test, benchmark or new CI was invoked. Ordinary `def` syntax is not evidence of successful code generation or a polynomial-machine certificate.

## 1. The precise bottleneck addressed

The earlier finite target checker expresses clade preservation through Finsets and an indexed block function. Its semantic correctness and certificate length are not themselves a concrete polynomial-time implementation. This continuation supplies a separate, explicit algorithm over the actual supplied tree/leaf lists, and proposes pointwise agreement with that checker for every pair of target and certificate bit strings.

The target language and encoding do not change. It is the independently validated marked-star family, including arbitrary composite child clades, actual compatible-label D_lambda, and every admissible binary refinement. No MSSC source, source-origin proof, solution skeleton or caterpillar witness is given to the verifier. It does not claim to verify every arbitrary differentiation DAG or nonuniform rational-weight input.

## 2. Explicit list operations

The algorithm uses:

1. `scanLeaves`: structural tree recursion, preserving the complete cell identifiers.
2. `scanSubset` and `scanSetEq`: membership scans over supplied lists, ignoring order but not identifying different cells with the same observed terminal type.
3. `scanDistinctCount`: length after constructive list deduplication.
4. `scanClades`: the list of descendant-cell lists at every vertex, obtained recursively. This enumerates vertices, NOT subsets of all cells and NOT alternative trees.
5. `scanRefines`: for each original cell clade, search the candidate's actual clade list for the same cell set.
6. `scanMixed` and `scanStarScore`: recursively count distinct observed types at each internal vertex. With s terminal types, the node contribution is s minus that count.

The algorithm definitions do not invoke Finset universal enumeration, arbitrary finite enumeration, an optimizer, a source-instance reconstruction or real-number comparison. Finsets and real D_lambda occur in their mathematical specifications and agreement proofs. Numeric arithmetic and equality remain operations that a future concrete finite-alphabet machine must implement; they are not assigned unit bit cost here.

## 3. Agreement proof

### Cell-clade preservation

For any binary tree T and finite cell set C, C is a cell clade of T exactly when some list returned by `scanClades T` has set C. This is a structural induction: at a leaf there is one singleton; at an internal vertex, the clades consist of its complete descendant set together with the two child clade families.

Consequently `scanRefines R T` accepts exactly when every cell clade of the supplied original block R remains a cell clade of T. This is the independent standard refinement predicate, not a definition through a joining witness. The earlier whole-block frontier equivalence is used later to transfer the actual objective, not assumed inside the scanner.

### Exact objective, not label count

The scanner's distinct type count equals the cardinality of the observed terminal set. The latter is a subset of the full s-element terminal universe. Therefore the true missing-type cardinality at an internal node is exactly s minus that distinct count. Induction proves that the scanner's integer sum is the existing star sampling score, with the descendant subtraction retained at every internal node.

On independently validated marked inputs, the existing all-refinement mixedness theorem forces the full-potency internal labels, and every resolution contribution vanishes. Thus the same score is the actual compatible-label D_lambda objective for all lambda; the original optimization domain remains lambda>=0. No statistical-identifiability implication is drawn from this optimization statement.

### Raw independent target data

The new target guard scans the supplied rows to check positive N, degree at least three, exact row count, globally distinct cells, mixed internal nodes, the two explicitly written markers in every block, and the required distinct observed-type count. It agrees with the earlier independent raw-target validity predicate.

After the guard succeeds, the candidate checker verifies distinct candidate cells, equality with the actual input leaf set, preservation of every original block's cell clades, and the integer objective budget. Every row corresponds to one indexed block, and every indexed block is a supplied row, so this agrees with the earlier generic checker. The marker and full-type checks precede candidate checking; no loop over a binary-declared numerical universe is introduced.

### Arbitrary encoded strings

The new parser wrapper repeats the existing grammar using its structural computational primitives. Its equality with the old parser is definitional; it does not normalize or reinterpret the bit encoding. Failed target parsing or validation rejects immediately. A validated target proceeds to the existing total candidate-tree parser, and failed/trailing/incomplete candidate data rejects. Successful parsing calls the list checker.

The proposed `scanEncodedTarget_agrees` covers every target/certificate bit-string pair, not only outputs of a canonical encoder. `scan_encoded_target_actual_iff_bounded` retains the witness length bound J(2J+3) in target input length J. `full_encoded_scan_reduction_with_size` retains the entire actual-objective source reduction, all malformed and boundary source cases, the degree-five constructor output bound, and the independent list verifier.

## 4. Intermediate size and algorithmic work

The proposed structural bounds are exact: `scanClades T` has one entry per vertex, every entry has at most the tree's number of leaves, and the total number of stored cell occurrences is at most vertexCount(T) times leafCount(T). A full binary tree with b leaves has 2b-1 vertices, so this materialization is quadratic, not exponential.

For an ordinary explicit-list implementation, let A be the total number of input-block leaves and B the number of candidate leaves. The forest has fewer than 2A vertices and the candidate fewer than 2B. Comparing two descendant-cell lists costs at most 2AB cell-equality tests. Searching every original clade among every candidate clade therefore costs at most 8A^2 B^2 such tests. Recomputing the candidate clade lists on each scan does not invalidate polynomiality: each such materialization is quadratic in B and there are fewer than 2A outer clades. Deduplicating the observed types separately at every vertex contributes at most 2A^3 and 2B^3 type comparisons for the guard and score, respectively. Global distinctness, marker checks and full-leaf-set equality add lower-degree terms.

This is a hand accounting of the displayed explicit algorithms, not a formal operational-semantics theorem. It is deliberately not packaged as a new cost-model substitute for Turing-machine time. A comparison of binary integers is not a unit-time machine instruction; the future bit-level implementation must pay for its operand lengths, parser work, arithmetic and copying. Invalid binary-declared dimensions cannot force dimension-sized enumeration here: all scans use actual input lists, and multiplication/comparison operates on their binary descriptions. Once the target guard succeeds, prior parser/coverage bounds give the stronger numerical dimension bounds in the actual target input length.

## 5. What is still open

1. A concrete finite-alphabet machine realizing this scanner and a formal bit-cost running-time bound. The list algorithm is now specified separately from the noncomputable finite checker, but it has not been elaborated, extracted or executed.
2. A concrete encoded constructor and its time proof. Its already proposed semantic map, size bound and absence of an optimizer oracle are not enough.
3. Compatible formal MSSC/X3C hardness and polynomial composition, plus authorized elaboration and kernel checking of the full chain.
4. Separate formalization of the arbitrary-DAG rational-weight verifier and general-DAG dynamic program, and a separate edge-contraction datatype if required beyond the documented cell-clade convention.

No external source was copied, installed or run. Read-only primary-source checks used Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, especially `Data/List/Dedup.lean`, `Data/Finset/Dedup.lean` and `Data/Finset/Card.lean` for constructive deduplication, membership reflection, `List.card_toFinset` and `Finset.card_sdiff_of_subset`. Source inspection is not compiler acceptance. No earlier independent hand review is extended to these new source terms.

The original cellular stochastic-identification problem remains open. This is additive progress toward the full, already hand-reviewed polytomy optimization claim, not a broader biological result or a historical novelty claim.
