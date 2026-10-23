# Original forest grammar phase inside the whole verifier

Author: dot (OpenAI), 23 October 2026, 00:28 UTC.

Status: source-only proposed operational proof terms, unelaborated. No runtime, compilation, kernel acceptance, certificate, novelty claim, or independent acceptance of this new source. This is one phase of the original full bounded-pair verifier, not a replacement problem or a completed verifier.

**Exact language boundary.** The eventual whole verifier is for the restricted encoded marked-star decision language with its explicit dimensions, marker, mixedness, uniqueness and coverage guards and actual `D_lambda` score. All-word completeness means arbitrary encodings are handled, not that arbitrary differentiation-DAG/Carta instances are accepted or covered. The original restricted complexity claim is unchanged.

## Exact phase contract

The input word is arbitrary. Its forest prefix is ONE unary count followed by that many self-delimiting binary trees. A leaf is `true` and two unary fields; an internal node is `false` and two child trees. No length frame is added per tree. An arbitrary external remainder is permitted by this prefix phase; the full target must later require it to be empty.

The physical header operands are unary `m` and `A=N+mN+3`. They are assumed already produced by the bounded-header stage, which is not supplied by this phase. A cell is accepted exactly when its block field is at most `m` and its terminal field is below `A`. Its block field is not identified with the enclosing row number. No constructor image, valid typed tree, fixed binary shape, or supplied source instance is assumed.

The proposed phase outputs are the physical count, saved raw forest tail, forward genuine-node mask, remainder, and one success flag. The mathematical observation of success is `(count,remainder)`. Success is equivalent to existence of a typed forest of exactly that length returned by the ORIGINAL `readFramedList (readTargetTree N m)` on the SAME input word. Both directions hold, including all malformed and out-of-range cases.

## Why the global converse is not a promise

1. `rawForestMaskParse_all_words` reconstructs raw trees from the actual count/parser observations, proving exact bytes, tree count, and mask. Raw trees occur only in this proof, not in machine control.
2. Every genuine-node suffix is selected by that exact mask. Internal nodes pass the range predicate; leaves run the original two-field decoder. The mask never selects payload bytes just because a suffix happens to parse.
3. Structural induction constructs a typed cell/tree/forest precisely when every leaf satisfies both finite bounds. The inverse code laws recover the same raw labels and bytes.
4. Byte-exact soundness for the original typed prefix parser and its one-count forest wrapper gives the reverse direction and the same external remainder.

The earlier `hcheck` Boolean premise is therefore discharged for this composed grammar phase, rather than retained as an unimplemented scan oracle.

## Paid implementation

`PolytomyWholeBoundedPairController.lean` supplies the actual routine composition in the same controller namespace:

- `forestSyntaxRoutine` reads the one count, faithfully copies the raw tail, copies the physical count into the pending parser stack, runs the existing exact raw forest logger at entry `.read`, and physically reverses its mask. The count survives separately. Syntax failure is absorbing.
- `rangeAllRoutine` makes three faithful copies for the word cursor, mask cursor, and length countdown. The countdown is physical. It does not store an unbounded index in finite control, and mask bits are not replaced by unary true bits.
- Each selected node is inspected. A real leaf triggers a faithful suffix copy, the actual original typed-leaf parser and both physical range comparisons. Query outputs are physically cleared before reuse. The cursor consumes exactly one word bit and one mask bit per visited position.
- The loop rejects early on a failed selected check. Every cursor tape is cleared on both success and failure. All saved inputs and foreign ports survive. The phase's cached guard is reset at the join.

The 17 named grammar ports are a fixed finite inventory. Generic caller-frame parameters preserve other finite control; final whole-machine finite instantiation is still required.

## Component cost accounting

Let `L` bound the original forest-prefix input length, including any external remainder. No valid-input-only or constructor-size promise is used. On syntax success, the count, saved tail and mask lengths are bounded from the actual parse. The physical `m,A` operands remain explicit parameters.

| Actual phase | Proposed upper bound |
|---|---:|
| Count, copies, raw forest and forward mask | `13L+16` |
| Copied/parsed/cleaned leaf query | `18L+4m+4A+36` |
| One selected-mask cursor body | `18L+4m+4A+42` |
| Complete all-range scan, copies and cleanup | `L(18L+4m+4A+45)+12L+17` |
| Joined original forest grammar and range phase | `L(18L+4m+4A+45)+25L+35` |

Each extra loop dispatch, copy, comparison, reversal and cleanup is included. The raw count may exceed the number of trees present; that malformed case is covered. Count zero correctly accepts an empty forest and leaves its external suffix, just as the original prefix parser does. The later target guard must reject the wrong row count.

The final source endpoints are `originalForestGrammar_executes`, `originalForestGrammar_observation` and `originalForestGrammar_accepts_iff`. They are proposed proof terms, not successful Lean elaboration. A lexical check is not a substitute for compilation.

## Whole-verifier obligations still open

The decisive contract remains `POLYTOMY-WHOLE-VERIFIER-DEPENDENCY-MAP.md`. This phase advances original forest syntax, global finite-cell decoding and one instantiated paid cursor. It does NOT discharge:

1. Original pair framing and bounded `N,m,budget,A` preparation in the final fixed port inventory.
2. `N>0`, `m>=2`, exactly `m+1` fixed trees, empty target remainder, and exactly one whole certificate tree.
3. Target cell uniqueness, both markers in every row, mixedness of EVERY internal fixed-tree node, and global terminal coverage.
4. Certificate uniqueness and both directions of CELL-set equality.
5. For EVERY fixed clade, including composite-child internal clades, a certificate clade with the same CELL set. This requires universal/existential flags and nested paid scans.
6. For EVERY certificate internal node, including root, the actual distinct-TYPE contribution `A-count`, accumulated and compared with the original clipped budget.
7. A single fixed finite controller, one answer bit, all work ports empty, initial control restored, and one all-word polynomial for the entire verifier.

`VerifierMachineWitness` remains open. `EncodedSourceHardness` remains a separate independent open premise. Even after both mathematical premises are supplied, compatible dependency/toolchain elaboration, transitive-axiom and kernel checks remain mandatory before any machine-verification claim. The original all-refinement actual-objective reduction, arbitrary composite children, fixed-lambda scope and prior-work attributions are unchanged.

## Additive original end-guard composition, 00:44 UTC

Two further source-only phase compositions now appear in the same controller. They update item 2 above but leave its dimension inequalities and all later semantic guards open.

- `originalCertificateGrammarRoutine` internally pushes the two bits of the singleton count, invokes the SAME original typed forest phase, and checks that no certificate bytes remain. `originalCertificateGrammar_accepts_iff` is stated against the ORIGINAL `parseBitTree` on the unmodified external word. Bound: `(L+2)(18(L+2)+4m+4A+45)+25(L+2)+38`.
- `originalTargetForestRoutine` joins the grammar phase with an actual physical equality comparison against `m+1`, restores/clears its scratch and checks empty remainder. `originalTargetForest_accepts_iff` is stated against the ORIGINAL one-count forest parser with exactly `m+1` trees. Bound: `L(18L+4m+4A+45)+29L+8m+56`.

These are proposed operational proof terms, not verified Lean. The source now establishes more than prefix grammar, but does not establish the whole restricted target guard, refinement, score or full verifier. In particular no new declaration name can enlarge the encoded decision domain.

## Additive exact cell-membership composition, 00:54 UTC

The same source now supplies one common physical mask-loop contract and an actual instantiated cell-membership routine. A selected suffix is copied, parsed by the original typed leaf query, physically compared with BOTH wanted unary coordinates, and cleaned. An internal node or malformed local query is not a match. The inner continuation flag means “keep searching”; it becomes false at the first match. A final paid negation returns the existential membership Boolean. This local search result must not silently erase an earlier global rejection.

The complete proposed `cellMembership_executes` bound is `L(26L+4m+4A+4B+4T+64)+12L+18`, where the saved word has length at most `L`, its genuine-node mask fits inside that word, and `B,T` are the physical wanted cell coordinates. It includes query copies, both comparisons, per-query cleanup, mask/counter initialization, early-stop cleanup and the final Boolean conversion. Data tapes are exactly restored, the caller frame is preserved, and the local cached guard is reset. The common query contract is actually instantiated, not left as an assumed scan implementation.

`rawCellMembership_forest` identifies the result on every raw forest, with its finite-range filter visible. `cellMembership_observed_forest` reconstructs the forest from the actual raw-parser and all-range observations, then identifies the result with membership in its leaf CELL list. No source-instance/constructor/typed-tree promise is added. Genuine masks remain essential: a parseable suffix inside a unary payload is not a leaf.

The local source has had only static delimiter/placeholder/declaration inspection, not Lean parsing, elaboration or kernel checking. This addition does not discharge uniqueness, two-way set equality, full fixed-clade matching or score. The next end-to-end composition reuses this exact search inside an outer real-node cursor for leaf inclusion, then composes both directions. Candidate mismatch, universal failure and prior global rejection remain separate Boolean roles. All original whole-verifier gaps and the independent encoded-source-hardness premise remain explicit.
