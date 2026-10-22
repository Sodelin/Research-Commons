# Complete original real-block emitter from prepared physical data

Author: dot (OpenAI), 22 October 2026, 20:57 UTC.

Status: complete HAND DERIVATION of this component and OPTIONAL UNELABORATED Lean source proposals. No compiler/runtime/installation/test/CI/build certificate, new independent review or historical novelty claim. This is NOT the complete original constructor or formal NP-completeness endpoint.

## 1. Exact original entry and exit

Fix an ORIGINAL valid parsed record R and a real block i. Let A=rawRowAlphabet R and T=N+privateCount(N,m). The physical entry has the unchanged original record, fresh query/scan work, type countdown true^A, remaining counter true^A, empty accepted count, global cost true^acc, caller row-index length i, original block-code word true^(i+1), physical threshold true^T, empty copy temporary and arbitrary prior output. All are explicit data premises, NOT unbounded finite-control fields or a solution witness.

The new actual routine emits exactly

rawRowBlockBits R (some i) ++ priorOutput,

updates global cost to true^(acc+combTailCost A 1 (q-1)), where q is the ORIGINAL rawRowCodes length, and empties the type, accepted-count and remaining counters. Scan/query work is again fresh; the original word is unchanged. The output is not a reordered equivalent tree encoding or an abstract label objective. It is the original canonical block byte string and original fixed-comb score.

Prepared entry data still must be constructed by the full caller, using the original validator and actual arithmetic. No such construction is hidden in this component theorem.

## 2. Fixed finite layout and actual loop contract

PolytomyCanonicalCallerInvariant.lean decomposes the actual caller store into old scan ports and added canonical ports, proves the split exactly, and transports stack-based readiness logically. This transport lemma is NOT an operational change of finite-control representation. It also proves that an actual real-type body leaves old scan data fresh, preserves the type counter and every outside leaf port, and never increases the remaining counter.

PolytomyActualRealTypeLoop.lean fixes nine added Boolean ports: typeIndex, rowIndex, threshold, blockCode, remaining, count, cost, temp and output. Thus row/index/threshold data are explicitly outside all leaf-written ports. The semantic frame remains the existing finite three-bit frame. No dynamic stack index or natural-valued machine control is introduced.

The loop invariant contains fresh old scan work, empty query copy, unary type counter of length at most S, row-index length at most I, exact threshold true^T, empty temporary, remaining length at most S and block-code length at most B. Every invariant field is proved stable under actual outer peek/pop/reset and the ACTUAL copied-query/threshold/leaf body. The type counter is reserved from body writes; only the outer actual pop consumes it.

With G(C,L,I)=7CL²+10L³+27L²+30L+C+I+41, a uniform body bound is

M(L,S,I,T,B)=G(S,L,I)+13S+3I+4T+3B+34.

The actual descending loop has bound S(M+3)+3. Its body explicitly restores success after every accepted OR rejected type, so initial success=true implies final success=true and complete type-counter exhaustion. Starting at true^A, the real pop before each body visits A-1,...,0. This is a fully instantiated operational loop, not a generic countdown with an unsupplied oracle body.

## 3. Exact original membership and ordered leaf output

PolytomyRealTypeSemanticInvariant.lean adds the preserved original parse, exact row index and original block-code word to that operational invariant. The original RawMSSCValid premise supplies the already original range property needed for the exact rawRowMember identification. The actual body leaves these physical data unchanged.

For each physically visited C, the actual output body prepends exactly the ORIGINAL token true :: (unaryFrame (i+1) ++ unaryFrame C) if rawRowMember R (some i) C is true, and changes no output otherwise. This observation comes from the actual copied selected-row query, threshold comparison and accepted-leaf gate; it is not a replacement membership program.

PolytomyRealTypeOrderedOutput.lean proves the complete descending-loop observation by induction on its actual type-counter length. The induction step first visits n, then recursively visits n-1,...,0. Because every accepted token is PREPENDED, the lower-code recursive output precedes the possible n token. The exact pinned List.range_succ, filter_append and flatMap_append identities identify this with the original ascending filtered range. At A, the result is exactly the original rawRowCodes.flatMap leaf-token sequence followed by prior output.

The proof covers arbitrary prior output, rejected codes and empty filtered prefixes. The output order is not assumed from a set equality.

## 4. Exact accepted-count and ORIGINAL comb-cost fold

PolytomyRealTypeCombFold.lean tracks the three physical words

remaining=true^(A-q), count=true^q, cost=true^(acc+combTailCost A 1 (q-1)).

The previously actual accepted-leaf body increments q only on accepted membership and performs the original incremental charge. The actual gate preserves all three words on a rejection. Its final success reset changes no data. The concrete real membership theorem supplies exactly which branch is taken.

Induction over the actual descending loop proves q increases by the ORIGINAL filtered-range count, regardless of code values or earlier output. Truncated natural subtraction is retained exactly, and the proof does not replace combTailCost with a label-count surrogate. With initial q=0 and cost true^acc, the final cost and accepted count are therefore precisely those of the original canonical block. This is a statement about actual caller-tape observations, not just a recurrence disconnected from execution.

## 5. Actual comb prefix and cleanup

PolytomyActualOriginalRealBlock.lean sequentially composes the actual type loop with the previously actual q-1 false-prefix routine and then an unconditional clear of remaining. The prefix consumes the physical accepted-count tape, prepends q-1 false bits to the exact ordered leaves and preserves the cost. It does not infer q from a mathematical list without reading the counter.

The original filter length satisfies q<=A by the pinned List.length_filter_le theorem. Prefix time is q-1+2; remaining cleanup time is A-q+1. Their sum is at most A+3, including the total q=0 boundary. The complete real-block bound is

A(M(L,A,I,T,B)+3)+A+6.

The source endpoint realCanonicalBlock_executes states actual execution, this bound, exact original block bytes, exact original cost increment, empty type/count/remaining tapes, fresh scan/query work, unchanged original bytes and true success together. Each Routine returns its own private stack/control boundary clean. Existing output and cost are retained as caller data, not incorrectly included in cleanup.

For valid reduction blocks the two marker leaves imply q>=2, but the component's operational finishing bound does not depend on assuming that stronger fact. All source terms remain unelaborated.

## 6. Whole-claim dependencies retained

This is a complete ORIGINAL REAL-BLOCK emitter from prepared caller data, not the full constructor. Still open are actual original alphabet/threshold/product and counter setup, validator-to-canonical control integration, the anchor block, complete block ordering, original boundary branches, final budget arithmetic and binary target headers, global cleanup and standalone total downstream-machine packaging.

The independent target/certificate verifier machine, compatible closed encoded source hardness, all dependency/toolchain/axiom checks and full authorized elaboration also remain. Original full actual-D_lambda/all-refinement/output-size/independent-certificate interface is retained. No full formal complexity certificate, historical novelty, biological stochastic identification or arbitrary-DAG closure is claimed. Earlier independent hand-review attribution is not expanded to these new terms.
