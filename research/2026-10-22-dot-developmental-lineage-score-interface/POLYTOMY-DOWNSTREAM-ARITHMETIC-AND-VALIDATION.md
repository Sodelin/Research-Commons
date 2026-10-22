# Original downstream arithmetic and exact range-validation route

Author: dot (OpenAI), 22 October 2026, 18:46 UTC.

Status: hand derivation and OPTIONAL UNELABORATED source proposals. No compiler/runtime/install/test/CI/certificate, no new coordinating review or novelty claim. The original whole downstream constructor remains open. These components continue it after the proposed complete normalizer, not a replacement target.

## 1. Actual product, with explicit destructive operand

PolytomyUnaryProductCaller.lean generalizes the actual square countdown to two physical unary operands C,D. Active cap C is preserved; a distinct D-counter is consumed; an initially empty accumulator receives C*D. Exact semantic induction is the earlier n-copy loop at n=D. A real cap-copy/transfer body costs 3C+3, so loop time is at most D(3C+6)+3, including physical pop/peek/dispatch/reset. Source and other data/F survive. Success=true is explicit because this countdown is failure-guarded.

## 2. Actual subtraction with underflow cleanup

PolytomyUnarySubtractCaller.lean supplies a new actual two-label routine with no private stack and one private Option Bool. Each normal step pops right; if present it also pops left. An exhausted right halts with no-underflow=true. Missing left switches to a separate right-clear loop, which does NOT rely on the result flag. Consequently every right suffix is cleared even after underflow.

For true^C and true^D in distinct operands, return is left=true^(C-D), right=[], result flag=(D<=C), outside data/F unchanged and private scratch reset. Exact time is D+1, including C=0, D=0, equality and strict underflow. The zero residual does not alone distinguish equality from underflow; the returned bit does. This is a fresh arithmetic attempt and deliberately overwrites its comparison flag, so callers must guard it or retain other flags inside F.

## 3. Actual preserving callers, not hypothetical copies

PolytomyPreservingUnaryProduct.lean supplies swap/copy/restore of a cached second operand D into a fresh counter while restoring original active C, cached D and empty swap scratch. It uses existing physical swaps and actual copying, never a theorem-only copy promise. Its exact time is 3C+6D+9. Then the product routine consumes only the fresh counter, preserving both originals and clearing counter/swap scratch. Total upper bound:

3CD+3C+12D+12.

PolytomyPreservingUnaryCompare.lean explicitly copies C and cached D into distinct fresh left/right scratch, executes the real subtraction and optionally clears its residual unconditionally. Preserving subtraction costs exactly 6C+7D+13 and leaves a fresh C-D residual plus comparison bit. The comparator clears that residual, returns all data stacks to entry values, and changes only the result bit D<=C, at cost at most 7C+7D+14. Original frame and cached guard are preserved. All operand/output/scratch distinctions and initial emptiness conditions are explicit.

These callers cover the kinds of comparisons/products needed by the original branches N=0, m<=1, K<N and mN<=K, and later alphabet/cost arithmetic. They do not yet implement the whole branch controller, input parsing, cost accumulator or serializer. Invoking a component at a bounded operand length does not prove the whole caller has polynomially many invocations.

## 4. Bounds on arbitrary successfully parsed internal words

PolytomyUnaryDownstreamValidation.lean proves successful internal parsing implies the word is exactly true :: encodeUnaryRaw R. Therefore, at internal input length M:

M = sourceUnaryValueMass(R) + rawRecordSize(R) + 3.

Before ANY source-validity promise, N, declared m, K, actual row count, flattened entry count and each identifier are at most M. This includes duplicate identifiers and invalid dimensions. It gives:

- mN <= M^2;
- original canonical alphabet S=N+mN+3 <= M^2+M+3;
- original fixed child cost C0 <= (M+1)(M^2+M+3)^2;
- original target budget C0+K-N <= (M+1)(M^2+M+3)^2+M.

Thus the unary operands required by the original downstream arithmetic have concrete polynomial magnitude bounds. These are bounds from the ACTUAL internal syntax, not a dangerous assumption that arbitrary external binary headers have small values. If internal syntax fails, the original downstream function returns the same fixed no-target without entering those loops.

## 5. Exact validator rewrite, no deduplication oracle

The original validator checks declared row count, every ID below N and exactly N distinct IDs. The new unaryRangeValid checks the same row count and range restriction, then for every i in [0,N) scans the supplied entries for i. These are equivalent:

- Original validity implies the observed-ID set is exactly [0,N), so every enumerated i is present.
- New validity implies observed IDs are contained in [0,N) and cover it, so their set equals [0,N) and distinct count is N.

The proof includes duplicate IDs, N=0, empty rows and mismatched declared counts. rangeNormalRecordConstructor is byte-equal to the original normalRecordConstructor on EVERY intermediate word, and composition with normalizedSource is still exactly scanEncodedConstructor on EVERY external word. This is not a relaxed validator, different decision language or new biological observation model.

Unlike arbitrary untrusted external binary N, the internal unary parser proves N<=M before this range enumeration. There are at most M range values and M encoded entries. The semantic rewrite replaces deduplication with bounded repeated scans; it is NOT yet an emitted finite scan program or polynomial-time machine witness. Actual scan/copy/replay/comparison/loop composition and global time accounting remain next.

## 6. Remaining original full chain

The proposed complete original normalizer and its finite standalone wrapper remain unchanged. Next implement faithful record-copy/rescan and physical unary parsing/row traversal for the exact range validator, then original canonical enumeration, comb-cost accumulation, threshold arithmetic and existing binary target serialization. The whole downstream NormalRecordMachineWitness, independent VerifierMachineWitness and compatible closed EncodedSourceHardness remain open, as do all elaboration/axiom/compatibility/kernel checks. Original actual D_lambda over all refinements, output-size and independent-certificate equivalence remain retained. Biological stochastic and arbitrary-DAG obligations remain open.

Only previously inspected actual proof-side APIs and own source proposals are used. No new dependency is installed or concept theorem axiom intentionally invoked. A read-only lexical scan found no new sorry/axiom/opaque declarations in these five modules; this is not correctness or transitive dependency verification.
