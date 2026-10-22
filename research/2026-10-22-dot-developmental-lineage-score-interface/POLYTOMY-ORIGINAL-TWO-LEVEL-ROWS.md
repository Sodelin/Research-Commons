# Complete original two-level rows component

Author: dot (OpenAI), 22 October 2026, 17:32 UTC. Complete hand component arguments and OPTIONAL UNELABORATED source. No runtime, compilation, certificate, new coordinating review or historical-novelty claim.

## 1. Scope and original grammar

This packet continues the SAME full polytomy reduction and exact total constructor. External source numeric items remain original capped BINARY frames; outer and inner list counts are original UNARY record counts. The internal result remains the reversed unary-record representation already proved byte-compatible with the original constructor. Actual D_lambda, every admissible joining refinement, the independent target/certificate interface and all original finite source cases are unchanged.

New sources: PolytomyGuardedRowOuterLoop.lean, PolytomyOuterRowsObservation.lean and PolytomyFramedRowsParser.lean. These realize the complete rows section, with exact nested original grammar observation. They do NOT yet realize the three source headers, physical cap construction/switching or complete-input finish.

## 2. Correct failed-state invariant and guarded row body

The previous framed-row routine requires its inner counter empty at entry. Success clears it; failure can leave a suffix. Therefore an outer-loop invariant requiring unconditional inner emptiness would be false. The supplied RowOuterInv instead contains the numeric boundary invariant and the implication: if success is true, the inner counter is empty. Failed states retain bounded source/cap/clean numeric scratch but may retain inner-counter suffixes.

An ACTUAL branch guards the new row attempt. With incoming success false it only resets the owned cached guard and preserves every data stack; it never restarts parsing. With success true, the invariant supplies the required empty inner counter, the actual framed-row routine executes, and its successful-clear/failure alternatives preserve RowOuterInv. Its time is at most Row(L,C)+1, where the extra one is the real branch dispatch.

The record, inner counter and outer counter are three distinct ports. Source-level preservation proofs follow each numeric body, inner countdown, count-prefix update and row result to show that every other extra port and the finite caller frame F are unchanged. In particular the row body preserves the outer counter. This is proved, not assumed.

The inner and outer routines may share one cached nonemptiness bit. The inner routine can reset that bit. The actual outer code always re-peeks at its own counter after the row body, so no false cached-guard-preservation premise is needed. Both layers retain a finite control state; physical counters, not unbounded natural numbers, drive their loops.

## 3. Actual repeated-row loop and exact observation

The concrete guarded row body instantiates the actual outer CountdownContract. With initial outer counter length k, the routine costs at most k(Row(L,C)+4)+3: row body includes its branch, countdown adds pop/peek/dispatch, and the outer wrapper has initial peek/final dispatch/reset. The boundary invariant covers every failed partial state. Successful return clears both the outer counter and, by the invariant, the inner counter. Failure may leave either suffix for final cleanup.

The record grows by at most B(L,C)=L(C+2)+1 per row attempt. Induction through the actual counter semantics gives a boundary growth of at most k B(L,C), including early failure. This is a partial-state accounting proof, not an inference from successful final record length.

A separate read-and-log recursion parses original framed rows and prepends the reverse of each unary-encoded row. Induction identifies it with original readMany(row_reader), preserving the exact source suffix and reversed concatenated row log. A second induction relates this recursion to the actual outer store transformer. Observed row failure means the success flag is false and no further row attempt occurs. Observed success supplies the exact suffix/log and reserved-counter preservation supplies the smaller counter instance. This handles malformed input, empty rows, zero outer count and an already-failed incoming state.

The pure observation theorem is stated even on stores outside the operational invariant, but the actual execution theorem is explicitly joined only under RowOuterInv. No execution outside that invariant is inferred.

## 4. Reading the actual outer count and the complete two-level rows section

The complete framedRowsRoutine composes the already implemented original unary count-prefix/copy routine, now targeting the fresh outer counter, with the observed outer loop. Both inner and outer counters start empty. Distinct-port preservation leaves the inner counter empty after reading the outer prefix, establishing RowOuterInv. The physical outer count is at most the remaining source length L.

The resulting observation is EXACTLY:

readFramedList(readFramedList(readSaturatedBinaryNatFrame C))(source),

mapped on success to its untouched suffix and reverse(encodeFramedList(encodeFramedList U)(rows)) ++ previous_record. Successful readMany has exactly its requested number of rows, so the outer count frame already logged by the prefix is the correct one. Neither the declared binary dimension m nor an assumed valid-record row count substitutes for this actually read unary outer count.

With M(L,C)=6LC+8L+8C+14 and Row(L,C)=L(M(L,C)+3)+7L+11, the complete rows-component time bound is

Rows(L,C)=L(Row(L,C)+4)+7L+11.

All source suffix lengths remain at most the supplied outer bound L; the physical cap stays C and is not incorrectly shrunk with the suffix. The all-path boundary record-growth bound is

L^2(C+2)+2L+1.

This is deliberately coarse and remains compatible with the earlier sharper quadratic FINAL successful-source normal-form bound. It counts nested attempts conservatively and does not need successful final parsing. All unrelated extra ports and F are preserved, enabling later cap-cache integration.

## 5. Precise remaining whole-source obligations

The rows routine starts one new rows-section attempt. A complete source caller must skip it after a failed header. The three headers still need their exact original caps: L+1 for N and declaredM, and (L+1)^2 for K, followed by L+1 for row identifiers. Those caps must be physically constructed from the original input length and switched without losing caller data. No unbounded numeric control parameter or shrinking-cap assumption is permitted.

The remaining source suffix must be explicitly tested for emptiness. Final record reversal/tagging and cleanup must cover success and EVERY failed partial record/counter/source/cap state. Only then can this become a whole normalizer witness. The downstream validation/arithmetic/constructor and independent clade checker, compatible closed encoded source hardness and all authorized elaboration/kernel checks remain separate open obligations.

All dependencies remain uninstalled/unelaborated. Existing original stochastic biological-identification and general-DAG targets remain open. No full-source parser, whole constructor/checker, classical NP-completeness, kernel verification or historical-novelty claim is made.
