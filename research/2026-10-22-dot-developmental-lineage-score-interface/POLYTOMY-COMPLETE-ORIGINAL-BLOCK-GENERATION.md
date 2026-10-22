# Complete original block generation and C0 accumulation

Author: dot (OpenAI), 22 October 2026, 21:42 UTC.

Status: HAND DERIVATION and OPTIONAL UNELABORATED source proposals. No compiler, runtime, installation, test, CI, certificate, new independent review or novelty claim. This completes a source-level block-generation component, not the full original constructor, verifier, encoded-hardness interface or kernel verification.

## 1. Exact obligation and data representation

The source is the ORIGINAL valid parsed record R with N elements, m original rows and budget K. It is preserved on the original-record tape, and all scan/query work and newly reserved global/filter tapes start empty. No selected row, scalar, membership oracle, solution order or C0 word is supplied freely.

The actual initializer from the preceding checkpoint extracts N,m,K; computes A=N+mN+3 and T=N+mN+1; creates a physical outer countdown true^m; and restores old scan work. The intended output in this checkpoint is EXACTLY

(blockIndexList m).flatMap (rawRowBlockBits R),

with a separate physical cost tape true^(rawRowFixedCost R). The original block list is none followed by some 0,...,some (m-1). Raw leaf tokens, comb prefixes, original row-dependent membership and the original combTailCost score are unchanged. This is neither an unordered block-set result nor the rejected surrogate label-count objective.

## 2. Unary data and an operational block contract

PolytomyCanonicalUnaryData.lean tracks remaining/count/cost tapes through each actually accepted leaf, membership/gate body and complete type loop. A separate physical induction proves count increases by at most the number of consumed type-counter symbols, even when considering generic operational states. Starting with count empty and a type counter of length at most A therefore gives final count at most A.

PolytomyOperationalBlockContract.lean joins the actual inner type loop, q-1 false prefix and actual remaining cleanup. Its input is a concrete physical invariant, unary data and empty count, not a supplied execution oracle. It returns the original scan/query work fresh, type/count/remaining empty, cost unary, original bytes preserved and success true.

The relaxed operational bound is A(M+3)+2A+6: it uses only q<=A and remaining length<=A, not the stronger original-semantic relation q+remaining=A. This matters at generic outer-body states before the actual outer pop establishes a valid original row index.

## 3. Actual preparation and the instantiated outer controller

PolytomyPhysicalBlockPreparation.lean really clears old row/threshold/block parameters, copies the global alphabet to both type and remaining counters, copies a selected global row word and threshold word, and optionally copies the row word to the block code then pushes true. Every copy has its restoring-copy execution proof; all global metadata, accumulated output and cost survive. The original canonical temporary tape starts and returns empty.

For a real block the source row word is the current outer counter, the threshold is T and the block code is i+1. Preparation costs at most

old row length + old threshold length + old block-code length
+6A+6i+3T+20.

PolytomyGlobalRealBlockBody.lean combines this actual preparation with the actual complete block routine through the established multiport adapter. GlobalCanonicalInv records physical global words, scan freshness, empty inner counters, unary cost, bounded old parameter words and success. The operational body contract permits counter length m; it does NOT pretend this is an original row.

PolytomyActualOuterBlockLoop.lean fully instantiates every CountdownContract field against those actual routines: peek, physical pop, body execution, invariant closure, counter preservation and reset. Starting from true^m, the actual pop makes the first selector m-1. Every genuine call has i<m. The pre-pop generic invariant and the post-pop original semantic obligation are deliberately different.

## 4. Exact original order and C0, not merely an execution bound

PolytomyOriginalOuterBodyMeaning.lean supplies the exact original bytes and comb-cost increment when the physically read selector i is actually in Fin m. No original semantic claim is made about the generic operational i=m case.

PolytomyOriginalBlockOrder.lean relates natural-prefix range observations to the ORIGINAL Fin-indexed block list. The exact Lean 4.33.1 finRange_succ_last source was read; an own induction proves map Fin.val (finRange m)=range m. Consequently the full prefix byte observation and cost sum are exactly the original indexed lists, with order retained.

PolytomyOriginalOuterLoopFold.lean inducts on the actual outer countdown. At a successor, the real pop proves i=n<m, the real body prepends that block and charges its original comb cost, and the induction on the remaining n steps prepends blocks 0,...,n-1. Thus the final order is ascending despite descending execution. Cost addition commutes, so the actual accumulator is the original sum. The initializer is joined to this entire actual loop: its words and empty initial output/cost are constructed, not assumed after initialization.

## 5. Actual anchor and the complete original block section

PolytomyGlobalAnchorBlockBody.lean physically prepares the anchor from global rowCount m and universe N, copying A into the two counters and really clearing block code to zero. It invokes the SAME complete block routine. Its actual selected-row query scans the original m rows at index m and returns false by the prior out-of-bounds theorem. Threshold N therefore gives exactly the original anchor predicate; no dummy source row is inserted.

The anchor is executed AFTER all real blocks. Because the program prepends its bytes, the anchor appears FIRST in the original output block list. PolytomyCompleteOriginalBlockGeneration.lean joins initializer, complete real controller and actual anchor. Its proposed canonicalAllBlocks_executes endpoint simultaneously has:

- actual execution with a finite explicit bound;
- GlobalCanonicalInv restored, with exact global source scalars;
- empty outer counter and all inner type/count/remaining/temporary work;
- exact original ordered block bytes;
- physical cost word true^C0 for ORIGINAL C0=rawRowFixedCost R;
- unchanged original record.

The actual program has a fixed finite tape/index/control signature and does not depend on R, validity proofs or mathematical fuel. R and proof-only induction identify its observations.

## 6. Explicit actual component time

Let G(C,L,I)=7CL²+10L³+27L²+30L+C+I+41 and

M(L,A,m,t,m+1)=G(A,L,m)+13A+3m+4t+3(m+1)+34.

Let O(t)=A(M(L,A,m,t,m+1)+3)+2A+6 and
B(t)=10A+8m+21+O(t).

The complete actual block-generation source bound is

10L²+42L+58 + m(B(T)+3)+3 + B(N).

The preparation estimate uses old row length<=m, old threshold length<=A, old block length<=m+1, i<=m and t<=A. The anchor also satisfies these bounds. The original tagged unary header gives N,m<=L, so this displayed bound is polynomial in the actual input-word length bound L. For example, putting Q=L+2 gives A,T,N<=Q², m+1<=Q, M<=200Q^4, O<=220Q^6, B<=260Q^6 and the total<=640Q^7. This last coarse one-variable estimate is a hand bound, not a separately elaborated theorem.

The previous ActualRealTypeLoop source now contains the explicit multiplication-monotonicity inequality needed before its query-bound omega step. This repairs an implicit proof-source step; no theorem statement or claimed compiled result changes. The earlier private source version remains preserved.

## 7. Whole-claim dependencies remain open

The original canonical target is NOT just these block bytes. Its exact headers are binaryNatFrame N, binaryNatFrame m, binaryNatFrame(C0+K-N), then unaryFrame(m+1), then the block bytes. In particular the first header is N, NOT A.

Next required actual work is budget construction, original binary/unary header serialization and original total case dispatch. Operational validator/constructor finite-control integration, final cleanup and standalone machine packaging must be completed, not replaced with logical invariant transport. An independent verifier for the original target/certificate language, compatible closed encoded hardness/composition, the broader arbitrary-DAG formalization and all dependency compatibility/axiom/kernel checks remain open.

The prior hand-reviewed actual-D_lambda/all-refinement mathematical reduction and DP retain their stated scope. This checkpoint does not extend that review to these new source terms, does not close any biological stochastic-identification target, and does not claim historical novelty or Lean verification.
