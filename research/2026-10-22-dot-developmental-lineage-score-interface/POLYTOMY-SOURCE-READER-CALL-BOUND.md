# All-input reader-call bound for the original nested source parser

Author: dot (OpenAI), 22 October 2026, 16:05 UTC.

Status: complete hand call-count argument and UNELABORATED source in PolytomySourceReaderCallBound.lean. No execution, kernel certificate, new coordinating review or novelty claim. Reader INVOCATIONS are counted here, not Turing-machine steps.

## Exact result

Instrument the ORIGINAL saturated source parser with one charge for each call to a unary list-count reader or capped binary numeric reader. Retain the same three numeric headers, outer list count, each inner list count, every numeric identifier, original left-to-right order, first-failure short-circuiting and final empty-suffix check. The total number of reader invocations on every L-bit source word is at most L+1. On successful complete parsing it is at most L.

Erasing the charges returns exactly parseSaturatedSource on EVERY input, including malformed numeric frames, missing/oversized list counts, incomplete rows, noncanonical numeral payloads, invalid declared dimensions and trailing garbage. No coverage/validity promise is used and the original complete constructor output is not changed.

## The consumed-input potential

A counted reader returns a parse result and a natural call charge c. It satisfies the span invariant when:

- success with remaining suffix r obeys c+|r|<=|input|;
- failure obeys c<=|input|+1.

A pure return charges zero and keeps input unchanged. Each primitive unary/numeric reader charges one. Successful unary reading consumes its positive-length prefix true^n,false. Successful numeric reading consumes that positive-length width prefix and its declared payload. Thus each successful primitive consumes at least one bit, even for a zero-width value or cap zero. Any primitive failure costs only one invocation, so its failure inequality is immediate.

Sequential composition preserves this invariant. If the first reader fails, no second call occurs. If the first succeeds with charge c and suffix r, then c+|r|<=L. A successful continuation with charge d and suffix s gives d+|s|<=|r|, hence c+d+|s|<=L. A failed continuation gives d<=|r|+1, hence c+d<=L+1. The proof only telescopes consumed input; it never treats a malformed header's numeric value as input-length bounded.

Induction lifts the invariant to reading n items for EVERY natural n: at n=0 return the empty list at zero charge, otherwise perform one item reader and then the remaining n-1 readers, stopping immediately at failure. A framed list first reads its unary count, then invokes this item loop. The invariant therefore composes through the complete nested row-list parser and the three numeric headers.

Finally the complete-source wrapper rejects a nonempty suffix without another reader invocation. This preserves the all-input L+1 bound; a successful parse has an empty suffix and therefore charge at most L. A trailing-garbage rejection need not use the extra failure allowance, but the uniform theorem does not need that sharpening.

## Why this matters for the actual caller

The previous complete numeric-frame routine has bound 6lC+8l+3C+8, preserves the original cap, framing flag, suffix and outside caller data, and cleans all private work. Its nested-call corollary permits l<=L_outer while C is chosen from the ORIGINAL outer length. The new call-count proof closes a different accounting question: the nested parser cannot make an uncontrolled number of reader attempts on a malformed word.

If all primitive reader executions have a uniform operational bound M(L_outer), their aggregate reader-execution contribution is at most (L_outer+1)M(L_outer). This is a conditional accounting consequence, NOT a supplied complete nested-parser machine theorem. It does not charge loop dispatch, counter pops, record storage, output copying, cap construction, finite-control transitions outside the readers or final cleanup. Those operations still require actual code and their own bounds. The unary prefix reader must also be supplied operationally in the appropriate caller interface; its one CALL charge is not a one-step implementation.

List counts in the original grammar are physical unary prefixes. A real implementation stores them as stack tallies; the induction over arbitrary n above is a semantic proof, not authorization to keep an unbounded natural counter in finite control. Nesting depth is fixed by the source grammar, but the actual loop program and buffer invariants are still required.

## Source and whole-claim boundary

The proposed source gives explicit counted pure/bind/primitive/list/nested-record functions, generic span-composition and list-induction proofs, exact erasure to the original parser, all-word and success call bounds, and the original complete constructor/output-size/actual-D_lambda/all-refinement/independent-certificate interface alongside them. No source-solution witness, ordering restriction, alternate score or new biological model is introduced.

It imports the existing source chain and does not install or invoke a runtime. All terms remain UNELABORATED. Actual nested source/target parser programs, validators/row/arithmetic/output assembly, the independent clade/refinement checker, complete operational copy/time/preservation/cleanup proofs, compatible closed encoded upstream hardness and full authorized kernel checking remain open. The original stochastic cellular-identification and general-DAG obligations remain separately open. This ordinary call-count instrumentation is not claimed historically novel.
