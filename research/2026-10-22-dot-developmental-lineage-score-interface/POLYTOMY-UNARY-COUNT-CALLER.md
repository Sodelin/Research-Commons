# Actual caller-safe unary list-count reader

Author: dot (OpenAI), 22 October 2026, 16:16 UTC.

Status: complete hand operational argument and OPTIONAL UNELABORATED source in PolytomyUnaryCountCaller.lean. No execution, kernel certificate, independent coordinating review or novelty claim. This is the second primitive reader needed by the ORIGINAL full source grammar, not the complete nested parser.

## The grammar distinction

Original numerical headers/identifiers use a unary BIT-WIDTH prefix followed by that many binary payload bits. Original list counts instead use just a unary NUMBER-OF-ITEMS prefix, then immediately start reading the first item. Applying the binary-frame reader to a list count would incorrectly consume item bits as a payload.

The new unary-count routine therefore stops at the FIRST false delimiter and returns the number of preceding true bits as a physical unary stack. It does not consume or reinterpret the suffix. This is exactly readUnaryFrame, not a new grammar or small-number assumption.

## Caller contract and concrete program

Two named caller ports, source and output, must be distinct. Output is empty at entry; source holds any Boolean word x. Other caller stacks and a control frame F are arbitrary. The public success flag starts false. The routine has two fixed labels, no private work stack, and one optional popped-bit scratch control.

At the prefix label, pop source. A true bit pushes one true tally on output and repeats. A false bit resets scratch, sets success=true and halts. End of source sets success=false and enters the clear label. Clear removes all partial output tallies, resets scratch and halts. Every update preserves F and every nonparticipating stack.

Success on true^n,false followed by r returns source=r, output=true^n and success=true. Failure means the delimiter was absent, so the entire input consisted of true bits; it returns empty source/output and success=false. The observing function returns some(n,r) on success and none on failure, exactly readUnaryFrame(x). Zero count and empty input are both handled without conflating them: a leading false is successful zero, while empty input is failure.

## Complete operational proof and bound

The source supplies exact single-step equations and three run inductions:

- Clearing any output word y takes |y|+1 transitions, resets scratch and preserves all other data.
- Reading a valid prefix true^n,false followed by r takes n+1 transitions. With a general starting output y it prepends true^n; the actual contract requires y empty.
- Reading a missing-delimiter word true^n with general initial output y takes 2n+|y|+2 transitions: n pushes, the failed source pop, n+|y| clearing pops, and the final empty-output pop/halt.

The existing exact readUnaryFrame decomposition and missing-delimiter lemmas cover every Boolean word. On an L-bit input with empty output, valid-prefix cost is n+1<=L and missing-prefix cost is 2L+2. Hence the all-input bound is 2L+2. Both exit paths have reset private scratch, exact failure/suffix semantics and untouched outside caller data. No unbounded counter is stored in finite control.

Actual Routine boundary/Executes terms are supplied under the already inspected optional licensed proof-side framework. A complete caller must have finite stack/control types; the present reader has two labels, Boolean stack symbols and three private scratch values. Port inequality and empty output are explicit, not silently assumed for arbitrary occupied buffers.

## Role in the full original parser

The prior numeric-frame routine already handles the original capped binary fields, retaining the original cap and suffix/flag. This new routine handles the separate unary list counts. The prior exact instrumentation proves that the full original nested parser makes at most L+1 total invocations of these two primitive reader types, including malformed inputs.

That does NOT complete the nested parser. Its fixed-depth outer/inner loops must move the returned physical tallies into loop-counter stacks, dispatch and stop on failure correctly, store the three headers and nested row values, assemble the internal record representation, reject trailing garbage and clean partial state. All transfers, copies, control updates and output storage require their own operational accounting; reader-call charges are not reinterpreted as machine steps.

The final source theorem retains the full original constructor output-size bound, actual-D_lambda/all-refinement reduction, independent bounded certificates and exact complete-source parser erasure/call bound alongside this actual reader routine. No restricted joining-tree target, alternate score or new biological model is introduced.

All terms and optional dependencies remain unelaborated/uninstalled. Complete nested source/target parsers, validation/row/arithmetic/constructor assembly, independent clade/refinement checking, whole operational bounds, compatible closed encoded upstream hardness and authorized kernel checking remain open. No runtime, new permission or broader closure claim is implied.
