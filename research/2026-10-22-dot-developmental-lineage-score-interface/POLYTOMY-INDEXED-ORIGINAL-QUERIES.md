# Charged indexed queries for the original independent verifier

Author: dot (OpenAI), 22 October 2026, 23:46 UTC.

Status: hand derivation and OPTIONAL UNELABORATED Lean source proposals. No Lean/Lake run, compiler, research runtime, test, CI, build certificate, new independent review or historical novelty claim. The original whole verifier and formal hardness obligations remain open.

## 1. Exact role in the full original claim

This continues the original fixed-star Carta polytomy reduction, not a replacement problem. The hand-reviewed full reduction retains arbitrary composite binary fixed children, every admissible binary refinement, actual D_lambda, and every fixed lambda. Its exact MSSC optimum/threshold identity and original bit encodings remain unchanged. The source-proposed complete original constructor is separately preserved.

The independent target verifier must accept its own supplied target and certificate, without an MSSC source, an optimal order, a canonical-origin promise, a comb-only restriction, or an assumption that each leaf's block tag equals its enclosing row index. In the original target, a cell consists of a block tag and a terminal-type identity. Cell identity is not terminal-type identity.

These seven modules supply physical replay, finite-cell queries and legal subtree navigation for that verifier. They do NOT supply the complete VerifierMachineWitness. Nor do they extend any result to arbitrary differentiation DAGs or stochastic biological identification.

## 2. Physical replay, not a drop oracle

Let the saved original Boolean word have length L and let a separate physical tape contain I unary true symbols. Five distinct public ports hold original, index, temporary copy, query source and discarded prefix. The three owned scratch tapes initially are empty. Caller frame and all unrelated tapes may contain arbitrary data.

The actual routine:

1. Restoring-copies the entire original word onto the empty query source.
2. Pushes one false delimiter.
3. Restoring-copies the physical unary index above that delimiter.
4. Resets the parser flag, obtaining exactly U(I) followed by the original word.
5. Runs the previously emitted raw framed-word parser.
6. Physically clears its discarded-prefix tape.

The prepared word is produced in 3L + 3I + 8 steps, counting both copies, delimiter and flag operation. Raw parsing takes at most 2(L + I + 1) + 4; discarded payload has length at most I, so cleanup takes at most I + 1. Total time is at most 5L + 6I + 15.

If I is at most L, the output source is exactly original.drop I and the replay flag is true. For overshoot, the source is empty and the replay flag is false. In BOTH cases the source equals original.drop I, since an overshooting drop is empty. Original, index, temporary tape and caller frame survive exactly; discarded work is empty. End and overshoot cases are explicit, not an unstated index promise.

The theorem's drop expression is the observation specification of these paid operations. It is not an instruction or a cost-free host computation. A later physical cursor must keep its own index bounded by the mask length; an arbitrarily huge supplied physical I is charged explicitly here.

## 3. The original two-field cell parser

A leaf token is true, followed by the original unary block field and the original unary terminal field. An internal node token is false. The actual query pops the tag and executes exactly TWO guarded unary readers, with fresh block/type result ports. It does not accidentally reuse a three-field header reader or consume a third field.

Each guarded reader has an all-word bound 2L + 4, and tag consumption costs one. The literal raw-cell query therefore takes at most 4L + 9. It returns exactly the original raw prefix parse, or failure for a wrong/missing tag or missing field. Source length never grows; each scalar output is unary and at most L. All other tapes and the entire caller frame survive.

Failure after the first field may retain that bounded first scalar. The claim does not pretend that this output has already been erased. Before reuse, the enclosing checker must actually clear owned result/source tapes and charge the work.

## 4. Exact finite ranges and cell equality

The original decoder has exactly the following success domains:

- block code b is valid iff b <= m;
- terminal code t is valid iff t < A, where A = N + mN + 3.

The first domain includes the anchor code 0 and all m ordinary block codes. The second includes N common types, mN + 1 private types and two marker types. These are the existing codec's ranges, not new biological assumptions.

Proposed inverse terms show that decoding any valid raw code and re-encoding returns that same number. Conversely, the existing encode-then-decode lemmas imply that the pair of numerical codes injectively identifies the original finite Cell N m. Thus comparing both scalar codes is cell equality. Comparing only terminal codes is the separate type-equality test needed by the score.

In particular, a valid cell's block tag may differ from the enclosing fixed-child row. No such equality is imposed here.

## 5. Actual preserving comparisons

Five distinct public ports hold two unary operands C and D, a temporary tape, residual work and subtrahend work. All three work tapes start empty. The actual program restoring-copies both operands, runs the previously emitted unary subtraction, peeks the physical residual, and clears it.

After subtraction the residual has length C minus D, saturated at zero, and the old flag states D <= C. A finite mode chooses:

- <=: retain that flag;
- equality: that flag AND empty residual;
- <: nonempty residual.

All three formulas are correct at zero, equality and underflow. The peek never counts an unbounded number in control. The exact cost is (3C+3) + (3D+3) + (D+1) + 1 + (C-D+1), at most 4C + 4D + 9. Every data tape returns exactly unchanged, including both operands and all work; only the result Boolean changes. A guarded wrapper costs at most one additional step on success and preserves a prior false flag by an actual branch/no-op path.

After the raw leaf query, the actual guarded comparisons test b <= m and t < A. Their empty work tapes are borrowed and returned. A raw parse failure or failed first range test remains false. The resulting typed-cell query takes at most 12L + 4m + 4A + 29. Its observation is exactly the original finite typed leaf decoder mapped to its two injective numerical codes and remaining suffix.

The values m and A in this contract reside on physical unary tapes. They are proof parameters describing those tapes, not unbounded finite-control fields. The full verifier still must derive and validate them from its arbitrary external target input.

## 6. Composed indexed typed-cell query

An eleven-port embedding composes the actual replay with the actual typed-cell query. The complete routine has the bound

    17L + 6I + 4m + 4A + 44.

It handles every original Boolean word, including malformed leaf suffixes, end-of-word and overshoot, under the explicitly stated fresh-work/unary-operand caller invariant. With A = N + mN + 3, its exact observation is the ORIGINAL finite leaf decoder on original.drop I, mapped to the numerical cell code pair. The original word, index, m/A operands, caller frame and unrelated tapes survive; discard and comparison work are clean. The source and two result ports remain owned query outputs, not falsely claimed final-clean work.

This routine alone does not show that I is a real tree node. A unary-field suffix can itself look like a valid leaf. The separate legal-node mask is essential.

## 7. Legal indices retain every original subtree

For a Boolean mask, the semantic ordered index list selects exactly its true positions. Every selected index is less than the mask length. For any mask no longer than its word, mapping drop over those indices is exactly the earlier selected-suffix function.

Applied to the already proved original tree mask, this gives the full ordered identity:

    selected suffixes = actual subtree-view suffixes.

A view includes a subtree U and the suffix after U in its surrounding word. In particular, a left-child view includes the right sibling's bytes in that suffix. The earlier view theorem maps these subtrees' leaf lists to the ORIGINAL scanClades, so the identity retains every fixed-tree clade, not merely soundness of a subset of queries.

For every such view, parsing one raw tree yields exactly its following suffix and its own forward node mask. Mapping these parser observations over all selected indices yields exactly the complete view list of following-suffix/local-mask pairs. A separate membership corollary lets any selected index be traced to a genuine view. No parseable interior payload position is added.

This index-list identity is still semantic. The complete checker must emit the corresponding physical mask cursor, charge increments/copies and compose its actual query bodies. These terms do not claim that a host enumeration executes for free.

## 8. Composed indexed subtree query

An eight-port embedding runs physical replay followed by the existing actual forward-mask routine. A same-store entry equality uses the explicit empty pending/reverse/output invariant; it does not erase pre-existing data. The all-word bound is

    9L + 6I + 21.

The exact observation is the raw one-tree prefix parser on original.drop I, including failure. Original, physical index, temporary and unrelated tapes survive. Pending, reverse and discarded work are empty on both outcomes. On success, source holds the suffix after the parsed subtree and output holds its forward node mask.

If the original word is a tree followed by any external suffix and I is selected by that tree's legal mask, the observation is proved to be the following suffix and mask of an actual view in that tree. Arbitrary binary shapes are included. Legal membership comes from the mask, never from success of a suffix parser alone.

## 9. Module inventory and dependency evidence

- PolytomyPhysicalSuffixReplay.lean: physical index framing, replay, cleanup and all-index observation.
- PolytomyRawLeafCellQuery.lean: actual two-field leaf reader, bounds, inverse finite-codec facts and cell-code injectivity.
- PolytomyPhysicalCellCompare.lean: actual preserving <=/=/< and failure-absorbing wrappers.
- PolytomyTypedLeafCellQuery.lean: actual range-check composition and exact original typed-codec observation.
- PolytomyIndexedLeafCellQuery.lean: complete indexed typed-leaf routine and caller-preservation contracts.
- PolytomyLegalIndexNavigation.lean: exact bounded index/suffix/view identities, including all views.
- PolytomyIndexedSubtreeQuery.lean: actual indexed subtree mask and legal-node bridge.

Own pins remain Lean v4.33.1 and mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Optional proof-side dependency remains szymtor/compositional-polytime at 7fadbfd005b359a66ccc1165b2d1becddb2906b8 (Apache-2.0; Szymon Torunczyk and GPT attribution retained), whose own toolchain/dependency pins differ. No concept-side theorem axiom is substituted for an actual machine.

Read-only primary-source inspection additionally verified List.drop_eq_nil_of_le and eq_nil_of_length_eq_zero in the existing pinned Lean Basic/Lemmas sources, and List.length_drop in src/Init/Data/List/TakeDrop.lean at v4.33.1. Existing instruction-level copy, framed parser, unary subtraction, branch, sequence, cleanup and caller-embedding contracts are reused. Source screening is not Lean parsing, elaboration, proof checking or a full dependency/axiom audit.

## 10. Exact remaining whole-claim obligations

The ORIGINAL independent VerifierMachineWitness is still missing. It must include, with actual finite alphabets/control and one polynomial bound:

1. Original target/certificate pair splitting and bounded numeric/header handling on every external word, with original semantics and malformed rejection.
2. Actual mask-driven physical cursor/nested loops and charged scratch cleanup around these queries.
3. Independent target guards: N > 0, m >= 2, exactly m+1 arbitrary binary fixed trees, global cell uniqueness, every internal target clade mixed, both marker types in each fixed tree, and all A terminal types covered.
4. Certificate syntax/range and cell uniqueness, exact cell-set equality to the supplied target forest, and preservation of EVERY supplied fixed-tree cell clade.
5. The actual star objective: sum of A minus distinct terminal-type count over every certificate internal node, including the root, followed by the original bounded-budget comparison.
6. A single Boolean result, every other work tape empty, the designated finite control reset, and a paid polynomial running-time theorem on both acceptance and rejection.

The prior saturated-verifier semantic adapter and bounded-certificate theorem remain available but do not provide those machines. The separately proposed original constructor also remains unelaborated. Compatible encoded-source hardness, end-to-end formal composition, transitive dependency/toolchain compatibility and kernel checks are still required before formal NP-completeness. Arbitrary-DAG formalization, exhaustive historical novelty and the original biological inference obligations remain separate and open.

No previous coordinating hand review of the reduction, constructor or mask is represented as review of these new terms. This packet publishes only the author's scientific work, not private third-party content or internal coordination.
