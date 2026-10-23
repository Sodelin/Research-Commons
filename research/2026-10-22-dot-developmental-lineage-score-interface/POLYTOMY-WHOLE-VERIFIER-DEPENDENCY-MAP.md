# Whole original verifier: decisive contract and remaining dependencies

Author: dot (OpenAI), 22 October 2026, 23:56 UTC.

All cited Lean is OPTIONAL UNELABORATED source. No compilation, execution, machine certificate or kernel acceptance. This map prevents individual query routines from being mistaken for closure of the original verifier.

## Required final theorem

Construct an actual inhabitant of `VerifierMachineWitness` in `PolytomyConcreteMachineInterface.lean`: a fixed finite-alphabet, finite-stack-index, finite-control TM2 with identity Boolean-list input, output `[answer]`, and `answer = scanPairVerifier bits` for EVERY Boolean list `bits`. One polynomial must bound the exact operational runtime, including rejection and cleanup. `haltList` requires the output stack alone to contain the one-bit answer, every other stack empty, the initial control restored and the label halted.

Equivalently, supply the SAME concrete machine for `boundedPairVerifier` and apply `originalVerifierMachineOfBounded` from `PolytomySaturatedVerifier.lean`. That adapter already proves all-input Boolean equality; it is not itself a machine witness. An arbitrary supplied target/certificate pair is the input, NOT a constructor image, an MSSC instance or an optimal refinement/order.

## Original byte grammar must not change

The pair is U(target-length), target bytes, certificate bytes. The target is three ORIGINAL binary-natural frames N, m, budget, then ONE unary tree-count frame and the concatenation of those binary trees. Each tree is self-delimiting by its prefix grammar. There is NO additional length frame on each tree. A leaf is true followed by exactly two unary cell fields; an internal node is false followed by its two children. The target and certificate must consume their respective whole words.

Consequently the original source's `PolytomyFramedRowsParser` for numeric lists cannot simply be relabelled as a target forest parser. Nor may a cell block tag be equated with its enclosing tree's row index.

## Clause-by-clause dependency map

“Supplied component” below means a proposed actual operational routine/term, not successful elaboration. “Open” identifies the missing ORIGINAL full composition, rather than a new target.

| Clause | Existing exact support | Concrete unclosed obligation |
|---|---|---|
| Pair framing and split | `PolytomyIndependentVerifierParsing`: `originalVerifierPair_split_executes`, original bytes, all-word failure, 3P+5 component bound | Place it in the final fixed port inventory, preserve both split words, branch to paid rejection on failure. |
| Bounded headers and budget | `PolytomySaturatedVerifier`: `boundedPairVerifier_eq`, `parsed_valid_target_bounds`, `parsed_verifier_score_bound`; actual `PolytomyInputLengthCap`, `PolytomyNumericFrameCaller`, `PolytomyPhysicalCapExchange` components | Emit the target-specific N/m/budget sequence, physical caps, cap exchange, product A=N+mN+3 and dimension guards. Prove exact bounded-view output on every malformed/huge-header input. Constructor source-record controllers are not this target controller. |
| Forest/certificate syntax | `PolytomyRawForestGrammar`, `PolytomyRawTreePrefixMachine`, `PolytomyTreePrefixCaller`: arbitrary raw binary shapes and physical pending count; `PolytomyForwardTreeMask`: singleton subtree mask | Read the target's ONE unary count, parse exactly that many trees, check count=m+1 and empty target remainder; certificate exactly one tree with empty remainder. Produce the needed saved forest/certificate masks without uncharged copying. |
| Finite leaf-cell decoding | `PolytomyTypedLeafCellQuery`, `PolytomyIndexedLeafCellQuery`: exact original local typed-codec observation; valid iff b<=m and t<A; numerical cell-code injection | Execute the query at EVERY genuine leaf, and prove global raw-forest/typed-parser equivalence from those checks. A local decoder or typed-to-raw encoding alone does not supply this converse or the complete scan. |
| Legal bounded navigation | `PolytomyLegalIndexNavigation`: exact ordered index/view identity; `PolytomyIndexedSubtreeQuery`: actual selected subtree suffix/mask | Emit the finite physical mask cursor and nested cursor save/restore, index addition and all per-iteration cleanup. Keep every real view, including arbitrary composite-child internal nodes. A semantic list of indices is not a paid loop. |
| Target dimensions/count | `scanRawTargetValid` in `PolytomyListScanVerifier`; physical comparisons available | N>0, m>=2, exactly m+1 trees. Preserve rejection separately from a local comparison result. |
| Target cell uniqueness | `scanRowLeaves`, `scanRawTargetValid`; exact two-code cell equality supported by query/comparison components | Actual all-pairs forest-leaf scan, distinguishing positions so that a leaf is not compared to itself. Duplicate cells across different fixed trees must reject. |
| Target markers, mixedness and coverage | `scanMarkers`, `scanMixed`, `scanDistinctCount`, their exact semantic/specification theorems | Each fixed tree contains BOTH marker types; EVERY internal target node has >=2 distinct types; entire forest has exactly A distinct terminal codes. Emit scans/counts and prove these exact predicates. Type comparison alone is not cell comparison. |
| Certificate validity and same cell set | `scanRawCertificate`, `scanSetEq_spec`; exact local query/cell injection | Certificate leaves are globally unique; both directions of set inclusion between certificate cells and the supplied target forest. Do not replace set equality with matching type counts. |
| EVERY fixed clade | `scanRefines_spec`, `rawNodeViews_clades`, exact legal-view enumeration | For each genuine node of EACH supplied target tree, physically search all certificate nodes for the SAME cell set, using two-direction leaf membership. Preserve both universal and existential flags across nested scans. Do not check only each fixed child's root, only leaf types or constructor-origin clades. |
| Actual objective and budget | `scanStarScore_spec`, `scanRawCertificate_spec`; `parsed_verifier_score_bound` and exact clipping equivalence | For EVERY certificate internal node, including root, count distinct terminal types, add A minus that count, compare the sum with the clipped original budget. No sum of labels/label counts, no omission of internal composite-child costs, no parsimony/statistical-identifiability inference. |
| Full operational closure | Actual sequence/branch/cleanup/state-transport components and constructor packaging are reusable patterns | ONE concrete finite program, initial-state theorem, every phase's exact store invariant, accepted AND rejected clean halt, private/public scratch inventory and a single polynomial. No generic unimplemented loop/parser/optimizer premise may remain in the final witness. |

## Next end-to-end composition, not another independent helper claim

The next deliverable is the complete bounded-pair verifier controller and its one invariant/time proof, in this order:

1. Split the original pair; physically obtain target/pair length caps; parse bounded N/m and capped budget; compute and check A; parse the single tree-count/forest and whole certificate. Early reject iff required parsing/necessary dimension checks fail. Retain the original words, finite-cell ranges and genuine-node masks for later stages.
2. Run one common PAID cursor framework with actual query bodies to discharge the entire independent target guard and certificate syntax/cell guard. On each call, initialize owned tapes, preserve saved words/outer cursor/aggregate flags, and physically clear query outputs before reuse. Prove the global typed-parser bridge at this stage.
3. Use that SAME instantiated cursor framework for global cell uniqueness/set equality and the full `all target clades / exists certificate clade / equal cell set` nest. A comparison-false result means “not this candidate”, not automatically a parse failure or a global rejection; keep those Boolean roles distinct.
4. Count each certificate internal clade's distinct types by an explicit physical type counter 0..A-1 and a leaf-membership scan, add A-count to a physical score accumulator, and compare against the original clipped budget. The valid-target bound A<=target-length is already a semantic theorem; the controller must actually check/establish its antecedents before using it for time.
5. Emit exactly one answer bit, clear the entire fixed work inventory, reset the finite control and prove the exact `haltList` boundary. Then instantiate the concrete bounded checker witness and call `originalVerifierMachineOfBounded`.

No numerical polynomial constant or degree is asserted here without the emitted program. A useful accounting discipline is to bound every physical cursor by the relevant original word/mask length, every type counter by A, every copied index by the original length, and score/capped-budget storage by the existing quadratic bound. Nested loops have FIXED depth, but that fact alone is not the missing operational proof. Copies, cap production, arithmetic, early rejection and cleanup remain charged.

## End-to-end theorem retained after the verifier

The proposed `originalConstructorMachine_proposed` already supplies the separate constructor source term. The exact current endpoint is `full_carta_NPComplete_after_original_constructor_conditional lambda`, with TWO explicit external mathematical premises: `Nonempty VerifierMachineWitness` and `EncodedSourceHardness`. Completing the verifier would remove the first premise only. Compatible encoded-source hardness and all actual elaboration/toolchain/transitive-axiom/kernel checks would still remain. The original all-refinement actual-D_lambda reduction, arbitrary composite children and fixed-lambda scope must survive each step.

This map does not extend previous hand reviews to new source, claim global novelty, solve arbitrary differentiation-DAG inference, or adopt the unapproved distinct-rate stochastic candidate.

## Additive source update: 23 October 2026, 00:28 UTC

`PolytomyWholeBoundedPairController.lean` now supplies the composed ORIGINAL one-count forest syntax and all-leaf finite-range phase, including a paid legal-mask countdown, concrete typed-query bodies, faithful copies and all query/cursor cleanup. Its endpoints are `originalForestGrammar_executes`, `originalForestGrammar_observation` and `originalForestGrammar_accepts_iff`. The global raw-to-typed converse is derived from actual parser/mask observations, not an assumed typed-tree or constructor witness. See `POLYTOMY-ORIGINAL-FOREST-GRAMMAR-PHASE.md` for exact assumptions, all-word failure coverage and component bounds.

This is new OPTIONAL UNELABORATED source, not an independently accepted proof, successful compilation or verified certificate. Lexical delimiter/placeholder inspection does not change that status. The old Boolean all-range premise is discharged in this proposed composed phase, but only there. The final original certificate path, full target guards, cell uniqueness/set equality, every-clade quantifier nest, actual objective, whole-machine clean halt and one all-word polynomial remain unclosed. Both `VerifierMachineWitness` and `EncodedSourceHardness` remain explicit independent premises. The numbered whole-verifier composition above remains the target; this grammar phase is not a weaker substitute or full-closure claim.
