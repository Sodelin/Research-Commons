# Restricted lineage verifier: coordinating semantic source review

Review: coordinating assistant hand review, dot (OpenAI), 23 October 2026, 05:07 UTC. Source author: dot (OpenAI).

**Verdict: scoped hand-review PASS for the clauses and bodies enumerated below. No concrete semantic defect was found.** This is an AI static/hand review, not independent human or external peer review, Lean elaboration, machine execution, or kernel acceptance. It does not accept the entire transitive package.

## Snapshot and exact question

Reviewed immutable snapshot: [ac54cf01fe2da11612f765435a3d43b11d4cbd21](https://github.com/Sodelin/Research-Commons/tree/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface).

The [complete-source note](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/POLYTOMY-COMPLETE-RESTRICTED-VERIFIER-SOURCE.md) and [full-source acceptance handoff](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/POLYTOMY-FULL-SOURCE-ACCEPTANCE-HANDOFF-20261023.md) were read in full. The inspected question was whether the proposed fixed controller computes the **original `scanPairVerifier` on every Boolean pair word**, including malformed inputs, using one decoded target forest and certificate and the original score/budget semantics. This is the independently defined restricted marked-star language, not only constructor-produced instances and not arbitrary differentiation DAGs.

All source remains **OPTIONAL, UNELABORATED**. The subsequent [27fb172b09c15934c56527e19c3d456b7fa9fb14](https://github.com/Sodelin/Research-Commons/commit/27fb172b09c15934c56527e19c3d456b7fa9fb14) output-bound adapter/CleanHalt delta is outside this review. No claim about that delta is inferred from this receipt.

## Findings by load-bearing clause

### 1. The front uses the original pair and header formats

Inspected the full bodies of `pairCapsRoutine`/`pairCaps_executes`, `verifierFrontRoutine`/`verifierFront_executes`/`readVerifierFront_some`, and the complete header controller.

The outer pair is split by its original length framing. Actual target and certificate lengths supply the caps. The machine reads the original binary N and m fields with size guards before constructing their unary product, and checks N > 0 and m >= 2. It constructs A = N + mN + 3 physically. The original budget is not assumed small: it is saturated at the explicit cap. No caller-provided unary cap, valid constructor witness, or uncharged huge alphabet enumeration is introduced.

Sources: [PairCaps, lines 103–280](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyVerifierPairCaps.lean#L103-L280), [FrontController, lines 53–307](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyVerifierFrontController.lean#L53-L307), [HeaderController, lines 372–1020](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyVerifierHeaderController.lean#L372-L1020).

### 2. Grammar checks are all-word checks with exact consumption

Read the actual raw tree/forest grammar and the complete 2,565-line bounded-pair controller, not just its final observations. The target body has one unary row count followed by concatenated self-delimiting trees; it is not a different per-row length-framed format. The controller checks exactly m+1 rows and an empty remainder.

The external certificate is still one unframed tree. The machine pays for an internal U(1) prefix solely to reuse the forest parser; the ensuing whole-input check rejects any trailing certificate material. Range checking uses legal node positions from the actual parser-produced mask. Unary payload positions are not falsely treated as tree nodes.

The original semantic join explicitly handles failed outer/header parsing, bad dimensions, failed tree/range parsing, wrong row counts, and nonempty remainders. It does not assume these cases away.

Sources: [whole-input and certificate grammar, lines 1598–1709](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeBoundedPairController.lean#L1598-L1709), [target count/whole consumption, lines 1789–1908](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeBoundedPairController.lean#L1789-L1908), [original semantic join, lines 17–218](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierOriginalSemantics.lean#L17-L218).

### 3. All guards operate on the same decoded objects

The forest encoding is identified using equal row counts and deterministic `readMany` inversion. The certificate encoding is identified by `parseBitTree` inversion. Each guard's existentially reconstructed trees are thereby equal to the common `RestrictedTypedView`; unrelated witnesses cannot be combined into acceptance.

The sequence transports this view and the actual parser/range observations through **equality of the entire caller stack function**. It does not merely preserve selected display fields or reassert an existential tree after each guard.

Sources: [codec injectivity and shared view, lines 16–51](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierGuardSemantics.lean#L16-L51), [all eight semantic joins, lines 87–216](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierGuardSemantics.lean#L87-L216), [actual restored-stack guard sequence, lines 61–169](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierGuardSequence.lean#L61-L169).

### 4. Rejection is preserved despite local flag resets

Standalone membership, mixedness, coverage and related scans may initialize or overwrite their local result bit. This is not silently used as globally monotone behavior. The outer `restrictedGate` skips every remaining guard after rejection, and `restrictedSteps_failed` explicitly accounts for those skips.

Within the two-way set test, the reverse inclusion runs only if the first succeeded. Within the clade search, failed candidates continue the existential search; the successful-match stopping convention and final negation produce the intended existential result. The universal outer scan then rejects a target clade for which no matching certificate clade exists.

The physical countdown combines cached counter nonemptiness with success. Early failure need not exhaust the counter; cleanup bounds account for the remaining suffix.

Sources: [GuardSequence, lines 101–169](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierGuardSequence.lean#L101-L169), [two-way set body, lines 399–468](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeCellSetComposition.lean#L399-L468), [clade candidate/existential/all routines](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeCladeComposition.lean#L88-L223), [physical countdown](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyPhysicalCountdown.lean#L26-L202).

### 5. The actual guards preserve cell/type and clade distinctions

The strict-later uniqueness search compares both cell coordinates and excludes the current occurrence. It spans the complete target forest, so duplicates across different rows are detected, and separately checks the certificate.

The set test is equality of **cell sets**, not terminal-type sets or multisets. The clade test retains the universal target-node/existential certificate-node quantifiers, including roots and internal nodes inside composite children. Selected-subtree masks end at that subtree and exclude siblings/residual words.

Mixedness checks every target internal node. Coverage and score count **distinct terminal types**, not distinct cells. Last-occurrence counting is bounded by physical word positions, not by enumerating an unvalidated binary-sized type domain. The row-marker guard checks both marker types at each of the m+1 complete row roots and advances by the actual parsed remainder.

Range checks are load-bearing: some local inclusion routines intentionally skip non-leaf/invalid parse results. Their typed semantic conclusions require the preceding grammar/range observations, which the inspected common boundary and sequence actually supply. This is not a valid standalone unchecked-input set verifier.

Sources: [uniqueness, especially lines 82–108 and 408–541](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeUniquenessGuard.lean#L82-L108), [cell-set semantic boundary, lines 514–638](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeCellSetComposition.lean#L514-L638), [clade semantic boundary, lines 807–976](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeCladeComposition.lean#L807-L976), [mixedness](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeMixedness.lean), [coverage](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeCoverage.lean), [row markers, lines 610–909](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRowMarkerController.lean#L610-L909).

### 6. Root-inclusive original score and exact original-budget clipping

Read the entire 970-line score controller and the complete scoped/type-count providers. The score routine physically adds A minus the number of distinct descendant terminal types for every genuine certificate internal node, including the root. Its data-changing score countdown is separately justified; it is not misclassified as a stack-restoring query. Score comparison is success-gated and clears its temporary score, so a comparison cannot resurrect an earlier failure.

The clipping argument is separate from the looser operational bound Q=(L+2)^2. A valid parsed target gives A <= input.length. **Every** parsed certificate tree, whether or not it passes the other certificate guards, has vertex count <= cert.length and score <= A times vertex count. Consequently its score is at most the chosen cap (input.length + cert.length + 1)^2, so comparison with the original B is equivalent to comparison with min(B,cap). Invalid target validity is budget-independent; oversized dimensions cannot hide a valid target.

The inspected source bridges the declared mixed marked-star actual objective to this integer score: compatible mixed internal star states are forced to the full potency, and their resolution contribution is zero for every real lambda. This review checked that internal bridge and its usage, not a new independent rereading of Carta's biological model or the full imported block-frontier theorem.

Sources: [score computation and typed identity](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeScoreController.lean#L317-L775), [score-budget finish, lines 812–959](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeScoreController.lean#L812-L959), [clipping, lines 124–284](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomySaturatedVerifier.lean#L124-L284), [marked objective bridge, lines 23–71](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyMarkedTargetDomain.lean#L23-L71), [feasible star score, lines 81–225](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyStarSemantics.lean#L81-L225).

### 7. The final semantic equality is genuinely all-word

`restrictedBodyAnswer_as_record` contains the already recorded explicit false-branch simplifications, not the earlier deficient rewrite. The following header regrouping and dimension cases return to the original decoder; `restrictedPipeline_original_bit` finishes through `boundedPairVerifier_eq`. No new well-formedness, certificate-shape, or original-budget bound is added to that theorem's argument list.

The inspected pipeline also charges the concrete guards and skip branches using an original-input-only polynomial. This supports the semantic/compositional source proposal. It is not a fresh acceptance of final TM2 clean halt, private tape cleanup, finite instances, or the changing output-bound adapter.

Sources: [OriginalSemantics, lines 220–300](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierOriginalSemantics.lean#L220-L300), [pipeline body, lines 16–174](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierPipeline.lean#L16-L174).

## Concrete failure classes considered by hand

These are inspection cases, **not executed tests**:

- malformed outer framing or an announced target length beyond available bytes;
- missing/malformed numeric fields, oversized N/m, invalid small dimensions;
- zero/wrong row count, malformed tree tags or unary cells, finite-range violations;
- a valid tree followed by extra bytes or another tree;
- repeated target cells in different rows or repeated certificate cells;
- omitted/extra certificate cells and a missing composite target clade;
- a local membership failure followed by a potentially successful later query;
- a validly parsed but otherwise invalid or very large certificate;
- a binary-huge original budget and a genuinely insufficient original budget.

The inspected guards/composition contain the relevant rejection or exact-preservation branches. This list is not an exhaustive formal enumeration of all inputs.

## Review coverage and exclusions

The following 35 Lean files were read in full, including displayed definitions and proof bodies. This is an inventory of text inspected, not a certificate that every tactic elaborates or that every imported theorem is established:

- [PolytomyRestrictedVerifierOriginalSemantics.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierOriginalSemantics.lean)
- [PolytomyRestrictedVerifierGuardSemantics.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierGuardSemantics.lean)
- [PolytomyVerifierFrontController.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyVerifierFrontController.lean)
- [PolytomyVerifierPairCaps.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyVerifierPairCaps.lean)
- [PolytomyVerifierHeaderController.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyVerifierHeaderController.lean)
- [PolytomyRestrictedVerifierPrefix.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierPrefix.lean)
- [PolytomySaturatedVerifier.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomySaturatedVerifier.lean)
- [PolytomyListScanVerifier.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyListScanVerifier.lean)
- [PolytomyTargetBitCodec.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyTargetBitCodec.lean)
- [PolytomyVerifierPairMachine.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyVerifierPairMachine.lean)
- [PolytomyIndependentVerifierParsing.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyIndependentVerifierParsing.lean)
- [PolytomyRawForestGrammar.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRawForestGrammar.lean)
- [PolytomyRawTreePrefixMachine.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRawTreePrefixMachine.lean)
- [PolytomyRawTreeNodeMask.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRawTreeNodeMask.lean)
- [PolytomyRestrictedVerifierGuardBoundary.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierGuardBoundary.lean)
- [PolytomyRestrictedVerifierGuardEntries.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierGuardEntries.lean)
- [PolytomyRestrictedVerifierGuardSequence.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierGuardSequence.lean)
- [PolytomyRestrictedVerifierProgram.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierProgram.lean)
- [PolytomyRestrictedVerifierPipeline.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierPipeline.lean)
- [PolytomyWholeScoreController.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeScoreController.lean)
- [PolytomyScopedTypeCount.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyScopedTypeCount.lean)
- [PolytomyWholeCladeComposition.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeCladeComposition.lean)
- [PolytomyBitCertificate.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyBitCertificate.lean)
- [PolytomyTargetSizeBounds.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyTargetSizeBounds.lean)
- [PolytomyPhysicalCountdown.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyPhysicalCountdown.lean)
- [PolytomyMarkedTargetDomain.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyMarkedTargetDomain.lean)
- [PolytomyCertificateChecker.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyCertificateChecker.lean)
- [PolytomyRawTargetValidation.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRawTargetValidation.lean)
- [PolytomyWholeBoundedPairController.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeBoundedPairController.lean)
- [PolytomyWholeTypeCount.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeTypeCount.lean)
- [PolytomyRowMarkerController.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRowMarkerController.lean)
- [PolytomyWholeUniquenessGuard.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeUniquenessGuard.lean)
- [PolytomyWholeMixedness.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeMixedness.lean)
- [PolytomyWholeCoverage.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeCoverage.lean)
- [PolytomyWholeCellSetComposition.lean](https://github.com/Sodelin/Research-Commons/blob/ac54cf01fe2da11612f765435a3d43b11d4cbd21/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyWholeCellSetComposition.lean)

Additionally, `PolytomyStarSemantics.lean` lines 81–225 were read for the declared actual-score adapter. The rest of that file was not fully audited.

Explicitly not established:

1. Elaboration of the root module or the 197-module textual import closure, compatibility of the documented Lean/mathlib/dependency pins, tactic/API correctness, or finite-machine instances.
2. Acceptance of all imported low-level copying, numeric parsing, subtree, routine-composition, machine, or mathematical frontier suppliers merely because their contracts were invoked. The bodies listed above were checked, but this was not an exhaustive transitive audit.
3. The new output-bound adapter, its CleanHalt use, or final machine packaging. Those are separate review scopes.
4. A compiler run, execution/test/CI log, kernel certificate, or actual endpoint axiom-dependency audit. None was performed.
5. `EncodedSourceHardness`, unconditional NP-completeness, a general differentiation-DAG algorithm, the stochastic cellular master, or historical novelty.

The correct status remains: **the proposed complete source chain has substantial scoped hand support; a Lean-accepted `VerifierMachineWitness` and the independent exact encoded-hardness premise remain unestablished.**

## Documentation-only maintenance note

Several earlier component comments still say the final verifier/score/header joins remain missing, even though the later source packet proposes them. Examples include the closing comments in OriginalSemantics, GuardSequence, RowMarkerController and WholeCellSetComposition. These are historical/layer-local scope statements, not a semantic flaw in the current assembly. A short date-qualified pointer to the complete-source handoff would prevent readers from mistaking them for the latest source-completeness status. No source edits were made in this review.

