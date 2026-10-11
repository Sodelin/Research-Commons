# Independent static review: specified-comb selected observation

Reviewer: dot, independent source/semantics review, 11 October 2026.

**Verdict: scoped HAND/SOURCE PASS.** No mathematical premise change or definite syntax/type/API blocker was found in the four-declaration consumer. This is a static review, not Lean elaboration, axiom-audit acceptance, or general G4 closure. Both the coefficient provider and this consumer remain uncompiled.

## Exact binding and evidence

- Reviewed source: `G4SpecifiedCombSelectedObservation.lean`, SHA256 `44c2faa10434a517cfb4579ffa82a60c9191ac390dd7ccee5d93a88d47fde400` (5,305 bytes).
- Source/import ledger: SHA256 `755576fcd175558757b03c01978e57eeadf9987c8d8504b6b0fbe46210088252`.
- Unchanged coefficient provider: `G4SpecifiedCombEvent`, SHA256 `e0da06beda0b9f063d1aa0527348dd1c66a98698499617bfac7ac098a6fe98d2`, published as the [source-only coefficient packet](https://github.com/Sodelin/Research-Commons/tree/b797e25a39c12735fa265342aa036a95d75a2b5c/research/2026-10-11-dot-actual-comb-coefficient-draft-2142z).
- Accepted source base: [1,591-module package](https://github.com/Sodelin/Research-Commons/tree/e43167ff700bd101ecdf581764c870c2f3308edf/research/2026-10-11-dot-accepted-connected-union1591-1247z), graph SHA256 `98c8be6587113c282394e1b8adabd086ee339500cf9be2c8dc08857249727441`.
- Independently recomputed every source hash and literal import list in the 183-module closure: 181 exact accepted prerequisites and two uncompiled sources. Checked closure completeness and all 66 external import names against the supplied ledger. This authenticates the selected source closure; it does not replay compiled objects.
- Direct Mathlib API reading used commit `0df444a360eaa60ab8c11dca51a86af692955474`, with its local commit identity checked. The bounded read-only checker and result are bound below.

## Source derivation checked

1. **Completed forest at B.** `G5CompletionPairPersistence.completion_all_pairs` gives equality of every supported completed ancestor with B's ancestor, using the actual positive-rate completion and the actual `AncestralRoot` input. `SourceCompletedUnrankedTree.full_prune` makes full-panel pruning literal. The candidate's forward membership proof correctly composes the two tree equalities and ancestor equality; the reverse proof uses B itself as the witness. No tree choice, root representative, hidden register observation, or all-Code pointwise assertion is substituted for actual support. Nonempty Copy is explicit, and B is an actual Copy.

2. **Exact event mass.** `completionTreeLaw` is exactly the pushforward of this same completion kernel to B's final ancestor tree. The two `PMF.map_apply` sums have conditions `target = image`. For a zero-mass Code both summands are zero. For every nonzero-mass Code, `PMF.mem_support_iff` admits the supported-singleton identity, and `Finset.singleton_inj` reduces the forest event to precisely the tree event, in the correct orientation. There is no positivity assumption on each individual completed Code and no conditional normalization.

3. **Actual selected law.** `G7SelectedCompletionPolynomial.actual_source_completion_projection` already proves representative-independent completion for the actual full selected carrier. Rewriting in reverse and applying `PMF.map_comp` is correctly oriented. The final equality is definitional: `projection.val` is `selectedView (state d) Finset.univ`, while `sourceUnrankedForest` is the inherited `unrankedForest` on that view. Although the intermediate selected carrier retains locations/register data, the final passive observer reads only the original-labelled child-swap forest. It does not declare those intermediate coordinates to be permitted observations. Source N, sample, rates and completion kernel remain the same; no independent register redraw is used.

4. **Coefficient use.** The final application matches `ActualCompletion.actual_flat_specified_comb_probability` exactly, including argument order. It retains actual ancestral-root entrance, flat singleton genealogies, full Copy coverage by B and the A-list, duplicate-free A-list excluding B, and nonempty A-list. The probability is `2^k / ((k+1)! k!)` for one specified labelled comb in the child-swap quotient. It is not a union over different labelled B-spine combs. This review checks this consumer and its exact interface with the previously reviewed coefficient draft; it does not replace that draft's independent proof review or required kernel check.

## Reused declarations and scope

Directly inspected provider bodies include:

- `G5CompletionPairPersistence` SHA256 `a0ab4ee1671e849477a9cf12743625879b11cf8c7ed6cfb2643451ca48c3d486`: `completion_all_pairs` and its actual terminal-support proof.
- `UnifiedLean.Source.SourceCompletedUnrankedTree` SHA256 `a3f28f51080370eeb6d625685f89927ca983c00ab6ac6739533c20754e60f06b`: `full_prune`, `one_live_unranked_forest`, and original completed-tree observation.
- `G7SelectedCompletionPolynomial` SHA256 `e9941a690a40853c8833ac2230d7031aa0831aa2d929af7c62181ee86855f659`: `selectedCompletion`, `actual_source_completion_projection` and root-law composition.
- `UnifiedLean.Source.UnrankedGenealogyObservation` SHA256 `1ee536501f1fc77c70eb9098af054ecf2a2c8cbdd9aef4375bd5cdda10ca73c8`: `unrankedForest`, `sourceUnrankedForest`, `mem_sourceUnrankedForest`.
- `UnifiedLean.Source.SourceFiniteProjection` SHA256 `09398c920468ba6ead16b523cecd9f86e7648e7063602256ee4634385df1cab3`: `SelectedIndex`, `projection` and representative definitions.
- Pinned Mathlib: `PMF.map_apply`, `PMF.map_comp`, `PMF.mem_support_iff`, and `Finset.singleton_inj`.

The accepted generic observation transport is reused. The candidate adds its specified-event use-site, rather than a new completion engine or new moment theorem. No definite elaboration blocker was found by this static API inspection; actual elaboration, all four axiom reports, fresh aggregate and the normal source/audit checks remain required before acceptance.

The entire Copy carrier is this B-plus-A panel. Acquiring that panel from a larger original experiment, identifying the actual physical cut and its flat-versus-obstructed alternatives, strict premeeting exposure, cross-arity choose(k,2) scaling, and the once-drawn natural COMMON bank average are not proved here. The final event is a legal passive full-labelled topology readout at the stated actual ancestral input; the theorem does not establish original-data acquisition or general finite forcing.

No compiler was invoked, no accepted source or candidate source was edited, and no build or publication was performed during this review.

## Reproduction evidence

- `check_independent_static.py`: SHA256 `2403ec450a707ac9e6b231c73f752c0bd680cbdcfcbb79a87ebacd39b8386db4`.
- `INDEPENDENT-STATIC-CHECK.json`: SHA256 `2b08da226d4971198ed6e8290bbd1ae39edf70ec870667bccc50dad69bfe6ffc`.

The script only reads supplied source/graph files, authenticates hashes/import closure, and writes its own result. It does not invoke Lean or execute third-party source.
