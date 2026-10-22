# Pinned complexity dependencies and representation boundary

Author: dot (OpenAI), 22 October 2026, 08:25 UTC.
Status: read-only source audit and source-only proposal. No Lean/Lake/compiler/runtime execution or certificate.

## Addendum, 12:25 UTC: a licensed structured compiler candidate

`POLYTOMY-STRUCTURED-COMPILER-AUDIT.md` records the newly verified Apache-2.0 external Lax218471 repository and the exact proof-side compiler/composition interfaces. Its `Computable.lean` dependency is text-identical to ours, but its Lean/mathlib pins differ and no compatibility build was performed. Concept-side theorem declarations are axioms; the optional adapter references only corresponding `Lax218471Proofs` theorem names. Archive/status verification reports were retrieved, but referenced raw build/replay logs were not in the pinned tree and no Actions runs were exposed. Do not turn that external report into a verification claim for this packet.

The optional adapter still demands actual finite structured programs, real subroutine machines, all-input correctness and polynomial source-step/call-size bounds for our exact constructor and independent verifier. Our separate constant-branch module provides source terms for fixed literal outputs only. The complete machine obligation remains open, as do formal source hardness and every kernel check. No package was installed or vendored, no pin was changed, and no runtime was launched.

## Addendum, 12:05 UTC: binary widths before validation

`PolytomyBinaryWidthBounds.lean` proposes a complete all-string width-consumption chain. A successful binary reader consumes at least twice the canonical value bit width plus one framing bit; nested list-reader induction and header telescoping bound the sum of all source numeric widths by the actual input length. The target's three binary header widths receive the same all-successful-parse bound. This includes noncanonical high-zero payloads and does not replace numerical values by unary input lengths before validation.

The exact `Nat.size_le` and `Nat.size_eq_bits_len` statements were read in pinned `Mathlib/Data/Nat/Size.lean` at revision `0df444a360eaa60ab8c11dca51a86af692955474`. No version upgrade or compiler run occurred. The resulting whole-interface theorem retains the actual-label/all-topology reduction, output-size bound and independent bounded pair verifier. This is representation-size progress only. It does not instantiate either exact `TM2ComputableInPolyTime` obligation or discharge source hardness, operational composition or kernel validation.

## 1. An actual polynomial-time interface exists, but is not instantiated here

At mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`, `Turing.TM2ComputableInPolyTime` requires a concrete multitape-machine realization and a polynomial bound on its output time, measured against the encoded input length. This is an appropriate kind of endpoint for the encoded constructor/checker obligations. It is stronger than ordinary computability. [Pinned primary source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/Computable.lean).

The same file marks composition of polynomial-time realizations with `proof_wanted`, not a completed theorem. The inspected Batteries implementation describes `proof_wanted` as a placeholder carrying the requested statement but no proof; referencing a wanted statement introduces an explicit hypothetical dependency. It must not be treated as a proven composition lemma or an axiom silently available to this reduction. This is a scoped dependency finding, not a claim that no alternative formal complexity framework exists. [Pinned Batteries source](https://github.com/leanprover-community/batteries/blob/4488d40d070b9700d4d5a6aa342f0d40c31b2a2d/Batteries/Util/ProofWanted.lean).

`ManyOneReducible` in the pinned computability library instead requires a computable map and logical equivalence. Substituting it for a polynomial-time many-one reduction would weaken the claimed complexity conclusion. [Pinned primary source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/Reduce.lean).

The inspected `Computability` and `Combinatorics` source paths did not supply an MSSC NP-hardness theorem suitable for the exact source encoding. That bounded search is not a statement of global absence. The formal endpoint must either import a fully identified theorem with matched encoding/complexity semantics or prove the attributed hardness dependency; writing it as an assumption would give only a conditional theorem.

## 2. Classical enumeration is not a supplied polynomial constructor

The existing finite reduction model uses `Finset.toList` for an arbitrary enumeration. The pinned source explicitly defines this noncomputably using choice. This is legitimate in the finite mathematical proof, but does not provide the executable polynomial constructor promised by the separate hand encoding argument. [Pinned primary source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Dedup.lean).

A constructive continuation can enumerate the tagged original/private/marker ranges canonically, filter by the explicitly supplied memberships, and construct each fixed binary comb. Alternatively, `Finset.sort` has a constructive implementation under a decidable total antisymmetric transitive order, together with `sort_nodup` and `sort_toFinset`. [Pinned primary source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Sort.lean).

Correction recorded at 08:33 UTC: changing the enumeration of a fixed comb can change its cell-labeled clades, so equality or labeled-tree isomorphism cannot be inferred merely from equal terminal sets. However, for THIS unit-weight gadget every block has distinct type leaves, and a k-leaf comb's internal descendant cardinalities are 2,3,...,k. Its fixed cost is therefore sum_{j=2}^k (s-j), independent of the enumeration. The earlier 08:25 sentence incorrectly said that enumeration alone might change this C0; that overstatement is withdrawn. Different block shapes, or nonuniform type weights, can change the fixed cost.

A robust realization adapter can still preserve the block terminal sets, compute each realization's own fixed cost, and retain the exact joining-cost identity. Its threshold uses that realization's C0 and therefore does not need an isomorphism claim. This is a constructive continuation of the hand reduction, which already permits any explicitly chosen fixed binary block trees of the stated kind.

`PolytomyBlockRealization.lean` now proposes this entire adapter. It defines tagged-range numeric codes and canonical sorted block lists, proves proposed injectivity/range, observed-set, mixedness, distinct-cell and size bounds, and connects both the full graft and cut/frontier D_lambda decisions to the original full finite reduction. The formula avoids arbitrary enumeration choice in the output realization. It remains unelaborated and supplies no encoded machine or time certificate. `POLYTOMY-ENCODING-INTERFACE.md` also makes input-length-bounded validation explicit before any loops over binary-declared dimensions.

## 3. New cut/frontier interface, with orientation made explicit

`PolytomyFrontierInterface.lean` proposes:

- `TreeIso`, generated only by identity, symmetry, transitivity, child congruence and left/right swaps. It does not include rotations or reassociation.
- Invariance of observed terminal sets, the exact star sampling score and the all-internal-mixed property under this rooted unordered-tree relation.
- `BlockFrontier`: an explicit recursive cut into unchanged original block trees, allowing orientation isomorphism. Its list tracks block identities, never repeated terminal type labels.
- `frontierRefinement_iff_graft`: a cut containing every block exactly once is equivalent to an arbitrary permutation-valid binary joining tree, up to `TreeIso`.
- `frontierCartaDecision_iff_refinementDecision` and `full_frontier_carta_reduction`: the complete finite reduction, with actual compatible labels and D_lambda, now transfers to all such cut-certified cell trees.

These are proposed proof terms, entirely unelaborated. They extend, rather than replace, the full caterpillar/anchor/threshold chain. The final decision problem is not restricted to caterpillar trees.

For the usual clade-preservation definition of binary refinement, the mathematical correspondence is as follows. Cell identities partition into disjoint original child-block leaf sets. Each block set must remain a clade. Because the original child block is already a full binary tree, preserving all of its cell clades leaves no additional internal resolution to choose there. These preserved block roots therefore form a cut through the refined tree. Contracting the portions strictly above them gives a binary joining skeleton; grafting reverses this construction. Conversely, a valid graft preserves every original child-block cell clade. Repeated terminal types do not affect this argument because clades are sets of distinct cell identities.

Continuation at 09:05 UTC: `PolytomyCladeRepresentation.lean` now DOES define an independent cell-clade/subtree model and proposes the complete clade-preservation/frontier/graft proof chain, ending in `full_standard_canonical_carta_reduction`. It does not assume that equivalence or define the independent predicate through graft existence. `POLYTOMY-CLADE-FRONTIER-BRIDGE.md` gives the full hand proof and verifies the standard convention against Schaller, Hellmuth and Stadler (2021). All source remains unelaborated. A separate graph-edge-contraction datatype and kernel-verified equivalence are still absent.

## 4. Whole-claim status

The complete mathematical fixed-star refinement NP-completeness proof and general-DAG subset DP retain the earlier scoped hand review. Proposed finite proof terms now span the exact all-tree reduction, actual-label score adapter, canonical block realization, cut/frontier representation and independently defined cell-clade preservation. No term has been elaborated. Encoded polynomial realizations, source-hardness interface, a separate graph-contraction model and the general-DAG DP formalization remain additional obligations. No full formal NP-completeness or biological identifiability conclusion follows from this checkpoint.

## 5. Continuation, 09:30 UTC: an upstream bridge, not a weaker endpoint

`PolytomyExactCoverBridge.lean` proposes both directions of an exact X3C-to-MSSC threshold theorem and composes it all the way through `full_standard_canonical_carta_reduction`. The target remains all independently specified cell-clade-preserving binary refinements under actual D_lambda; no caterpillar restriction or surrogate label sum is introduced. The new source uses a prefix-capacity equality argument and explicitly constructs a complete ordering from a selected cover. Its full hand argument appears in `POLYTOMY-EXACT-COVER-BRIDGE.md`. An encoded classical X3C-hardness theorem could now replace the more involved MSSC source-hardness import, but that formal theorem and its matching machine-time interface are not supplied here.

Read-only investigation also found an alternative concrete mathlib-TM2 composition development with pinned external successful CI and inspected axiom logs. That is evidence against any global-infrastructure-absence claim, which this audit never made. `POLYTOMY-EXTERNAL-COMPLEXITY-AUDIT.md` preserves the exact repository revisions, existing run links, different toolchains, license/interface limits and the distinction between retrieved third-party CI evidence and this project's unelaborated sources. No external source was copied or executed. The encoded constructor/checker, hardness integration and full local elaboration remain open.

## 6. Continuation, 09:51 UTC: independent target verifier and fixed bit certificates

The three new certificate modules extend the same full reduction through an explicit independent target-data record, finite cell-clade reflection, total prefix parsing, bounded cell decoding and fixed Boolean witnesses. They include `full_mssc_bit_reduction` and `full_exactTripleCover_bit_reduction`; their endpoint still permits all admissible binary refinements and compatible actual-D_lambda labels. `POLYTOMY-BIT-CERTIFICATE-INTERFACE.md` proves the mathematical certificate correspondence and polynomial length bound.

No source-instance cover proof is passed to the target verifier. The constructor produces fixed blocks and budget; generic verification uses only those fields and the finite cell/type domains. The actual D_lambda equivalence is scoped to the canonical mixed gadget, not to arbitrary supplied blocks. Boolean certificate soundness ranges over every proposed bit string; completeness supplies a bounded encoded tree. A parsing inverse for valid tree encodings does not replace the separate successful-parse/checker soundness argument.

The source-only Boolean reflection uses noncomputable dependencies and is not a machine implementation. Instance bit encodings and malformed-input validation, a polynomial encoded constructor/verifier, compatible formal X3C/MSSC hardness and full elaboration remain open. The new bound uses a simple unary payload codec; its degree-five source-input bound is different from, and does not invalidate, the earlier sharper logarithmic-identifier construction-size estimate. No new runtime or external code execution occurred.

## 7. Continuation, 10:23 UTC: arbitrary source strings and total finite cases

The four new source-input modules now propose explicit binary-valued source parsing, malformed-dimension-safe record validation, successful-parser consumption bounds and the total finite source-bit-to-independent-target map. The polynomial numerical dimension bounds are proved for every parsed-and-validated input, not only canonical encoder outputs. Directly decidable source cases and malformed strings map to actual constant one-polytomy star targets with three composite binary blocks; they are not language sentinels. The zero-budget constant is excluded by a positive immutable block-cost lower bound over all refinements. A generic canonical-block actual-label adapter permits arbitrary budgets, retaining the full original D_lambda claim for the constants as well as the hard branch.

The new endpoint is `full_total_source_actual_reduction`. Source parsing and finite boundary-case semantics therefore have proposed terms now. Remaining whole-claim gaps are independent target-instance bit encoding/validation, concrete total polynomial machine implementations and cost proofs, compatible formal source hardness/composition, and elaboration of every dependency. The hand account `POLYTOMY-SOURCE-INPUT-INTERFACE.md` preserves this distinction. No existing hand-review attribution is expanded to the new source terms.

## 8. Continuation, 10:51 UTC: independent target bytes and target-sized witnesses

Target-side source now proposes an independent marked-star domain and raw guard, exact bit codec inversion, all-string parser consumption/dimension bounds, and L(2L+3) certificate size in target input length L. The domain is checked using the supplied finite trees, distinct observed type codes and two markers before enumerating numerical universes. It does not require an MSSC source, a canonical-origin proof or a solution witness. Every total source-map output lies in that independently specified domain. Its all-refinement actual D_lambda equivalence follows from the existing cell-clade/frontier theorem and the new marked mixedness induction.

The total proposed semantic map now has fixed Boolean alphabets at both ends. `full_encoded_source_actual_reduction` and `full_encoded_source_bounded_reduction` compose the entire chain, including all malformed/boundary cases and the independent target verifier. `POLYTOMY-TARGET-INPUT-INTERFACE.md` distinguishes this restricted hard-family encoding from a verifier for arbitrary original differentiation DAGs.

Independent target encoding/validation therefore has finite proposed terms now, not kernel acceptance. Remaining obligations include the constructor output-length/time theorem, concrete total polynomial machines, compatible formal source hardness/composition, full elaboration, and the arbitrary-DAG rational-weight verifier/full-DAG DP formalizations. Noncomputable specifications and size bounds are not polynomial-time certificates. No prior coordinating hand review is extended to these new terms, and no original stochastic-identification problem is closed.

## 9. Continuation, 11:05 UTC: total output size, not running time

`PolytomyOutputSizeBound.lean` proposes a degree-five bound for the actual encoded constructor on every source input. The proof accounts for all constant branches, the fixed-cost budget bound, framed binary numeric headers and the complete concatenated block forest. It retains the complete actual-objective and independent bounded-certificate endpoint in `full_encoded_reduction_with_size`. `POLYTOMY-OUTPUT-SIZE-INTERFACE.md` gives the full derivation and the polynomial 3(L+2)^5+10(L+2)^4+32(L+2)^3+51(L+2)^2+65(L+2)+41.

This supplies proposed finite output-size terms, not constructor/verifier machine running times. The remaining formal complexity interface still requires concrete polynomial machines, compatible formal source hardness and composition, and full authorized elaboration. No optimizer oracle or minimizing-order witness is used by the constructor. Existing noncomputable semantic declarations are not an executable certificate. The arbitrary-DAG verifier and DP obligations also remain separate.

## 10. Continuation, 11:22 UTC: explicit supplied-list verifier

`PolytomyListScanVerifier.lean` now proposes a separately defined list algorithm for independent target validation, cell-clade comparison, distinct-type score computation and complete encoded checking. Finsets and real scores occur in the specifications/proofs, not in the new algorithm bodies. Ordinary definitions are intended to be computational, but have not been elaborated or code-generated. The parser wrapper is definitionally the same grammar, and the proposed pointwise agreement ranges over every target/certificate bit-string pair, including malformed inputs.

The final `full_encoded_scan_reduction_with_size` retains the original actual-D_lambda and all-refinement reduction, all total source cases, the polynomial output bound and independent quadratic target certificate bound. The scanner does not request a source-instance or joining-tree witness. Exact structural terms bound its clade-list count and stored payload; the companion hand note accounts for ordinary list scans without declaring a new formal cost model equivalent to Turing-machine time.

The remaining bridge is still substantial: concrete finite-alphabet constructor/verifier machines and bit-cost time proofs, compatible upstream formal hardness/composition, and full kernel checking. A syntax-level ordinary definition and finite operation accounting cannot replace that bridge. This continuation makes the verifier's algorithm explicit without weakening the full target or expanding the scope to arbitrary differentiation DAGs or stochastic biological identification.

## 11. Continuation, 11:35 UTC: explicit constructor and exact machine types

`PolytomyExplicitConstructor.lean` proposes an ordinary-definition realization of the SAME total bit constructor, with pointwise byte equality. The source guard precedes bounded range enumeration, the canonical sorted fixed blocks are unchanged, and an explicit block-list score sum computes the same C0. Proof-only source coverage fields are not solution searches. The final full finite endpoint retains actual D_lambda and every admissible refinement, all malformed/boundary inputs and the existing output/witness bounds.

`PolytomyConcreteMachineInterface.lean` fixes the actual pinned finite-alphabet TM2 types required for both complete algorithms. Its pair-input parser is total and rejects malformed framing. `ConcreteMachineObligation` is merely the open conjunction of machine-witness existence, not an axiom or a proved assertion; no conditional replacement is presented as NP-completeness. The required output convention includes clearing every non-output stack and restoring the initial control state, so cleanup time is part of the missing machine proof.

Pinned Lean source clarifies that an explicit noncomputable modifier and a noncomputable section are not equivalent evidence about code generation. The new ordinary definitions are intended computational paths, but source inspection alone does not establish successful elaboration/code generation. The exact program/time witnesses, compatible formal source hardness/composition, all kernel checks and separately scoped arbitrary-DAG/graph-contraction obligations remain open. No optimizer oracle or weaker target is introduced.
