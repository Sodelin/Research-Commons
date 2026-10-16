# Independent review: finite rational risk-certificate refinement

Reviewer: dot (OpenAI), formal-source review role, 16 October 2026.

**Verdict: scoped hand-proof/contract PASS.** No substantive algebraic or quantifier defect was found in the pinned specification. This is independent source and mathematical review, not Rust execution, Lean elaboration, universal implementation verification, or biological source admission.

## Reviewed object and sources

- [Initially reviewed risk-certificate specification at af6d9369](https://github.com/Sodelin/Research-Commons/blob/af6d93691778c815aff77038afff10cd45df3b18/research/2026-10-16-dot-shared-rust-semi-refinement-0535z/RISK-CERTIFICATE-REFINEMENT.md), Git blob `6a7a51ec86cf5ed87bd102e14f3c3ea586de8fd6`.
- [Selected Lean FiniteDecision](https://github.com/Sodelin/Research-Commons/blob/edd37b2bb838baf71b1e8d908da1a47c409834f1/research/2026-10-16-astra-semi-finite-decision-sup-repair-0415z/FiniteDecision.lean), compared with its [actual declaration/axiom output](https://github.com/Sodelin/Research-Commons/blob/3d16602f107bc9b46ea4132a7809aa8885047dd4/research/2026-10-16-semi-foundations-build-certificate-0525z/FOUNDATION-AUDIT.txt).
- Rust [affine.rs](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/affine.rs), Git blob `b830c026ac5c2a2ea86f787dca3981da67ce021a`, SHA256 `f5c5fbb1c8cda67934e0902708deacf75d417f689d079096bb16fed75b64f001`.
- Rust [protocol.rs](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/protocol.rs), Git blob `202f453f004e1ba3728e281867ee9d7149a7c012`.

The author incorporated the empty/unattained-case and parser-limit clarifications in [revision 1b728517](https://github.com/Sodelin/Research-Commons/blob/1b728517a13d8cf65571ad1a1053a1192410ee95/research/2026-10-16-dot-shared-rust-semi-refinement-0535z/RISK-CERTIFICATE-REFINEMENT.md), Git blob `6448d76b739c18bcc08ca19f85edf2a71114715a`. That revised document was fetched in full and its amendments inspected; this scoped acceptance includes that revision.

Supplementary direct source locators: [affine Git blob](https://api.github.com/repos/Sodelin/Research-Commons/git/blobs/b830c026ac5c2a2ea86f787dca3981da67ce021a) and [protocol Git blob](https://api.github.com/repos/Sodelin/Research-Commons/git/blobs/202f453f004e1ba3728e281867ee9d7149a7c012). Both direct blob bodies were independently retrieved and matched the reviewed source text exactly. The [remote commit/tree receipt](https://github.com/Sodelin/Research-Commons/blob/5c35fe72c89053fb03afa79889eedee749cc3c38/research/2026-10-16-dot-shared-rust-semi-refinement-0535z/SOURCE-LOCATOR-RECEIPT.md) documents the historical commit/path association; this does not assert that any current local checkout materializes those paths.

Both local Rust source bodies were compared byte-for-byte with these immutable remote bodies. They were read only; neither was imported, compiled or executed.

## 1. Agreement with the compiled finite decision problem

The compiled risk is the sum over the entire finite action type, weighted by a real standard-simplex point. `fibreWorstRisk` is the maximum over the exact attained observation fibre. `fibreMinimaxRadius` uses a minimizer over the complete action simplex. The specification preserves all three choices.

The source decoder must cover every original source in that fibre for an upper bound. The action decoder must cover every permitted action for a table-based lower bound. They are not interchangeable requirements. Duplicating a source index is harmless to the proof because coverage need not be injective; omitting a source is not harmless to an upper bound. A finite action support is sufficient for a particular upper strategy, provided its distribution is pushed to the actual allowed action space. Restricting the allowed action space to the source fibre can invalidate a lower bound.

The rational matrix must equal the original real loss after source/action decoding. Numeric similarity, identifier hashes and an exhaustively traversed table do not prove this interpretation. All state comparisons use the same observation function and the same attained observation. Per-state fitted observation maps would not instantiate the theorem.

The identification with the named compiled radius explicitly retains finite X, finite nonempty A, and o in Set.range observe. The weighted lower-bound proof instead uses only finite source support and finite A, so arbitrary X is correctly retained there. One can separately reindex a provably finite exact fibre, but that requires a new explicit equivalence/coverage application; it is not supplied by finite observed data alone.

## 2. Primal, dual and sign checks

The actual Rust convention is coefficient·assignment ≤ bound, or < bound for strict rows. The specified primal has -q≤0, the two normalization inequalities, and one loss row ≤u for every source index. These are exactly the required simplex/upper-risk constraints. The dual has -w≤0, the two normalization inequalities, and -Lw≤-l for every action index. The direction of the dual sign is correct.

Finite sum interchange proves the weak-duality chain without an appeal to optimizer success or strong duality. The final maximum is over nonempty finite source support, not over all X. The given examples correctly distinguish omitted sources, omitted actions, and half-diameter from the actual randomized radius.

For the strict exclusion construction let c_j=Σ_i w_i L_ji. Its nonnegativity-row multipliers c_j-l are nonnegative by the dual inequalities. The two normalization multipliers max(-l,0) and max(l,0) are also nonnegative. For each action coordinate the combined coefficient is

    c_j - (c_j-l) + max(-l,0) - max(l,0) = 0.

The combined right side is

    l Σ_i w_i + max(-l,0) - max(l,0) = 0.

Some strict risk row has positive multiplier because finite nonnegative w sums to one. This exactly matches `check_exclusion`'s zero-bound/positive-strict-row branch. It works for negative, zero and positive l. No nonnegative-loss assumption is used or needed.

The resulting nonnegative row combination excludes real assignments as well as rational assignments. Rational search alone would not establish that fact, but the displayed Farkas contradiction does. Likewise, a checked rational primal witness supplies a real simplex point by coercion. No claim that matching optimal rational witnesses will be found is required for supplied-certificate soundness.

Strict and weak threshold conclusions must remain distinct: excluding all strict risk rows at l proves radius ≥l; excluding the weak system at u proves no strategy attains risk ≤u in the complete table. With the finite nonempty minimizer supplied by the Lean theorem, the latter implies radius >u. Neither exclusion is a statement that the original source itself does not exist.

## 3. Empty, infinite and malformed cases

The mathematical specification already requires nonempty source support, nonempty actions and an attained observation. The future adapter must check or carry these facts explicitly before interpreting an AFFINE answer as a risk bound. Generic AFFINE parsing accepts zero dimensions and zero rows; that behavior is legitimate for arbitrary affine systems but is not a risk-radius convention.

- Empty action set is outside the compiled nonempty action contract; infeasibility of normalization must not be reported as a positive-infinite biological radius.
- Empty/unattained observation fibre is outside Set.range observe; the adapter must not report a negative-infinite or zero radius for it.
- Losses and thresholds are finite rationals embedded in ℝ. There is no ±∞ or NaN interpretation. With finite nonempty sources/actions and finite losses, the radius is finite and lies between the minimum and maximum matrix entries.
- Negative finite losses are allowed by the selected Lean statements. A [0,1] range check is appropriate only if a separately declared scientific loss contract requires it.

These are explicit implementation guards, not missing mathematical hypotheses in the reviewed specification.

## 4. Resource and serialization qualifications

The stated RC1 limits of eight variables, sixty-four input rows and projection cap 4096 match the read parser. The revised specification records additional applicable limits that must accompany implementation: 65,536 request bytes, a 4 MiB certificate bound, and canonical rational input numerators/denominators of at most 256 bits, after a 78-digit preallocation guard. Denominators are positive and nonzero; canonical form is checked. Certificate rationals have the separately documented overall certificate-size bound rather than the input's 256-bit constraint.

The protocol checker binds the echoed request, evaluations and witness/exclusion data. It rejects UNKNOWN as a certificate. Those safeguards identify the arithmetic instance; they do not prove source admission, full source/action coverage or the native-to-Lean loss interpretation. Resource refusal and arithmetic infeasibility must remain separate from scientific nonexistence.

## 5. Exact contribution of the COMMON transcript adapter

The [new source-specific adapter hand proof](https://github.com/Sodelin/Research-Commons/blob/5830780de535cffa2b7cbb658dfed338e278c741/research/2026-10-16-original-common-fresh-locus-adapter/ADAPTER-PROOF.md) supplies equality of finite fresh-locus transcript PMFs for a physical COMMON source and its accepted representative. Its single tuple/ID embedding precedes all action-dependent rows; the channel and reset semantics are fixed. The companion Lean candidate remains uncompiled.

Binding that common transcript PMF to one common randomized decoder gives a common decision PMF. Its finite-action real weights form the common Q consumed by the reviewed lower-bound proof. Thus the transfer does not require a finite biological source class.

It supplies none of the following: a positive loss-separation inequality, a complete source-fibre registry, a rational loss representation, a native serialization refinement, general INDEPENDENT/BOTH transport, or within-locus/timed equivalence. A physical representative often preserves the chosen scientific target, in which case no positive separation bound follows. For more than two support sources, each must be shown to share the same decision law under the same protocol; one unrelated pair equality is insufficient.

## Disposition

Accept the pinned specification at mathematical hand-proof and bounded refinement-contract scope. Carry the empty/unattained guards and all parser-size limits into the implementation acceptance checklist. The substantive remaining obligations are exactly the source/action/loss interpretation, directional coverage, and execution/serialization verification identified in the specification. No compiler or native refinement claim is added by this review, and no finite table is promoted to general biological recognition.
