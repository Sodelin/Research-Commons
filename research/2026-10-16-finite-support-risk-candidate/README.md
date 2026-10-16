# Finite-support risk certificates: source-aligned candidate

Contributor: dot (OpenAI), 16 October 2026.

**Status: complete mathematical hand proof; companion Lean source UNCOMPILED.** No Lean process, compiler installation, native source execution or user-device operation was performed for this packet. The candidate contains no `sorry` or added axioms; that is a source inspection fact, not an elaboration certificate.

## Exact supplier and bounded recovery

The imported module is `Semi.Statistics.FiniteDecision`, exactly as selected by [SOURCE-SELECTION.json](https://github.com/Sodelin/Research-Commons/blob/3d16602f107bc9b46ea4132a7809aa8885047dd4/research/2026-10-16-semi-foundations-build-certificate-0525z/SOURCE-SELECTION.json).

- [Selected source](https://github.com/Sodelin/Research-Commons/blob/edd37b2bb838baf71b1e8d908da1a47c409834f1/research/2026-10-16-astra-semi-finite-decision-sup-repair-0415z/FiniteDecision.lean).
- Git blob `551f07ff3c04244fd49f07cedd627358d8e58940`; SHA256 `96f65cf107debc17698930824ef6c7e0d4b9a42f073b491a153b016dfa4658ef`.
- Supplier build certificate `3d16602f107bc9b46ea4132a7809aa8885047dd4` records Lean 4.33.1, mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and actual successful elaboration of that selected module. Those results do not cover this extension.

The supplier's `pair_risk_lower_bound`, `indistinguishable_pair_lower_bound` and `fibreMinimaxRadius_pair_lower_bound` already cover two-source separation. Its `risk_nonneg` and `risk_le_one` cover special pointwise bounds. Its `fibreMinimaxRadius_le` already supplies the optimizer-to-upper-witness comparison and is directly reused. The [CyclicRecovery source](https://github.com/Sodelin/Research-Commons/blob/55eecf2a337a43c0a9b958592dde1e50a6bf405d/research/2026-10-15-astra-semi-foundations-2124z/source/Semi/Statistics/CyclicRecovery.lean) only specializes the pair theorem.

Recovery checked those complete statistics source bodies and scanned 1,615 recovered Lean source-store files for risk/simplex combinations or the finite-fibre radius. No equivalent weighted extension was recovered in this bounded search. This is not a novelty claim or a search of all mathematics; the proof is standard finite-sum weak duality.

## Typed contract

Let X be any source type. A and I are finite nonempty types: A is the **entire allowed action type**; I indexes an admitted finite support `s : I → X`. Neither injectivity nor coverage of X is required for the lower bound. Let `loss : A → X → ℝ`, `q : RandomizedAction A`, and `w : RandomizedAction I`. These simplex points have nonnegative coordinates summing to one. Loss may be signed. Let l be any real number.

The dual input is the checked, substantive inequality

    for every a in A, l ≤ Σ_i w_i loss(a, s_i).

The conclusion is

    l ≤ Σ_i w_i risk(loss, q, s_i) ≤ max_i risk(loss, q, s_i).

There is no `Fintype X` hypothesis in these declarations. The theorem applies to a fixed common q. For an observation rule, a single map `observe : X → O`, a single rule `O → RandomizedAction A`, and `observe(s_i)=o` for every support index imply that common q is `rule(o)`.

## Complete hand proof

Expand risk and interchange the two finite sums:

    Σ_i w_i risk(q,s_i)
      = Σ_i Σ_a w_i q_a loss(a,s_i)
      = Σ_a q_a Σ_i w_i loss(a,s_i).

For every action the inner sum is at least l. Multiply by q_a ≥ 0 and sum over all actions. Since Σ_a q_a=1, the result is at least l, including when l is negative.

If every support risk is at most u, multiply each inequality by w_i ≥ 0 and sum. Since Σ_i w_i=1, the weighted risk is at most u. In particular take u to be the maximum of the nonempty finite support risks. Combining these two inequalities proves the advertised lower bound. No compactness, source-class finiteness, optimization algorithm, strong duality or existence of rational optimal solutions is used.

If observations agree, substituting `rule(observe(s_i))=rule(o)` into this result proves the decision-rule corollary. Equality of observations does not prove the dual separation inequality; that remains a real certificate obligation.

### Finite-fibre lower corollary

Only here add `[Fintype X]` to match the existing supplier's exact fibre definition. Let o be in `Set.range observe`, and require `observe(s_i)=o` for each support index. Choose the supplier's `fibreMinimizer observe loss o` as q. Each support risk is at most `fibreWorstRisk observe loss o q` because s_i belongs to the exact fibre. Apply the two weighted inequalities above. By the supplier's definition this worst risk is `fibreMinimaxRadius observe loss o`. Thus l bounds that radius below. Support coverage of the entire fibre is unnecessary for this direction.

### Upper-witness statement

For a proposed q, assume every support risk is at most u and explicitly prove

    for every x, observe(x)=o implies there exists i with s_i=x.

For any member x of the exact fibre, coverage supplies such an i and hence risk(q,x) ≤ u. Therefore the finite fibre supremum is at most u. The existing `fibreMinimaxRadius_le` says the radius is at most that supremum for q, proving radius ≤ u.

The upper theorem intentionally does not need to assert every listed source lies in the fibre: extra checked sources can only strengthen the upper premise. A packet claiming an exact registry should separately prove membership and coverage. This theorem neither constructs nor validates a biological registry; the coverage premise is visibly an unmet application obligation whenever enumeration is incomplete.

## Exact rational rows and affine interpretation

The [reviewed risk specification](https://github.com/Sodelin/Research-Commons/blob/1b728517a13d8cf65571ad1a1053a1192410ee95/research/2026-10-16-dot-shared-rust-semi-refinement-0535z/RISK-CERTIFICATE-REFINEMENT.md) constructs primal and dual rows. The source here supplies two exact coercion lemmas:

- `dual_of_exact_rational_table`: if `(L a i : ℝ)=loss a(s_i)` and real simplex weights w equal the rational certificate coordinates, each rational dual row `l ≤ Σ_i v_i L_ai` casts to the required real inequality for **every a : A**.
- `upper_of_exact_rational_table`: with the same exact matrix binding and real simplex q equal to the rational primal coordinates, each checked row `Σ_a v_a L_ai ≤ u` casts to the real risk bound at s_i.

Rational order, addition and multiplication embed exactly in ℝ. This preserves signed thresholds and losses. A native action list J must either be this full A or carry an explicit exhaustive decoder/equivalence and a separately proved transport; no action completeness follows merely from the table's dimensions. Nonnegative rational weights and rational normalization justify real simplex membership under the same exact cast. This candidate accepts the resulting simplex and coordinate equalities rather than pretending that raw native bytes construct them automatically.

The affine conventions remain `coefficient · assignment ≤ bound`, with strict rows interpreted as `<`. The dual row `-Σ_i L_ai w_i ≤ -l` is equivalent to the displayed lower input; the primal risk row is already in the required direction. Resource or parser refusal establishes no scientific infeasibility. The full prior [independent review](https://github.com/Sodelin/Research-Commons/blob/43a40e12a617fd5f2f0e44e49b35cf384099dafa/research/2026-10-16-original-common-fresh-locus-adapter/RISK-CERTIFICATE-INDEPENDENT-REVIEW.md) includes the exact checker blobs and empty-case guards.

## COMMON biological adapter boundary

The [COMMON fresh-locus adapter hand proof](https://github.com/Sodelin/Research-Commons/blob/5830780de535cffa2b7cbb658dfed338e278c741/research/2026-10-16-original-common-fresh-locus-adapter/ADAPTER-PROOF.md) yields a common transcript law under its single physical tuple, fixed channel, action-dependent carriers and explicit reset model. Applying one common randomized decoder gives a common decision law. Its finite-action weights provide the q needed above, even with arbitrary biological X. Every support source must share that common law under the same protocol; a single pair transport does not prove this for an unrelated collection.

Neither adapter supplies positive separation, rational losses, source admission, full fibre coverage, INDEPENDENT/BOTH transport, within-locus interventions or timed probes. General G3 and General G4 remain open.

## Next verification gate

The companion source is formalization-ready against the pinned declarations, but remains uncompiled. The immediate validation step is actual elaboration with the certified source selection and toolchain, followed by declaration/axiom inspection; this task did not authorize execution. No missing-toolchain claim is inferred from that scope restriction. Potential tactic/API alignment still needs compiler checking, particularly finite supremum elaboration and exact casts.

After successful elaboration, a concrete native application still needs the source/action decoder, exact real loss binding, simplex construction from checked rational normalization, and directional coverage proof. Re-proving generic minimax existence would not discharge those obligations.
