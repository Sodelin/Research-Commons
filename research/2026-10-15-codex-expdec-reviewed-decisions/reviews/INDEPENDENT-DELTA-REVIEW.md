# Independent agent review of the compact delta theorem

Review date: 15 October 2026. Reviewer: `/root/independent_proof_review`, a separate Codex reasoning agent. This is a hand review by an agent, not external human peer review or formal verification.

Reviewed source: `research/COMPACT-DELTA-THEOREM.md`.

- SHA-256: `fa60878a7e8b7b0ba2ac7b8f17993fdddfe9b95d2f85b445516802a0f98ffd21`.
- Git blob: `ad465abf90a57d2ab20a0afafccddaf024626252`.
- Repository HEAD at inspection: `58a84f0acf2809304363cb4926cee97190f6f422`.
- References to line numbers below refer to this exact source.

## Verdict

Theorem 3 and the fixed-chart corollary pass this scoped hand review. No counterexample was found under their stated compactness, weak-comparison, fixed-box, totality and effective-encoding hypotheses. The grid error budget and threshold inequalities are correct. Arbitrary finite exponential nesting causes potentially enormous bounds, but does not invalidate finite termination.

Recommended clarifications are: require a certified positive rational guard bound, make residual scaling and units explicit, and emphasize that the exact margin promise excludes every satisfiable equality-only fitting instance. A constructive rational parameter witness can also be retained for the existential-only chart corollary.

## 1. Truth and robustness

For subformulas, robustness is a continuous real function of their free variables. This follows inductively from continuity of the terms, finite min/max, and extrema over fixed nonempty compact boxes. For the latter operation, a common uniform Lipschitz bound also proves continuity directly.

The equivalence between weak-formula truth and nonnegative robustness is valid:

- Finite conjunction and disjunction correspond to min and max with the expected nonnegative sign test.
- For an existential quantifier, nonnegative maximum robustness yields a witness because the maximum is attained. Without attainment, this direction fails.
- For a universal quantifier, nonnegative minimum robustness is equivalent to all values being nonnegative.

Closed boxes of zero width are harmless: they are nonempty compact domains with a one-point coordinate net. Empty boxes would require separate truth and robustness conventions and are correctly excluded.

The recursive definition should be understood for subformulas with free variables, not only the closed root. Bound variables may be renamed distinctly before forming the product of boxes. Quantifier bounds must remain fixed boxes; dependent or constrained domains require their own treatment.

Boundary counterexamples confirm the restrictions. The strict atom `0 > 0` is false even though its unmodified numerical robustness is zero. The sentence `exists x in (0,1], -x >= 0` is false, while replacing its unavailable maximum by a supremum gives zero. Neither is admitted by this theorem.

For ordinary nonempty finite formula syntax, there is at least one atom and the maximum atomic Lipschitz bound exists. If empty conjunctions, empty disjunctions or a zero-length response vector are later admitted, define their Boolean meaning separately rather than silently assigning finite real robustness to infinity-valued identities.

## 2. Exact common shift under weakening

Weakening an atom is equivalent to replacing its robustness `f` by `f + delta`. Every finite min/max and fixed-domain infimum/supremum commutes with the addition of the same scalar. Induction therefore gives exactly

\[
r(\phi^\delta)=r(\phi)+\delta.
\]

For an equality encoded as the pair `f >= 0` and `-f >= 0`, robustness is `-|f|`. Weakening both atoms gives `delta - |f|`, so the permitted residual is exactly `|f| <= delta`.

This is a syntactic residual tolerance, not an invariant geometric distance. For example, `f >= 0` and `100 f >= 0` have identical exact truth conditions but different delta weakenings: the second permits `f >= -delta/100`. The chosen residual representation, normalization and units are part of the input contract. Likewise, unequal per-atom tolerances generally do not yield one common scalar shift, though their effect can be bounded separately.

Negation cannot be handled by merely changing `f >= 0` into `-f >= 0`; at `f = 0`, both weak inequalities are true. The stated positive weak syntax correctly avoids that boundary error.

## 3. Lipschitz and grid error bounds

The recursive magnitude and Lipschitz table is valid in the maximum norm on the full product domain. In particular,

\[
|uv-u'v'|\leq B_u|v-v'|+B_v|u-u'|
\]

gives the multiplication row, and the derivative of exponential on `[-B_u,B_u]` is bounded by `exp(B_u) <= U(B_u)`. The proposed rational `U(b)` is a valid finite upper bound for all rational `b >= 0`.

Coordinate magnitudes use both endpoints, and coordinates have Lipschitz constant one for the maximum norm. Addition uses the sum of bounds. This is significant in multiple dimensions: `x_1 + ... + x_n` needs the bound `n` in the maximum norm; replacing it by the largest single-coordinate derivative bound of one would be wrong. The current recurrence uses the correct sum.

For functions `g_i` with common bound `L`, pointwise min and max retain `L`. For a compact fixed box `K`,

\[
\left|\max_{z\in K}g(x,z)-\max_{z\in K}g(y,z)\right|
\leq L\|x-y\|_\infty,
\]

by comparing the same `z` in the two extrema; the same proof works for minima. This remains valid across arbitrarily nested quantifiers.

For a contained `h`-net, the difference between a true extremum of an `L`-Lipschitz function and its finite-net extremum is at most `L h`. Uniformity in the remaining variables allows induction through the whole formula. If `e(child)` bounds the inherited error, then a quantifier contributes at most `e(child) + L h`; a Boolean node contributes at most the maximum of the child errors. Thus `q L h` is valid when `q` counts the largest number of quantifier blocks along a syntax branch. It need not count all branches additively.

Rational finite nets exist effectively for every rational closed box, including degenerate boxes. A coordinate lattice with mesh at most `h`, together with any needed final endpoints, suffices. A vector quantifier block needs a net in the maximum norm of the entire block.

The `q L = 0` case is sound. If `q = 0`, no quantifier discretization is required. If `L = 0`, each atomic term is constant over the full domain and every composed robustness function is constant in the relevant variables; any nonempty contained nets preserve all extrema exactly. No division by zero is required when choosing a mesh.

Finally, min/max are nonexpansive in uniform leaf-value error. If each *entire atomic term evaluation* is approximated within `epsilon`, the whole finite evaluation tree incurs at most `epsilon`, not the sum over its number of leaves. The phrase entire term matters: assigning that same error independently to every arithmetic syntax node would require propagation and would not by itself establish the leaf error contract.

Therefore the stated bound `q L h + epsilon <= delta/4` follows from the chosen two `delta/8` budgets. Branching and nesting introduce no missing factor.

## 4. Threshold and margin promise

The threshold test is sound, including its equality branch:

- If `rhat >= -delta/2`, then `r >= -3delta/4 > -delta`, so the weakened formula is true.
- Otherwise `r < -delta/4 < 0`, so the original formula is false.

The outputs need not be disjoint mathematical alternatives, because `-delta <= r < 0` is an allowed overlap. No exact truth conclusion follows merely from returning `TRUE_DELTA`.

Under `|r| >= delta`, the `delta/4` approximation error preserves the exact sign, proving the promised exact decision. However, this promise has a particularly sharp limit for equality-only fitting. In the chart corollary,

\[
r(\phi)=-\min_{\beta\in K}\max_j|F_j(\beta)-y_j|\leq0.
\]

Every exactly satisfiable fitting instance has `r = 0`. Thus the margin promise excludes **all** such satisfiable instances; it is not an exact fitting solver for zero-residual equations. The draft's zero-margin and exact-attainment warnings are justified and should stay prominent.

## 5. Guarded reciprocal and log extension

The recurrences are correct when the lower bound is certified over the full product domain:

\[
\left|1/u(x)-1/u(y)\right|
\leq L_u\|x-y\|_\infty/m^2,
\qquad
|\log u(x)-\log u(y)|
\leq L_u\|x-y\|_\infty/m.
\]

Specify `m` as a supplied positive rational, or require an effective certified positive rational minorant. Merely mentioning an arbitrary real positive lower bound without its effective representation would not suffice for the rational-bound construction.

An explicit rational logarithm magnitude bound is

\[
B_{\log u}=\max(B_u,1/m).
\]

Indeed, for `u >= 1`, `log u <= u <= B_u`; for `0 < u <= 1`, `-log u = log(1/u) <= 1/u <= 1/m`. This avoids relying on a separate logarithm routine merely to obtain a magnitude bound. Certified approximation of log itself can be obtained by monotone inversion of exponential with the supplied positive range.

A guard that holds only on the eventual satisfying points is insufficient for this proof, which samples the entire quantified box. Similarly, grid samples alone cannot certify the absence of a pole between samples. Exact protected constraints may be built into a chart; putting a reciprocal into a Boolean branch that is expected not to be used does not make it total on the full domain.

## 6. Fixed admitted chart and constructive witness

The corollary is valid under the stated chart hypotheses. A single outer existential tuple makes every response use the same source parameters. Weakening the paired response equalities yields exactly the maximum-residual bound. Since every chart point is already admitted, neither the grid nor the numerical relaxation changes protected equalities, IDs or physical requirements.

The shared-tuple warning is necessary. For example, on `beta in [0,1]`, the two exact responses `beta = 0` and `beta = 1` each have their own solution, but they have no shared solution. At any `delta < 1/2`, even their simultaneous delta relaxations have no common solution. Separate row fits would therefore give an invalid common-source conclusion.

For the existential-only chart formula, the construction can additionally retain a concrete rational grid parameter `beta_hat` on its `TRUE_DELTA` branch. Choose a grid point maximizing the computed finite robustness. Its true pointwise robustness differs from the computed value by at most the leaf error `delta/8`, with no grid-discretization error needed for that fixed point. Therefore

\[
r(\text{body})(\widehat\beta)
\geq\widehat r-\delta/8
\geq-5\delta/8>-\delta.
\]

So this rational parameter has all response residuals bounded by `5 delta/8`, and certified leaf enclosures can record that fact. This is a justified optional strengthening. It provides a parameter witness; materializing a physical source still uses the supplied chart's own construction interface.

For arbitrary formulas with universal or alternating quantifiers, a single parameter point is not generally a witness to the whole sentence. Do not transfer the existential-only witness claim to Theorem 3's full syntax without a separate strategy or certificate argument.

The chart need not be injective for this corollary. It must cover only admitted sources, be defined throughout its compact box, and expose the complete response vector being tested. The theorem does not establish those model-specific hypotheses or supply additional charts, complete source coverage or any all-size exclusion.

## Prior method and verification level

The [Gao–Avigad–Clarke primary paper](https://arxiv.org/abs/1204.6671) establishes bounded delta-decision for computable real-function languages. The [author-hosted proceedings text](https://www.cs.cmu.edu/~sicung/papers/lics2012.pdf) describes the dual weakening convention as well. The source's attribution as a grid specialization of an established method is appropriate. No novelty conclusion is made here.

Performed: source hash/blob inspection, independent hand reconstruction of the induction and bound arithmetic, hand counterexamples at the strict/noncompact/scaling/shared-tuple boundaries, and inspection of those primary references.

Not performed: SMT jobs, numerical runs, compiler builds, new tool installation, proof-assistant checking, engine implementation, physical-chart validation or external human review. This agent edited only this review file for the delta task and changed no other project's source, runtime, configuration, owner or hold.

## Addendum: integrated revisions and supplied-state bridge

At the root agent's request, re-read these later local snapshots:

| File | SHA-256 | Git blob |
|---|---|---|
| `EXPONENTIAL-EXPRESSION-THEOREM.md` | `1d0d621f022d0a1709a7ff7633d1ae00c65e78bb70189c34903dd79dff1ec7fb` | `86fb17abf686db3704a507d71ccb61bc24766fc8` |
| `research/COMPACT-DELTA-THEOREM.md` | `df4a070a94d4ad65cb568f0025b07d2a947cfe17b5255acd84a7b1a3f13bbc8a` | `5e5b385e7fb26245cd28ab28c0b9d609c900eabe` |
| `research/COMMONS-COMPILER-BRIDGE.md` | `53eb428e0ca11edbf43fd7fe0e55a47ca6f7d91dad1c8705e31f5aa7d3a6554e` | `3f81e37b6f2a72caf9b2a48f31e7f3f2b09cdb3a` |

The main theorem now makes guarded atomic semantics, graph-variable scope, effective domain encoding and real Schanuel explicit. Those revisions address the specification issues in the earlier proof review and preserve its mathematical claims. Its Theorem 3 summary is supported by the reviewed compact theorem.

The revised compact theorem now states rational guard bounds, retains the constructive rational grid witness, warns that exact equality fits have zero robustness, and fixes residual scaling as part of the input contract. These additions are correct. The witness reasoning applies to its existential-only chart formula and has not been generalized to universal or alternating-quantifier formulas. No further mathematical correction to those additions is requested.

For the bridge, this addendum reviews the mathematical implication from the **reported** retained finite compiler and reference-measure coverage facts to the algebraic supplied-state corollary. It does not independently re-fetch or audit the pinned historical Python and manuscript files. Their exact hashes and historical controls remain attributed to the bridge author's source audit.

Under those reported facts, the algebraic extension is justified. Finite history/routing enumeration is combinatorial; algebraic ages can be sorted exactly; rate/probability/survival coefficient updates use algebraic arithmetic; and the resulting exponential intercepts and slopes stay algebraic. Theorem 1 then decides each analytic cell-density identity. Every nonempty open cell contains a rational box. Its witness is a genuine law distinction because continuity makes the nonzero density difference have a fixed sign on a smaller open neighborhood of positive measure. The reported positive continuous waiting-time model and almost-sure ancestral completion exclude missing boundary or singular masses.

One small hypothesis clarification is recommended: state explicitly that sampled leaves have age zero in a shared calendar origin, as the bridge's actual-input section says the retained compiler requires. The derived corollary currently says contemporaneous leaves without repeating the origin. If another common sampling age is allowed, first reduce it explicitly to the common zero origin; do not compare models with mismatched calendar origins under the retained zero-sample-time compiler. This is a specification sharpening, not a discovered counterexample under the intended same-model interpretation.

The distinction between a mathematical algebraic extension and the existing `Fraction` implementation is correctly retained. Source admission must still be separately established under the actual source validator and owner policy. The extension compares two supplied finite states; it does not search unbounded source sizes, construct complete charts, establish empirical observations or complete the model-specific G3/G4 obligations.

No additional jobs, builds, installs, staging, commits or runtime changes were performed for this addendum. Later edits to these files require a fresh pin; this addendum covers only the listed snapshots.
