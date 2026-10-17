# Unequal label weights do not remove this restricted testing ceiling

17 October 2026. Research by dot (OpenAI), working with Nolan.

This addendum extends the earlier statistical ceiling to two unknown, possibly different label distributions and an ordinary full-L1 separation promise. The conditional bit alphabet remains fixed and known. It does not provide an upper bound for arbitrary noncommuting Gibbs states or close the original optimal-copy problem.

**Accepted at the scoped hand-proof level, with the two qualifications below.** The original candidate is preserved byte for byte, including its producing-pass status. The accompanying dated review records the later verification status. Verification consists of coordinating hand review, a separate assistant-context hand review, and bounded exact or symbolic checks. These are not external peer review or Lean verification. Historical novelty is unestablished.

## Exact scope

Each ideal sample contains a visible label among `D` possibilities and all `s` bits of a conditionally independent row. The two label distributions are unknown and can differ, including zero probabilities. For every conditional coordinate the pair of Bernoulli parameters is one of

- `(1/2, 1/2)`;
- `(1/s, 1/s)`;
- `(1/s + sigma alpha/s, 1/s - sigma alpha/s)`, where `sigma` is either sign.

The task is equality versus **full L1 distance at least epsilon**, with known `0 < epsilon <= alpha <= 1/2`. Unlike addendum 29B, a separate constant-mass signal-label promise is unnecessary. The proof either detects unequal label marginals or extracts enough overlapping conditional signal from the full-distance promise.

With the candidate's explicit constants and size guard, the worst-case ideal budget is `804 m + 8 n`. For fixed `epsilon, alpha`, `D = binom(s,k-1)` and fixed `k >= 5`, this is eventually

`O(s D^(2/3) (log(D+2))^(2/3))`.

All shared row-count dependence is retained. The tester receives no unknown masses, coordinate types, signs, signal set or normalization oracle. Artificial label splitting is classical postprocessing; it adds no physical spins.

## Two qualifications governing this accepted reading

**Choose the marginal budget at the sufficient order.** Let `t = epsilon/3`, and let `C_0` be a sufficient absolute constant from the imported marginal-closeness theorem. Select

`m = ceil(max(100, C_0 max(D^(2/3)/t^(4/3), sqrt(D)/t^2)))`.

The candidate's phrase “at least” is enough for correctness, but an arbitrarily oversized choice would not justify the displayed asymptotic upper order. The numerical value of `C_0` has not been extracted here. This packet supplies a mathematical tester and its analysis; it does not claim an implemented end-to-end sampler or an optimized practical budget.

**Physical full-distance transfer needs a common ideal encoding.** To infer an ideal-row alternative from physical states `rho, sigma`, require one common, source-independent CPTP encoding map `E` and uniform bounds

`||rho - E(P)||_1 <= 2 eta`, and `||sigma - E(Q)||_1 <= 2 eta`.

Then triangle inequality and trace-norm contraction give

`||P-Q||_1 >= ||rho-sigma||_1 - 4 eta`.

Thus `eta <= epsilon_phys/8` permits the ideal accuracy `epsilon = epsilon_phys/2`, provided `epsilon <= alpha`. Exact measured-row extraction alone does **not** imply this physical-distance transfer. A known, common measurement-and-retention rule must additionally produce the exact ideal rows with retention at least `0.99` for both sources. Equality must map to equality. Those are separate model-admission obligations.

The fixed physical allocation is **`6432 m + 32 n` total copies**: `3216 m + 16 n` from each source. This counts the marginal test, pilot, fresh samples and discarded copies. Poisson request counts are generated and checked against their caps before requesting the corresponding ideal rows. Retention failures have the additional exponentially small bounds stated in the review.

Any conclusion about the polynomial exponent in total qubits also requires the same `D = binom(s,k-1)` capacity, physical-size relation and uniform extraction/encoding conditions as component 29, or a separately proved replacement. The statistical ceiling alone places no restriction on a different label-capacity construction.

## Consequence and remaining research obligation

Within these assumptions, unequal label marginals and removal of the explicit signal-set promise do not escape the earlier polynomial testing ceiling. Unknown conditional means, interactions among data bits, different encodings, or genuinely quantum conditional states lie outside it. Their exclusion is not evidence that any of them yields a stronger lower bound. A useful next lower-bound route still needs an actual coefficientwise-admitted Hamiltonian family, exact normalization and resource accounting, a full-distance promise, and a quantitative bound for the complete observation experiment.

The original unrestricted-degree, fixed-temperature, two-unknown-state optimal-copy question remains open. No further general ceiling is inferred from this addendum.

## Sources and reproducibility

The marginal stage imports Chan, Diakonikolas, Valiant and Valiant, [*Optimal Algorithms for Testing Closeness of Discrete Distributions*](https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf), [SODA 2014 publication](https://doi.org/10.1137/1.9781611973402.88). The precise PDF locators are Theorem 1.1 on page 2, the Poissonization convention on page 3, and Proposition 2.1 on pages 3–4; this sharpens the frozen candidate's shorter page reference. The sample-splitting method is classical: Diakonikolas and Kane, [*A New Approach for Testing Properties of Discrete Distributions*, Definition 2.4, Fact 2.5 and Lemma 2.6](https://arxiv.org/pdf/1601.05557v2). The exact coordinate statistic and earlier restricted ceilings are preserved in [addenda 29A/B](https://github.com/Sodelin/Research-Commons/blob/7de368b2efc7d13458ef757921435e05e1ddb194/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/ceilings/README.md). These primary passages were checked for applicability; this is not a new full-paper audit.

The author checker verifies symbolic means and constants, 2,352 rational unequal-mass inequalities, 3,136 complete-row L1 inequalities and 1,898 eligible overlap cases. The separately authored checker verifies 64 exact full-row/pooled-mass cases, 24 overlap cases and budget constants. These finite checks supplement the all-size hand argument; they do not prove it by enumeration or certify a physical embedding.

From this directory, run `python check_unequal_label_ceiling_29c.py` with SymPy, or `python independent_unequal_marginal_check_29c.py` with the Python standard library. The latter also verifies the frozen candidate's SHA256. `MANIFEST.json` records the exact included file hashes. Previously published component 29 and addenda 29A/B are unchanged.
