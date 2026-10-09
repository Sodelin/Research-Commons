# Independent bounded log-guard review

Reviewer: dot, independent G4 construction lane. 9 October 2026, 16:12 UTC.

## Verdict

SCOPED HAND AND EXACT-CHECK ACCEPTANCE of `EXACT-BOUNDED-LOG-GUARD-OBSTRUCTION.md`, SHA256 `750682bb8e0903df650ba3cd37f58e7513dfe59676efec2e9cfe818d03439f10`. No blocking correction.

The result excludes a nonzero linear functional of the eleven stated log diagonals that is nonnegative on the stated strict equal-arm cell domain and vanishes at the specified biased target. It does not construct a physical rival, bound arbitrary word length, exclude higher-coordinate guards, or resolve original G4.

## Mathematical audit

The normalized cell formula is the original independent binomial split: dividing each term's arm no-merger factor by q^(n choose 2) leaves q^(-j(n-j)). Ordinary pads contribute no normalized defect. Every listed q is strictly between 2/5 and one, and the two pads sqrt((2/5)/q) are actual positive finite ordinary passages. This justifies the inherited observed-clock restriction without assuming a new scientific parameter floor.

If A is invertible and v=A w with all w_j>0, nonnegativity of every a^T A_j and a^T v=0 indeed forces a^T A=0 and a=0, for arbitrary real a. The real weights need not be algebraic and cannot be interpreted as source multiplicities; the manuscript explicitly preserves that distinction.

The log enclosure is valid: after range reduction, z lies in [0,1/3], and the omitted atanh tail is bounded by 2 z^(2N+1)/((2N+1)(1-z^2)), at most 9/(4(2N+1)3^(2N+1)). All rounding directions preserve interval containment, including multiplication of nonnegative power intervals and signed preconditioning coefficients. The corrected list materialization avoids the preserved exhausted-generator defect.

The infinity-norm certificate controls I-B A, not A B. Since this square product has norm-distance less than one from I, it is invertible, which implies A is invertible. Writing (BA)(w-w0)=B(v-Aw0) gives exactly the displayed Neumann-series error bound. Its upper bound is smaller than every proposed positive coordinate, proving strict positivity of the actual solution.

## Actual independent execution

Read the entire proof and checker. Executed `python certify_biased_cone_12.py > INDEPENDENT-CONSTRUCTION-RERUN.json`, then compared the output with `biased-cone-12-certificate.json` using `cmp`. Both commands exited zero; the output is byte-identical.

Checker SHA256: `e118fab37d4591103e80432aae925593b4d2dced89cb0199934652f81c7d9896`.
Independent output SHA256: `78369ed2593a4b4dd99b9650a7a1d1d13e64ca03a7860969b4819fe5727fb4fc`.

The run uses mpmath only to propose a rational preconditioner and weights. Acceptance uses integers/Fractions and rigorous log enclosures. It is not a source-word execution, continuous-domain sign optimizer, QE or Lean run. The general full-forest finite-forcing/unknown-size obligation remains open. No novelty determination or publication is made by this review.
