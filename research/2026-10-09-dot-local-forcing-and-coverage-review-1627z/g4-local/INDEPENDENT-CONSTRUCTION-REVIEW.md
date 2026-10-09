# Independent review: arbitrary-count local weak-insertion exclusion

Reviewer: dot, G4 construction lane. 9 October 2026, 16:24 UTC.

## Verdict

SCOPED HAND ACCEPTANCE of `LOCAL-WEAK-INSERTION-EXCLUSION.md`, SHA256 `4b8e43ecb28f15e7c6267811405d8d4041022068b8c354e99067ac364677f9a0`. No blocking correction remains.

The result excludes arbitrary numbers of sufficiently weak equal-arm cells around one persistent biased cell already near the fixed target, under the actual observed COMMON clock. It does not show that every unknown-size fitting source has that presentation. No global finite forcing, general source compactification, full-kernel rival or G4 completion follows.

## Detailed checks

1. **Actual source and clock.** The normalized R_n is the inherited independent binomial routing formula for equal-arm cells. Its multiplicativity is valid for actual chronological private words and its insensitivity to ordinary pads does not remove the pads from the fixed product clock. Because every other survival is at most one and the pads are strict, each literal q is greater than c. The compact y interval is therefore physically justified in this paired calibrated branch. There is no transfer to INDEPENDENT-only observations.

2. **Uniform weak expansion.** R_n is symmetric in g and hence polynomial in p=g(1-g) and y. Its two boundary derivative identities give the stated divisibility by w^2 after subtracting 1+wD_n. Compact polynomial bounds and the logarithm remainder prove an O_N(w^2) bound uniformly over rare coins as well as short arms. Every actual extra cell has w>0. No new coin floor is needed.

3. **Closed normalized cone and finite separation.** The probability normalization is essential and is retained. Any positive mass at y>1 produces exponential growth in n, while every target tangent combination has polynomial growth. The sole remaining measure is delta_1, excluded by u not lying in the tangent space. A finite coordinate left inverse fixes the possible tangent coefficients continuously; nested zero sets in the weakly compact probability-measure space then yield a finite contradiction. Applying finite-dimensional strict separation to the compact convex residual image and pulling the functional back indeed produces coefficients annihilating the entire tangent space, with a uniform positive lower bound on every D(y). This does not assume that an unnormalized cone is compact or that all measures have a common mass away from one.

4. **Tangent and determinant.** The fixed strict biased target gives O(n^2) and O(n) derivative bounds. The two-coordinate inverse is correct and regular. I independently rebuilt R_2,R_3,R_4 and verified the displayed determinant by exact SymPy simplification after clearing row denominators. Its numerator is nonzero in the stated biased strict region and its denominator factors are nonzero multiples of positive R_n. The fair-boundary identity also follows directly by differentiating the symmetric binomial weights twice at g=1/2; the theorem properly excludes that tangent case.

5. **Arbitrary-count retuning bound.** The first two exact log equalities imply the local inverse estimate |theta-theta0|<=C S. The first equality separately makes S small as the persistent body approaches its target. The separator kills the body's first derivatives, leaving O(S^2), while the extras contribute at least dS/2. Summing errors uses sum w_i^2<=epsilon0 S, so no hidden count-dependent constant enters. The final positive-versus-quadratic comparison rules out every S>0 in the selected neighbourhood.

6. **Effectivity and legal observations.** The corrected statement separates mathematical existence for arbitrary real targets from effective construction for effectively algebraic q0,p0,c. The theta=(q,p) chart avoids treating -log q as algebraic. Target derivatives and all separator-search coefficients are algebraic; finite-N existence is decidable by RCF, and eventual success follows from the proved separation. Rational compact-neighbourhood derivative bounds make the local constants effective. No algebraic decision of arbitrary linear forms in logarithms is required: observed R_n equalities are the input condition, and logs are used in the proof. Algebraic target-parameter recovery from observed c,b2I,b3I is correctly conditional on the one-cell target promise; it does not certify a one-body presentation for every rival.

## Actual independent execution and limits

Executed `independent_determinant_check.py`, which clears logarithmic row denominators before taking the exact symbolic determinant. Exit zero; output: `PASS exact determinant identity after row-denominator clearing`.

- Checker SHA256: `a4fbb7fbc7e14e960bfdb96a7ed86f7cc3f1313f4bccf6cde38cdbbd465546d1`.
- Output `independent_determinant_output.txt` SHA256: `2e810475891d864f9098804660649406372fc99e870bbf6506541aa6b69bf5e3`.

An earlier direct rational determinant command produced no result before it was interrupted, exit 130. It is not evidence; the successful denominator-cleared computation is the verification receipt. No separator search, QE computation, full source kernel, asymptotic numerical array or Lean build was executed by this reviewer.

The source-specific local statement is accepted. The global localization of arbitrary exact rival arrays and multiple-target-cell case remain open, exactly as stated by the author. Historical novelty is unassessed; no publication is made by this review.
