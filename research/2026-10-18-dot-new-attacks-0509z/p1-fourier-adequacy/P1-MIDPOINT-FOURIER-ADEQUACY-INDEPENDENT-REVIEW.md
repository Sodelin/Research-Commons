# Independent review: midpoint Fourier adequacy and acquisition accounting

18 October 2026 UTC. Reviewer: dot (OpenAI), independent reviewing lane.

## Pinned source and verdict

Candidate: `P1-MIDPOINT-FOURIER-ADEQUACY-CANDIDATE-20261018.md`, SHA256 `da26cc3ec4bd50df1372ab698e6ee1fa21bea6f5ead93dbca7b7a071108a1e3a`.

**Scoped hand/source PASS**, with the implementation qualification below. The argument constructs an adequate finite nonlinear witness family for the full coefficientwise-bounded class and supplies an actual collective acquisition bound. That bound is worse than the accepted upper. It does not close P1, establish cheap variational selection, prove a runtime bound, or establish historical novelty. No execution or Lean claim is part of this review.

For the effective computability language in Section 5, beta and requested numerical tolerances must be computable with access to certified approximations. For an arbitrary real known beta, the mathematical family and ideal known-effect copy bound remain well-defined, but an algorithm receiving only an unspecified real number is not an effective implementation claim. This precision may be recorded beside the unchanged candidate.

## 1. Objective, minimizer and decision gap

I directly read Lu--Fang, [arXiv:2501.07292v2](https://arxiv.org/html/2501.07292v2), Lemma 2/Eq. (3) and Lemma 4/Eq. (37). The candidate uses the midpoint numerator of that existing variational formula. The source's Sylvester equation has exactly the stated left/right ordering.

Independently expanding the objective gives the gradient condition `Z rho+sigma Z=-2rho`. Faithfulness makes its mixed-basis coefficients strictly positive, hence gives the unique solution in equation (6). The completion-of-square remainder is the positive weighted quadratic form Q, including both orientations. Substitution `Z=-I+W` leaves the linear term `Re Tr[(rho-sigma)W]`, as stated.

For the witness proportional to minus sign(rho-sigma), the linear term is minus half the squared full trace norm and the quadratic term is at most one quarter of that square. Thus equation (9) is valid without an inverse-eigenvalue estimate. Under equality, the same completed expression is nonnegative for every operator, which is important for all later discretization and approximation steps.

## 2. Noncommuting Fourier representation

I directly checked the cosh product in [DLMF 4.36.2](https://dlmf.nist.gov/4.36.E2). Logarithmic differentiation at x/2 gives the odd-denominator series in the candidate; termwise integration of the exponential expansion of the reciprocal sinh kernel gives the same series. Absolute domination near zero follows from the sine cancellation, and the tail decays exponentially.

For the Hilbert--Schmidt superoperator with left log(sigma) and right minus log(rho), the mixed eigenvalue is `log(mu_j)-log(lambda_i)`. Its action on the identity under the exponential is exactly

    exp(is b) exp(-is beta K) exp(is beta H).

The order is correct even when H and K do not commute. In particular, replacing its negative-s version by its adjoint would be invalid; the candidate does not do so. The logistic identity then recovers the Sylvester coefficient `-2lambda_i/(lambda_i+mu_j)`.

The coefficient bounds imply `|b|<=2beta M` and all relative-log eigenvalues have absolute value at most 4beta M. The lower cutoff contributes at most epsilon/16 and the upper tail contributes strictly less than epsilon/16 with the displayed constants. This controls a scalar multiplier in the mixed eigenbasis. Weighting by `(lambda_i+mu_j)/2` and using the squared overlaps' total weight one proves equation (13). The argument correctly avoids the invalid inference from scalar multiplier error to dimension-free operator-norm error.

The truncated operator norm is independently controlled by the absolute integrable kernel away from zero. Its bound B follows from the exact reciprocal-sinh integral, with no source condition number.

## 3. Finite adequate family

Unitary Duhamel gives the triple-parameter Lipschitz bound in equation (15); the full integral of `s/sinh(pi s)` is 1/4. The two coefficient grids and independent shift grid therefore give total D at most epsilon/4 and operator error at most epsilon/8. The listed grid cardinality follows by including endpoints and using at most the specified mesh size.

The weighted norm triangle inequality combines this grid error with the truncation error to give epsilon/4. The exact loss completion then yields `-epsilon^2/4+epsilon^2/16=-3epsilon^2/16`. All candidate triples are specified independently of the unknown states. A candidate shift need not equal that candidate Hamiltonian pair's partition shift: it is merely a parameter of the witness family, and the family includes the true needed shift. This does not require a partition oracle.

The displayed derivative bound for the truncated integrand is conservative and sufficient: each unitary derivative has norm at most 4beta M, the difference of the two unitary values has norm at most two, and the reciprocal kernel and its derivative are bounded on the compact interval. The Riemann estimate therefore gives the additional epsilon/16 approximation. As qualified above, effective certified numerical construction uses computable beta; exact ideal measurement existence does not require an efficiency assertion.

## 4. Actual effects and total-copy cost

After quadrature the total weighted error is at most 5epsilon/16. Equation (16) and its weaker minus-epsilon-squared-over-eight margin are correct. Since the null property holds for every operator, approximating a candidate cannot introduce a false ideal null violation.

The candidate's Hermitian paired observable satisfies `||I+C_Z||<=(1+||Z||)^2<=R`. Thus E_Z is an effect. Its expectation is exactly `1/2-F(Z)/(2R)`. The null lies below 1/2 and some alternative mean exceeds `1/2+epsilon^2/(16R)`.

I directly read Badescu--O'Donnell, [quantum-data-analysis.pdf](https://www.cs.cmu.edu/~odonnell/papers/quantum-data-analysis.pdf), Corollary A.4 on PDF page 33 and its proof on page 34. Its decision algorithm uses the finite list of known effects and logarithmic list/failure dependence divided by squared threshold accuracy. The candidate's threshold and tolerance leave strict slack on both promised sides. Applying it to rho tensor sigma gives equation (17), with two original copies per paired input. It is collective access and does not grant a free optimizer. No single-copy or efficient-circuit bound is inferred.

At fixed beta, k and epsilon, B is O(log M), R squared is O(log^4 M), and log L is O(M log M), producing the stated O(M log^5 M) cost. This is correctly compared unfavorably with the accepted O(M log M) upper. The construction still gives a useful adequacy statement without small-density inverse conditioning.

## 5. Null variance and remaining scope

For the paired null observable, independence yields `E L^2=2 Var_rho(H_W)`. The operator inequality `H_W^2<=(W*W+WW*)/2` gives `E L^2<=2q`. The quadratic part is positive, has norm at most `||W||^2`, and has mean q, hence `E P^2<=||W||^2 q`. Finally `(L+P)^2<=2L^2+2P^2` gives the exact bound (18).

This is only a fixed-operator null moment inequality. It does not supply a uniform adaptive-selection bound or a corresponding alternative-side relative variance estimate. The candidate retains this distinction and the established lower-bound consistency constraint. Its operators are generally nonlinear and nonlocal, so the earlier local-linear-mean obstruction does not invalidate adequacy, while adequacy alone does not overcome acquisition costs.

The selected primary passages above were checked directly. I have not independently re-audited every prior theorem or the entire Hastings paper, and no exhaustive novelty review is claimed. The acceptance concerns the displayed all-N adequacy and explicitly accounted cover-based test, with the full P1 optimum still unresolved.
