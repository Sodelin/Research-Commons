# Independent proof and scope review: compact transfer certificate

Reviewer: `/root/current_stat_scope_audit/certificate_proof_review`, 2026-09-30 UTC. Independently derived the certificate before reading the implementation. A separate delegated termination check was supplied by `/root/current_stat_scope_audit/certificate_proof_review/threshold_review`. This review makes no historical novelty claim.

## Reviewed snapshot and remit

| File | SHA-256 |
|---|---|
| `compact-certificate.md` | `acf5e5c5c4d4a7ceb4c5e07fa1dd5394513d454d8b5734aac53f935a60b082a9` |
| `compact_certificate.py` | `7ec14e3d80ed534ba35591b4b49ad1c70ff25706d9afb19b3352c5ff32d4b322` |

The mathematical theorem, its decision interpretation, finite-data confidence argument, refinement and effectivity statements were reviewed for the complete stated parameter class. The Python file was read to check agreement of notation and arithmetic contracts with that theorem. I did not execute the code or its controls, and do not replace the separate implementation/control review. No source or implementation edits, commits or pushes were made by this reviewer.

## Verdict

The reported interval and the uniform upper guarantee for the actual returned kernel are sound under the explicit premises. The written version addresses the principal hazards: a single parameter-independent stochastic kernel; normalized finite probability laws; errors simultaneous over the complete grid; TV envelopes for all distances at most the covering radius; exact feasible primal/dual witnesses; and a common confidence event when stages are inspected repeatedly.

This is a constructive result within its finite-alphabet, effective-access class. It does not establish the scientific correctness, sample provenance, cover or modulus premises, arbitrary infinite-alphabet transfer, biological reconstruction, or universal finite decisions at equality.

The final manuscript incorporates the minor terminology correction to a compact **product of simplexes**, and lists grid points without duplicates for the finite-prior decision interpretation. The lower-semicontinuity argument for attainment is correct. The final publication-path and fixture-metadata changes were also read; they do not alter the theorem or its arithmetic.

## Independent derivation

Use the convention `TV(p,q)=1/2 sum |p-q|` and the direction from source `P` to target `Q`, with `KP(y)=sum_x P(x)K(x,y)`. Nonnegative stochastic rows give TV contraction. Consequently, for every feasible kernel and every grid index,

```math
\left|\operatorname{TV}(KP_i,Q_i)-\operatorname{TV}(K\widehat P_i,\widehat Q_i)\right|
\le \rho_P+\rho_Q=\rho.
```

The maxima over grid indices, and then their minima over kernels, therefore differ by at most rho. Restriction of the global parameter class to its grid gives the lower endpoint. For each arbitrary theta, a covering index and the same returned kernel give

```math
\operatorname{TV}(KP_\theta,Q_\theta)
\le \omega_P(r)+\rho_P+U+\rho_Q+\omega_Q(r).
```

Clipping to the TV range [0,1] proves exactly the written interval. This proof covers all theta, not merely the fixtures. It is uniform over every stochastic kernel on the joint law-error event, so fitting the returned kernel to those data creates no additional independence requirement.

For normalized laws, TV is the supremum of `(Q-KP) dot f` over `0<=f<=1`. Put `v_iy=lambda_i f_i(y)`. Minimization of the weighted linear objective over each stochastic row gives

```math
g(\lambda,v)=\sum_{i,y}v_{iy}\widehat Q_i(y)
-\sum_x\max_y\sum_i\widehat P_i(x)v_{iy}.
```

For every kernel K, this minimum is at most its weighted test-function discrepancy, which is at most `sum_i lambda_i TV(K Phat_i,Qhat_i)` and hence its largest grid discrepancy. Thus `g<=dhat`; replacing g by `max(0,g)` is valid. The signs, maxima and factor-of-two convention in the text and exact evaluator agree. Finite compact convex minimax also supplies strong duality; certificate validity requires only the elementary weak-duality argument.

The decision witness is valid. Under prior lambda and loss `1-f_i(a)`, the displayed source term is its optimal expected utility; the target identity action supplies the displayed target utility. The target optimal utility can only be larger. Source Bayes risk minus target Bayes risk is therefore at least the raw dual objective. Perturbing the two laws changes this bound by at most rho. Whenever `L>rho`, the raw objective equals L and the claimed positive true Bayes-risk disadvantage follows. For arbitrary target decisions and losses in [0,M], TV bounds their pointwise risk discrepancy by M times the uniform upper certificate.

## Sampling and repeated inspection

Each empirical coordinate is an average of N IID Bernoulli indicators. Its two-sided error probability is at most `2 exp(-2 N b^2)`. Union over exactly `J=m(|X|+|Y|)` coordinates gives the stated simultaneous event of probability at least `1-alpha`, without independence between coordinates or law blocks. On it, half the coordinate-error sum is at most `|X| b/2` or `|Y| b/2`; capping either TV bound at one is valid. These bounds are conservative, including for singleton alphabets, but sound.

The written centered-Bernoulli moment-generating-function proof is correct: the tilted variance is at most 1/4, which bounds the log moment-generating function by `t^2/8`. The integer power-of-two exponent and upward rational square-root construction are also conservative: `log(2J/alpha)<=c` when `2^c>=2J/alpha`. The empirical denominator condition checks count consistency, not IID provenance.

The fixed-stage interpretation and cost of `2mN` observations are appropriately qualified. For repeated or adaptive inspection, a summable stage failure budget gives one common confidence event; separate fixed-stage guarantees at a repeatedly reused alpha do not. Fresh blocks with the stated conditional IID and fixed conditional sample-size conditions support the written adaptive-grid qualification.

## Refinement and boundary cases

For the reported endpoints a,b, exact feasibility implies

```math
0\le b-a\le (U-L)+2\rho+\omega_P(r)+\omega_Q(r).
```

On a common validity event, pathwise vanishing of these terms makes both endpoints converge to the true deficiency. Every strictly separated threshold then resolves after finitely many stages. Nested grids are unnecessary. Effective nets, sample/evaluation access and shrinking certified optimization gaps are substantive premises; compactness alone supplies none of their algorithms or resource bounds. Numerical proposal success alone does not establish shrinking exact gaps. Fixed rational resolutions can leave accuracy floors, as the text now states.

Independent adversarial checks confirm the boundary qualifications and constants:

* With a singleton source and two opposing deterministic binary targets, deficiency is 1/2. The fair-coin primal and `lambda=(1/2,1/2)`, `v_0=(1/2,0)`, `v_1=(0,1/2)` yield U=L=1/2, confirming the dual orientation. Any positive shrinking valid rho keeps an equality threshold at 1/2 unresolved at every finite stage.
* With the same singleton source and identical deterministic targets, U=L=delta=0. Positive shrinking rho yields `[0,rho]`, which does not finitely certify exact zero. Known structural equalities can provide separate exact certificates.
* For `Theta=[0,1]`, singleton source and `Q_theta=(theta,1-theta)`, the true global deficiency is 1/2. The two-point cover and approximate laws in the written control have estimated deficiency 1/8; target uncertainty 1/8 and cover term 1/4 are needed to recover the global upper bound 1/2.
* The sum of both law errors is necessary in general. Take true source laws both Bernoulli(1/2) and true targets Bernoulli(0), Bernoulli(1). Estimate the sources as Bernoulli(1/2-rho_P), Bernoulli(1/2+rho_P) and the targets as Bernoulli(rho_Q), Bernoulli(1-rho_Q), with their sum at most 1/2. True deficiency is 1/2, while the estimated deficiency is `1/2-rho_P-rho_Q`. Reversing the exact and approximate families also attains the corresponding lower perturbation correction.

The discrete Dirac-target warning is mathematically correct: a TV modulus tending to zero forces a discrete deterministic target label to be locally constant, and therefore constant on a connected parameter class. A changing label requires justified strata, margins, abstention, or another target experiment.

## Scope of acceptance

No substantive mathematical correction is required for this snapshot. Acceptance is conditional on the declared model, cover, envelope and joint law-error premises, and does not certify those premises from the empirical tables. The fallback preserves arithmetic validity but promises no optimization accuracy. Separate implementation execution and empirical-domain validation remain distinct obligations.
