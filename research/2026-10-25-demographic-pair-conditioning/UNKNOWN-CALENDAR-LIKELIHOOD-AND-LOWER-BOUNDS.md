# How much is conservative certification, and how much is weak information?

Author: dot (OpenAI), 25 October 2026. Classical sufficient-statistic, Fisher-information and two-point-testing analysis with an executed synthetic inference benchmark. No novelty, empirical applicability, uniform MLE coverage, or globally verified optimization claim.

## 1. Prior overlap and unchanged observation

The sign-variation information-count framework is classical, and the older repository bridge already implies finite-length sufficiency on this bounded no-migration subclass; see UNKNOWN-CALENDAR-PRIOR-REVIEW.md. The contribution of this pass is an actual conditioning/inference comparison, not another claimed identification principle or another arbitrary tiny calibration box.

Keep exactly TWO copies, THREE conditionally independent JC sites sharing ONE pair genealogy per locus, known clock s=1, and independent loci. Write x=exp(-T). Conditional on T, a site's base-match probability is q=(1+3x)/4. The number K of matching sites therefore has a binomial(3,q) mixture law. Its probabilities for K=0,1,2,3 are

    p = (1/64) [[27,-81,81,-27],
               [27,27,-135,81],
               [9,45,27,-81],
               [1,9,27,27]] (1,phi(1),phi(2),phi(3))^T.

K is sufficient for the full three-site pair data: for fixed K, matching-site positions and nucleotide identities have parameter-independent probabilities. In particular, this compression does not discard demographic information. Independent-locus category counts are multinomial(N,p).

The two-epoch source is z=(initial hazard x, tail hazard y, cut t), with its earlier explicit moment formula. Hereafter x in z denotes the hazard, not exp(-T).

## 2. Source-conditioned information: a genuinely weak direction

At z0=(1,2,1), the four status probabilities are approximately

    (0.086264387, 0.241583355, 0.332289397, 0.339862860).

Using the analytic derivatives of the complete sufficient law, the per-locus Fisher matrix is

    F = J_p^T diag(1/p) J_p.

Its floating eigenvalues are approximately (0.0000242556, 0.00783779, 0.220961), a condition ratio about 9,110. The normalized weakest direction is approximately (0.01922,0.92134,0.38829): tail hazard and cut can compensate while changing initial hazard very little. The diagonal of F^(-1) is approximately (25.6338,35015.1451,6318.9480).

Accordingly the local regular asymptotic standard deviations at N=10^7 are approximately (0.001601,0.059174,0.025138). These are source-local Fisher diagnostics, NOT finite-N confidence radii, minimax guarantees, or guarantees for biased/clipped estimates. The conditioning calculation explains why inferring an unknown cut is substantially harder here than simply observing that the map is injective.

## 3. A rigorous two-source finite-budget obstruction

For two actual sources with category laws P0,P1, a certified upper bound c on chi-square(P1||P0)=sum_k (p1_k-p0_k)^2/p0_k yields

    KL(P1||P0)<=c,
    TV(P1^N,P0^N)<=sqrt(N c/2).

If their parameter sup distance is >=2eta, the strict eta-success balls are disjoint. An estimator with success at least 0.95 at BOTH sources supplies a test with total error at most 0.10. Thus TV>=0.90 is necessary, and consequently

    N >= 1.62/c.

This is a necessary bound, not a sufficient achievable sample size. Because sufficiency of K is exact, the obstruction also applies to methods using every original nucleotide identity and site position.

### Same tiny box and SAME target as the earlier upper certificate

Keep b=1/16384 and eta=b/2=1/32768. The sources are z0=(1,2,1) and

    z1=z0+b*(0.02055418,1,0.41996702).

The decimals are exact rationals; BOTH sources are in the original c+[-b,b]^3 box. Their tail hazards differ by exactly 2eta. The direction was suggested by the nuisance-adjusted Fisher calculation, but the bound uses exact source laws, not its asymptotic approximation.

Outward rational-interval arithmetic proves

    chi-square(P1||P0) <= 531887851569 / 5000000000000000000000000,
    N >= 15,228,774,216,419.

The earlier uniform sufficient budget was 239,624,413,446,670,153 loci, roughly 15,735 times this necessary bound. There is therefore a large unresolved gap between certified sufficient and necessary budgets. This gap alone does not establish inefficiency relative to the unknown optimum, but the small-target difficulty is NOT merely an artifact of its Hoeffding calculation: this fixed two-source test already needs trillions of loci. The remaining upper/lower gap is unresolved; a lower bound does not prove a better attainable budget.

### Broader separated chart and a coarser target

For the actual likelihood benchmark below, declare the much broader chart

    x in [0.5,1.5], y in [1.75,3], t in [0.5,1.5].

It has positive rates, minimum jump 0.25, minimum finite duration 0.5 and bounded cut 1.5. Compare z0 with the rational source

    z1=(1.0033542746, 2.2, 1.0735205285).

Numerical nuisance fitting motivated this rival; its optimality is unnecessary. The exact final pair has tail-rate separation 0.2, so eta=0.1 strict success regions are disjoint. The certified bound is

    chi-square(P1||P0) <= 7857862935151133431 / 10^25,
    N >= 2,061,630.

This changes the resolution and allowed chart explicitly. It is not a direct replacement for the earlier tiny-target uniform budget. It shows a source-conditioned million-locus obstruction even at a much coarser precision in this fixed three-site experiment.

## 4. An actual seeded likelihood-fit benchmark

benchmark_unknown_calendar_likelihood.py generated multinomial counts directly from the sufficient law at z0, seed 20261025. This is exact-model synthetic sampling, not genealogical Monte Carlo, biological data, or independent sites masquerading as independent genealogies. Each count represents one independent shared-genealogy locus.

For each of N=10^4,10^5,10^6,10^7, 60 replicates were generated (240 fits total). Each fit minimized the multinomial negative log likelihood up to a constant, using analytic derivatives, the broad box above, and three fixed starts. One of the three fixed starts was the generating truth (1,2,1); this truth-containing initialization can make single-source convergence diagnostics optimistic and is not evidence of a deployable optimizer that knows the source. The best numerical objective was retained. NumPy/SciPy already present in the workspace were used; no installation occurred.

| Loci N | Tail-hazard RMSE | Cut RMSE | Fits with all errors <0.1 | Boundary fits |
|---:|---:|---:|---:|---:|
| 10,000 | 0.6687 | 0.2047 | 2/60 | 51/60 |
| 100,000 | 0.4515 | 0.1400 | 7/60 | 34/60 |
| 1,000,000 | 0.2244 | 0.0831 | 20/60 | 3/60 |
| 10,000,000 | 0.05333 | 0.02311 | 55/60 | 0/60 |

At low counts, boundaries frequently determine the fitted answer; a boundary estimate is not evidence the biological parameter is actually at that bound. At ten million loci the empirical errors are compatible with the Fisher scale, but 55/60 is neither a proven 95% success rate nor uniform coverage. Sixty replicates are a bounded diagnostic, not a precision coverage study.

Raw optimizer failure flags occurred in 4,3,3,0 fits respectively and remain visible in the saved record. All fitted points, including flagged ones, had floating projected-gradient sup norm below 5.74e-9 on the per-locus objective. This diagnoses near-stationary stopping/roundoff rather than establishing global optimality. Three independent exact-law fitting controls returned maximum parameter errors about 1.9e-8, 9.2e-10 and 2.5e-6. These are additional implementation checks, not a global solver certificate. All 240 counts, fitted parameters, objective values, flags and projected gradients are retained for inspection.

## 5. Evidence files and the justified conclusion

- benchmark_unknown_calendar_likelihood.py and unknown-calendar-likelihood-benchmark.json: reproducible floating synthetic inference and conditioning diagnostics, with full count records.
- certify_unknown_calendar_testing_bound.py and unknown-calendar-testing-certificate.json: standard-library rational-interval probability and chi-square checks for BOTH pairs. The script reuses the previously saved outward exponential/interval implementation; it does not depend on NumPy to certify the fixed rational candidates.
- The written testing inequality is classical; it is not formally verified. The exact interval engine itself remains subject to review. No bounds are claimed on probability model misspecification, mutation-rate uncertainty or linked loci.

The practical mathematical finding is a distinction, not a victory claim: there is a large unresolved gap between certified sufficient and necessary budgets, and this three-site unknown-cut experiment has a real tail-hazard/cut compensation direction. The coarse-target synthetic fits do not demonstrate an attainable improvement at the original tiny target. Actual inference at a coarse target improves markedly with millions of loci, while the earlier microscopic target remains provably demanding even for the best possible method. A useful next design investigation would change locus length or impose a scientifically justified calibration, rather than repeatedly shrinking an arbitrary box and reporting a larger certificate. Such a changed design must be accounted for explicitly; it cannot be advertised as an improvement under unchanged observations.
