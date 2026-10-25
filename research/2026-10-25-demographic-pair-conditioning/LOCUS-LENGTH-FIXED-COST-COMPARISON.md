# Longer loci versus more independent genealogies at fixed nucleotide cost

Author: dot (OpenAI), 25 October 2026. Source-conditioned design analysis, exact two-source controls and synthetic inference benchmark. Classical information/design/testing machinery; no novelty, practical biological recommendation, global optimum, uniform MLE coverage, or general demographic closure.

## 1. Explicitly changed experiments, not a hidden budget improvement

Retain one population, two contemporaneous copies, known stationary clock-JC with s=1, positive two-epoch hazards, one unknown cut, and independent nonrecombining loci. CHANGE the shared-genealogy site count L per locus. A locus costs 2L nucleotide calls; a budget B supports N=floor(B/(2L)) independent genealogies. Sites within a locus do not become independent genealogies when L increases. Longer L is not automatically biologically feasible: recombination within a locus, dependence between loci, or mutation/demographic misspecification can invalidate this comparison. This is model-conditional design sensitivity, not demonstrated empirical accessibility or a practical sequencing recommendation. The normalization s=8mu/3=1 fixes the known mutation/time scale; uncalibrated rate or time units are not being inferred.

Use source z0=(initial hazard x, tail hazard y, cut t)=(1,2,1) and the previously declared broad chart x in [0.5,1.5], y in [1.75,3], t in [0.5,1.5]. It has minimum hazard jump 0.25 and cut width 0.5. The observed cost here counts only nucleotide calls, NOT per-locus laboratory overhead, sequencing errors, recombination, data-cleaning effort or computational cost.

The earlier sharp cutoff and prior review establish the readout's structural meaning. Sign variation, finite-locus sufficiency, sufficient statistics, Fisher information, data processing and two-point testing are all prior/classical methods. This packet's delta is an actual same-cost changed-design comparison. The corrected earlier packet explicitly retains a LARGE UNRESOLVED necessary/sufficient budget gap; no claim of wasted budget relative to optimum is resurrected here.

## 2. Complete sufficient readout and stable forward computation

At any L, K=number of matching base pairs among the L sites is sufficient. Given genealogy time T, K is binomial(L,q(T)), q(T)=(1+3exp(-T))/4. Conditional site positions and nucleotide identities given K have parameter-independent probabilities, so the complete sequence likelihood loses no information when compressed to K.

For k=0,...,L,

    p_k = E[binom(L,k) q(T)^k (1-q(T))^(L-k)].

For exact interval checking, expand

    p_k = binom(L,k) 3^(L-k)/4^L
          sum_(i=0)^k sum_(j=0)^(L-k)
           binom(k,i) 3^i binom(L-k,j) (-1)^j phi(i+j),

where phi(0)=1. This is an exact polynomial-moment formula, but plain floating evaluation suffers cancellation at large L.

The floating design/likelihood engine instead integrates POSITIVE binomial probabilities against the two-piece genealogy density. It uses 96-point Gauss–Legendre quadrature before the cut and 96-point Gauss–Laguerre after it. Let g(T) be the vector of conditional K probabilities, A its pre-cut integrated contribution, R its post-cut contribution, and v=y(T-t) on the tail. Analytic derivatives are integrated as

    partial_x p = integral_pre g(T) f(T)(1/x-T)dT - t R,
    partial_y p = integral_tail g(T) f(T)(1-v)/y dT,
    partial_t p = (y-x)[R-exp(-xt)g(t)].

The last expression includes the moving-boundary density jump; dropping that term would give incorrect information. The derivative-score formulas are exact continuous expressions; their quadrature implementations are numerical approximations.

At the source, comparison with 192-point quadrature found probability/Jacobian differences around 1e-14 through L=96, around 2e-13 at L=128, rising to about 2.5e-10 at L=256. Probability normalization and zero derivative-sum checks are saved. Agreement of two quadratures is a numerical diagnostic, NOT a rigorous error bound. The separate high-precision rational polynomial controls do not depend on quadrature.

## 3. Source-local Fisher information per nucleotide call

For one locus F_L=J_p^T diag(1/p)J_p. The fixed-cost information is approximately B F_L/(2L). Thus the relevant regular asymptotic variance coefficient is 2L diag(F_L^(-1)), not merely the per-locus information.

| L | Initial-hazard variance × B | Tail-hazard variance × B | Cut variance × B |
|---:|---:|---:|---:|
| 3 | 153.8 | 210,090.9 | 37,913.7 |
| 12 | 89.1 | 15,676.3 | 3,092.6 |
| 64 | 266.3 | 5,939.9 | 1,126.2 |
| 128 | 484.3 | 6,757.9 | 1,094.0 |

These are floating source-local regular-asymptotic diagnostics, NOT finite-N confidence statements. Among the tested lengths, tail-hazard information per call improves dramatically over three sites, then has turned down by L=128; initial-hazard information favors much shorter loci. No single objective-free optimum exists. The sparse tested grid does not establish the best integer L or an optimum over mixed-length experiments. Lengths 1 and 2 cannot identify all three parameters in the unrestricted genuine two-epoch chart; their information matrices have insufficient rank for full joint inference.

## 4. Independent-locus replication remains necessary: a rigorous all-L obstruction

Even if each locus revealed its COMPLETE genealogy time T, varying only tail hazard y gives score

    score_y(T)=1_{T>=t}(1/y-(T-t)),
    E[score_y(T)^2]=exp(-xt)/y^2.

For any finite-site sequence channel, the observed score is its conditional expectation. Conditional Jensen therefore gives F_(L,yy)<=exp(-xt)/y^2. N independent loci supply at most N times this information, and unknown nuisance parameters cannot improve efficient information beyond the raw yy entry. At fixed B, this upper bound is B exp(-xt)/(2L y^2), tending to zero as L increases. This is an information bound; applying a Cramer–Rao variance interpretation would require its usual regularity/unbiasedness conditions.

A separate finite-sample statement avoids those estimator restrictions. Compare actual sources (1,2,1) and (1,11/5,1). For their complete genealogy laws,

    KL(P1_T || P0_T)=exp(-1)[log(11/10)-1/11].

The expression follows from the common pre-cut distribution and common tail mass exp(-1), followed by exponential waiting times with different tail rates. Sequence-channel data processing cannot increase this KL. The sources differ by 0.2 in tail hazard. For strict error eta=0.1 with success >=0.95 at BOTH sources, the same Pinsker/testing argument requires at least 1001 independent loci, for EVERY L. check_long_locus_obstruction.py certifies the logarithm by an alternating rational series and the exponential by outward intervals.

Consequently at least 2002L nucleotide calls are necessary for this two-source demand. At B=60,000,000, lengths exceeding 29,970 are ruled out by this bound alone. This is a weak necessary restriction, not a recommended maximum or a sufficient budget. It rigorously prevents the interpretation that arbitrarily long reads can replace independent genealogy replication at fixed total calls.

## 5. Exact finite-L two-source checks

For L=3,12,64,128, a rational rival with tail hazard 2.2 was chosen by numerical nuisance fitting near z0. The finalized source coordinates—not optimizer optimality—are used in the certificate. Exact binomial polynomial coefficients and outward rational intervals certify an upper bound on chi-square(P1||P0). The 95%-at-both-sources, eta=0.1 testing condition yields:

| L | Necessary independent loci | Necessary nucleotide calls |
|---:|---:|---:|
| 3 | 2,061,630 | 12,369,780 |
| 12 | 37,226 | 893,424 |
| 64 | 2,413 | 308,864 |
| 128 | 1,327 | 339,712 |

Different actual nuisance-adjusted rivals are used at different L, all within the same declared broad chart. These necessary lower bounds do NOT rank achievable performance, prove optimal design, or establish a sufficient budget. They are source-faithful checks that avoid comparing uncalibrated moment distances alone. The all-L genealogy obstruction remains independently valid.

certify_locus_length_testing.py upgrades the existing interval engine at runtime to denominator 2^512 and degree-100/101 alternating exponential enclosures before scaling/squaring. Its exact coefficient expansion is stable at that rational precision despite cancellation. It verifies every category lower probability is positive and the probability-sum enclosure contains one. The old interval-engine file bytes are preserved. The output fixes every rational rival, chi-square upper bound, integer testing threshold and numerical enclosure width. No floating likelihood fit is used as proof of the bound.

## 6. Actual fixed-call synthetic inference, including nontruth starts

The primary follow-up benchmark holds B=60,000,000 calls EXACTLY fixed:

| L | Independent loci | Tail-hazard RMSE | Cut RMSE | Initial-hazard RMSE | All three errors <0.1 |
|---:|---:|---:|---:|---:|---:|
| 3 | 10,000,000 | 0.05807 | 0.02500 | 0.001605 | 56/60 |
| 12 | 2,500,000 | 0.01535 | 0.006624 | 0.001130 | 60/60 |
| 64 | 468,750 | 0.009868 | 0.003365 | 0.002190 | 60/60 |
| 128 | 234,375 | 0.008976 | 0.003971 | 0.003325 | 60/60 |

There were 60 multinomial count replicates per design, seed 202610251. Each count is one independent shared-genealogy locus, not independent within-locus sites. Fits use the same broad box and analytic derivative formulas. The table uses ONLY predeclared NONTRUTH starts (0.75,2.4,0.75), (1.25,2.7,1.25), (1.1,1.8,0.8).

An initial changed-design run had included truth among three starts. It was preserved, then repeated with the same generated counts and the nontruth starts. The largest fitted-coordinate difference between runs was 2.45e-6; this is a meaningful bounded initialization control at THIS source, not proof of general global convergence. The old separate 240-fit three-site benchmark also retains its truth-start disclosure and original bytes/results; it was not silently replaced.

The nontruth run has raw optimizer stopping-failure flags 0,1,6,13 at the four lengths. All fits have floating projected-gradient sup norm below 9.1e-9, and none reached the chart boundary. Flags and gradients are retained, not called global-optimality certificates. All 240 counts and fitted parameters are recorded for each initialization run.

The empirical tail RMSE happens to be slightly smaller at L=128 than L=64, while source-local Fisher predicts a modest reversal. Sixty-replicate Monte Carlo fluctuation and finite-sample effects do not identify the optimal length from that difference. Likewise 60/60 successes do not prove 95% coverage or a uniform theorem. The robust qualitative comparison is that moving from extremely short loci to moderate/long loci materially improves the displayed source-conditioned tail/cut diagnostics at equal calls, while sacrificing initial-hazard precision at the longer lengths. This is explicitly a changed experiment, not an improvement under the original three-site observation contract.

## 7. Files, provenance, and limits

- compare_locus_length_designs.py; locus-length-fisher-design.json: source-local quadrature/information calculations and rational rival candidates.
- certify_locus_length_testing.py; locus-length-testing-certificate.json: exact finite-L sufficient-law testing controls.
- check_long_locus_obstruction.py; long-locus-obstruction-control.json: exact all-L genealogy KL bound.
- benchmark_fixed_call_budget.py; fixed-call-budget-benchmark.json: preserved truth-containing-start run.
- benchmark_fixed_call_budget_nontruth.py; fixed-call-budget-nontruth-benchmark.json: same-count nontruth-only-start control used in the table.

No new installation, external write, empirical dataset or biological model check occurred. The prior-provenance review and corrected unknown-calendar likelihood packet remain dependencies. The exact numerical controls and written probabilistic inequalities remain hand/code-review evidence, not Lean certificates. The finite-data sequence-to-demographic direction advances only within this explicitly supplied one-population, known-clock, finite-dimensional family. Arbitrary migrations/pulses, unknown complexity, unknown clocks, linked loci, model misspecification, and the original broad cross-mechanism goal remain outside this result.
