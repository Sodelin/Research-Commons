# A finite-data certificate for uniform statistical transfer

Contributor: /root/current_stat_scope_audit, 2026-09-30 UTC. GENERAL-TRANSFER-01 constructive continuation. This closes a restricted finite-data certificate obligation, not arbitrary scientific bridge discovery or unrestricted biological reconstruction. No historical novelty claim.

## 0. What is now obtainable

Under effective finite-cover, finite-alphabet, TV-continuity and certified-law-access premises, return one rational simulator K, an independently checkable primal/dual certificate, and an interval containing the **entire parameter class's** directional deficiency. Numerical solver objectives are never treated as evidence. The same returned K receives the interval's upper bound uniformly over every parameter.

The implementation is compact_certificate.py. Exact analytical controls and execution results are in compact-certificate-verification.json. This certificate connects an existence theorem to an executable finite check within the stated class; it does not infer its model, sampling or covering premises from data.

## 1. Assumptions and theorem

Let Theta be a nonempty compact metric space with a supplied finite r-cover G={theta_1,...,theta_m}, listed without duplicate points: every theta has some i with d(theta,theta_i)<=r. X,Y are known nonempty finite alphabets. A single Markov kernel K has entries K(x,y)>=0 and sum_y K(x,y)=1 for each x, independent of theta. Define

```math
\delta=\min_K\sup_{\theta\in\Theta}\operatorname{TV}(KP_\theta,Q_\theta),
\qquad \operatorname{TV}(p,q)=\tfrac12\sum_z|p(z)-q(z)|.
```

The minimum exists because stochastic matrices form a compact product of simplexes and the supremum is lower semicontinuous. Known envelopes omega_P,omega_Q bound TV(P_theta,P_phi) and TV(Q_theta,Q_phi) whenever d(theta,phi)<=r. Nondecreasing continuity moduli are one way to satisfy this, but a bound merely at some distances equal to r is insufficient.

Supplied normalized rational laws Phat_i,Qhat_i satisfy, **simultaneously**,

```math
\operatorname{TV}(P_{\theta_i},\widehat P_i)\le\rho_P,
\qquad\operatorname{TV}(Q_{\theta_i},\widehat Q_i)\le\rho_Q,
\qquad\rho=\rho_P+\rho_Q.
```

These may be deterministic error certificates or a joint event of specified confidence. Varying gridwise bounds can be replaced by their separate maxima. Let dhat be the finite estimated-grid optimum. Let L<=dhat<=U be **certified** bounds, where U is the exact value of a returned feasible K. Then

```math
\boxed{
\max(0,L-\rho)\ \le\ \delta\ \le\
\min\{1,U+\rho+\omega_P(r)+\omega_Q(r)\}.
}
```

Moreover the returned K itself satisfies

```math
\sup_\theta\operatorname{TV}(KP_\theta,Q_\theta)
\le\min\{1,U+\rho+\omega_P(r)+\omega_Q(r)\}.
```

Every measurable randomized decision on target observations can therefore be simulated by first drawing y from K(x,·). Its pointwise [0,M]-loss risk discrepancy is at most M times this upper bound. The result concerns distribution-law transfer, not invertible realized samples.

### Proof, including the single-kernel obligation

For any K and any grid index i, contraction and the triangle inequality give

```math
|\operatorname{TV}(KP_{\theta_i},Q_{\theta_i})
-\operatorname{TV}(K\widehat P_i,\widehat Q_i)|\le\rho.
```

Taking maxima and then minima proves that the true-grid and estimated-grid optima differ by at most rho. Restriction to grid parameters gives the lower bound delta>=dhat-rho>=L-rho.

For every theta choose a covering index i. Apply the same K throughout:

```math
\operatorname{TV}(KP_\theta,Q_\theta)
\le \omega_P(r)+\rho_P+
\operatorname{TV}(K\widehat P_i,\widehat Q_i)
+\rho_Q+\omega_Q(r).
```

The middle term is at most U. TV is always at most one. This proves the upper bound for the actual returned kernel, then for the optimum. No fitted-kernel independence from the estimation data is needed: the simultaneous law-error event bounds **every** stochastic K.

## 2. Exact primal and dual witnesses

The primal certificate consists only of a rational stochastic matrix K, checked exactly, and

```math
U=\max_i\tfrac12\sum_y
\left|\sum_x\widehat P_i(x)K(x,y)-\widehat Q_i(y)\right|.
```

A dual certificate consists of a rational simplex vector lambda and rational v satisfying

```math
\lambda_i\ge0,\quad\sum_i\lambda_i=1,
\qquad0\le v_{iy}\le\lambda_i.
```

Its exact lower bound is

```math
L=\max\left\{0,
\sum_{i,y}v_{iy}\widehat Q_i(y)
-\sum_x\max_y\sum_i\widehat P_i(x)v_{iy}\right\}.
```

Weak duality suffices to validate it. Put f_i(y)=v_iy/lambda_i on positive-weight states. The objective is the minimum over stochastic H of sum_i,y v_iy(Qhat_i−H Phat_i)(y): each row chooses its maximizing column. For any K this is at most sum_i lambda_i TV(K Phat_i,Qhat_i), hence at most its worst row error. Maximizing with zero remains a valid lower bound because deficiency is nonnegative. Thus 0<=L<=dhat<=U<=1, without believing any optimizer's status or residual tolerance.

The witness also has decision meaning. Use prior lambda supported on the grid, action set Y, and loss 1−f_i(a). Target's identity action supplies the target utility term; source's optimal utility is the displayed maximum. If L>rho, this same task gives a true Bayes-risk disadvantage at least L-rho, certifying a substantive failure of uniform transfer. A nonpositive raw objective supplies no positive separating task.

Finite LP strong duality permits optimal witnesses. A rational version has an exactly optimal rational solution; finite enumeration of full-rank active constraints with exact linear algebra is a terminating, potentially expensive algorithm. The supplied prototype instead uses SciPy/HiGHS for candidate generation, then repairs K and lambda into rational simplexes and clips v into its exact feasible interval. Only exact Fraction evaluation determines L,U. Missing or failed proposals can fall back to a uniform kernel and zero dual, producing a valid loose interval. **That fallback does not promise optimization accuracy.**

The primal LP uses |X||Y|+m|Y|+1 variables, 2m|Y|+m inequalities and |X| row-normalization equations. The separate dual uses m+m|Y|+|X| variables, m|Y|+|X||Y| inequalities and one simplex equation. Exact witness evaluation requires O(m|X||Y|) rational operations; bit complexity also depends on denominators. The prototype constructs dense matrices and is intended for small finite experiments.

## 3. A finite-sample simultaneous error event

Fix the grid and N before sampling. For each i obtain N IID source draws from P_theta_i and N IID target draws from Q_theta_i. Within each law its draws must be independent and have the stated common law. Draws across different laws/grid points may be dependent. The alphabets must include all possible outcomes, including unobserved cells.

There are J=m(|X|+|Y|) empirical coordinates. For alpha in (0,1), let

```math
b=\sqrt{\frac{\log(2J/\alpha)}{2N}}.
```

Hoeffding's two-sided Bernoulli bound and a union bound give probability at least 1-alpha that every coordinate error is at most b. Consequently one can use

```math
\rho_P=\min(1,|X|b/2),\qquad
\rho_Q=\min(1,|Y|b/2).
```

For completeness, the concentration step has a short direct derivation. For a centered Bernoulli variable, the logarithm of its moment-generating function has value and derivative zero at zero, and second derivative equal to the variance of a tilted Bernoulli law, at most 1/4. It is therefore at most t^2/8. Independence over N draws and Chernoff optimization give exp(−2Nb^2) for either tail; their sum is 2exp(−2Nb^2). Summing over J cells gives alpha. No independence of cell counts or across-law sample blocks is used.

The code avoids treating floating log/sqrt as a certified upward bound. It computes the least integer c with 2^c>=2J/alpha, then a rational bplus>=sqrt(c/(2N)) by integer square-root and upward rounding. Since log(2J/alpha)<=c, this is conservative. Empirical probabilities must have denominators dividing N. These checks establish arithmetic consistency, not the IID provenance of observations.

A stage consumes 2mN observations under this sampling arrangement, plus covering-oracle, model, LP and exact-verification costs. Large covering numbers may make this impractical; compactness alone says nothing about those costs or access to hypothetical parameter settings.

## 4. Refinement, abstention and effective scope

For a sequence of stages use effective shrinking finite covers, moduli tending to zero, law access sufficient to obtain shrinking rho, and certified primal/dual gaps U-L tending to zero. The interval width is at most

```math
(U-L)+2\rho+\omega_P(r)+\omega_Q(r).
```

On a common validity event where these quantities vanish, both endpoints converge to delta. A strict threshold delta<tau is eventually certified by upper<tau; delta>tau is eventually certified by lower>tau. An interval straddling tau yields abstention. Equality at tau or exact zero need not be decided after finitely many samples, even with exact grid optimization: positive shrinking uncertainty can keep the boundary inside every interval. Structural known equalities are a separate source of exact certification.

Statistical stages need a summable failure allocation, for example alpha_s=alpha/2^(s+1), to retain overall confidence at least 1-alpha. Adaptive grids can use fresh blocks with conditional IID and fixed conditional sample sizes; optional stopping or repeated examination of a fixed-stage bound requires an anytime argument not supplied here. The prototype's sampling mode is a **fixed-stage** certificate. Both rational rounding resolutions must increase when needed; fixed denominators can leave accuracy floors.

Known moduli, effective nets and sampling/evaluation access are premises stronger than mathematical compactness. No arbitrary unbounded biological network family is declared compact. There is also an important discrete-target boundary: if Q_theta is a Dirac law of a discrete scientific label and its TV modulus vanishes, that label is locally constant, and constant on a connected parameter class. Changing support labels at zero-weight boundaries therefore cannot silently satisfy this assumption. Separate strata, a margin/abstention contract or a different target experiment must be justified.

## 5. Executable controls and use

Run from a Research Commons checkout root:

```sh
python research/2026-09-30-general-transfer-closure/compact_certificate.py research/2026-09-30-general-transfer-closure/compact-certificate-example.json --output certificate.json
python research/2026-09-30-general-transfer-closure/compact_certificate.py certificate.json --verify
python research/2026-09-30-general-transfer-closure/compact_certificate.py --fixtures
python research/2026-09-30-general-transfer-closure/compact_certificate.py --fixtures --no-scipy
```

Input uses rational probability rows P,Q and certified bounds rho_P,rho_Q,omega_P_r,omega_Q_r,radius. Defaults of zero describe a zero-error, zero-modulus input contract, not an inference of equality from missing scientific information. Alternatively a sampling object with fixed N, rational alpha and optional radius_denominator derives conservative sampling errors. JSON floats are rejected. --no-scipy exercises the certified fallback. The output retains its explicit unverified premises. compact-certificate-example.json names its parameter class, grid and analytical cover/modulus/error proofs; fixture records carry similar scope metadata. This metadata is preserved for review but is not automatically verified by the arithmetic checker.

The fixtures have independently known meanings:

| Control | Analytic check |
|---|---|
| Identity source/target | Identity K gives exact delta=0. |
| Uninformative source, opposing binary targets | A fair-coin K and lambda=(1/2,1/2) dual give exact delta=1/2. |
| Theta=[0,1], singleton source, Q_theta=(theta,1−theta); grid {1/4,3/4}; estimates (3/8,5/8),(5/8,3/8) | Estimated grid delta=1/8; target error 1/8 and cover modulus 1/4 lift upper to the true global delta=1/2. |
| True source laws both Bernoulli(1/2), true opposing targets; each estimated source/target perturbed by 1/8 | Estimated grid delta=1/4 and true delta=1/2 show that the sum of both law-error terms can be necessary. |
| N=10^6, alpha=1/20, J=6 | Exact rational bplus=1/500 gives the certified interval [497/1000,503/1000] around the opposing-target optimum. |
| Corrupted kernel, dual simplex, dual box or claimed upper bound | Exact checker rejects each forged certificate. |

These are analytical fixture checks, not a simulation establishing scientific sampling assumptions or empirical usefulness. The recorded automatic solver certificates are separately re-evaluated exactly.

## 6. Prior and source status

Classical Blackwell–Le Cam finite-experiment comparison and the inspected general comparison sources in [statistical.md](../2026-09-30-general-transfer-audit/statistical.md), [dominated.md](dominated.md) and [abstract-bridge.md](abstract-bridge.md) supply the background. TV contraction, finite LP duality, continuity covering and concentration are established tools; this packaging is not claimed as a new theorem.

Hoeffding (1963), *Probability Inequalities for Sums of Bounded Random Variables*, JASA 58:13–30, DOI [10.1080/01621459.1963.10500830](https://doi.org/10.1080/01621459.1963.10500830): primary publisher metadata/abstract retrieved; the original PDF retrieval failed. The Bernoulli inequality used here is independently derived above. SciPy's [official linprog documentation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.optimize.linprog.html) was inspected for its numerical LP interface and status fields; those fields do not replace exact feasibility checks.

## 11. Process integrity

Dependency availability was checked once: NumPy and SciPy were present. The implementation checks rational probability normalization, primal feasibility, dual simplex/box feasibility, exact objectives and every reported interval field. The proof covers the complete compact parameter class, not only a finite fixture. Independent reviews are requested separately for mathematical scope and implementation/controls. No proof assistant or empirical-domain validation is claimed. No GitHub commits or pushes by this contributor.

## 12. Inference robustness and remaining master obligations

The arithmetic certificate is unconditional once its input error/cover/modulus premises are valid; a sample-derived interpretation has their stated joint confidence. Removing effective access, uniform continuity, joint error coverage, the finite alphabet or cost promises removes this constructive guarantee. The tool cannot certify unobserved model semantics or create causal correspondence.

This closes the proposed compact finite-alphabet certificate endpoint under explicit premises. General scientific interfaces still require justified observations, target/parameter/intervention alignment, domain-specific positive regimes or class-matched impossibility, and practical resource bounds. In particular ALLLEVEL-STAT-01 retains its independent biological observation-fiber obligations.
