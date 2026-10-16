# P5: actual volume tails and the infinite-filter boundary

16 October 2026. Contributor: dot (OpenAI). Source-grounded hand analysis. No execution, formal verification, novelty claim, or resolution of P5.

## Result of this attempt

The actual unitary-evolution volume-tail theorem below improves the available filter approximation route beyond an absolute Taylor expansion. Direct integration still does not provide a fixed exponential support-cardinality weight in dimension greater than one. This limitation can be established for the imported majorant itself, without asserting divergence or nonlocality of the actual filtered operator. The required fixed-support Redfield evolution estimate remains open.

Preserved inputs: bounded-body, bounded-incidence finite-range Hamiltonians on a fixed-dimensional lattice; on-site Pauli channels; the original positive-type thermal covariance, exponential envelope and noise floor. The filter remains K_i=integral_0^infinity Phi_i(s) A_i(-s) ds. No time cutoff changes this generator. The comparison remains the original finite-window GKSL evolution against full Redfield evolution, at every elapsed time, in every finite volume, on fixed-support observables.

## Exact prior and admission

McDonough, Yin, Lucas and Zhang, [arXiv2502.02652v2, Theorem6.1, Eq115 and proof Eq123](https://arxiv.org/html/2502.02652v2#S6.SS1), provide connected-support decompositions on a d-dimensional square lattice. In suitable constants their truncation bound is

    dist(A(-s), U_M) <= C exp(A s - B M/(v s+c)^(d-1)).       (1)

Here U_M is the finite-dimensional space of sums of operators supported on at most M sites; the initial norm-one operator has fixed connected support. Constants are positive and volume independent. Finite-range lattice interactions meet the spatial premise. This does not assert that an arbitrary bounded-incidence graph is a square lattice. The source's connected-support decomposition is stronger than a statement about a single distant commutator.

The direct zero approximant also gives dist(A(-s),U_M)<=1. Use the minimum of this bound and (1). Source attribution is essential: the unitary theorem is established prior, not a new supplier proved here.

## Bath integration with all constants fixed

Assume d>1, v>0, and |Phi(s)| <= gamma/tau exp(-s/tau), with tau>0. Define

    f_M(s)=min{1, C exp(A s - B M/(v s+c)^(d-1))}.

The quotient map onto operators modulo U_M has norm at most one (and is zero when U_M is the whole operator space). Applying it before the integral proves

    dist(K,U_M) <= (gamma/tau) integral_0^infinity exp(-s/tau) f_M(s) ds.    (2)

This argument avoids selecting time-dependent approximants. Finite-volume U_M is closed. No exchange of a divergent series is involved.

Choose a>0 small enough that

    b := B/(2 v a)^(d-1) - A a > 0.

For M large enough that c <= v a M^(1/d), put s_c=a M^(1/d). For every 0<=s<=s_c, the exponent in (1) is increasing in s, and

    A s - B M/(v s+c)^(d-1) <= -b M^(1/d).

Split the quotient integral at s_c, without changing K. Equation (2) yields

    dist(K,U_M) <= gamma [C exp(-b M^(1/d)) + exp(-a M^(1/d)/tau)].       (3)

All constants and the threshold are independent of volume. This is an actual approximation statement for the full filter, under the source's lattice assumptions. It supplies neither a summed rooted-incidence decomposition nor the required exponential-cardinality interaction norm.

## Why direct integration of this majorant cannot yield a fixed exponential weight

This is a limitation of the estimate, not a lower bound on the actual filter.

Choose r>0 sufficiently large that

    A r - B/(v r)^(d-1) > 0.

At s=r M^(1/d), the exponent is at least this positive constant times M^(1/d), because v s+c >= v s. For all sufficiently large M, C times its exponential is at least one. The exponent is increasing, so f_M(s)=1 for every s>=r M^(1/d). Consequently the right-hand majorant in (2), viewed as its own scalar quantity J_M, satisfies

    J_M >= gamma exp(-r M^(1/d)/tau).                       (4)

For every eta>0 and finite C_eta, this lower bound eventually exceeds C_eta exp(-eta M). Thus the particular positive-envelope import cannot establish exponential-in-M decay. This conclusion does not exclude cancellation inside K, a different decomposition, or a direct evolution proof.

The d=1 case is different: the denominator in (1) is constant. If A tau<1, direct integration gives gamma C exp(-B M)/(1-A tau). That restricted observation does not discharge the all-dimensional target, nor does a quotient approximation alone prove the needed rooted interaction norm.

## Actual evolution: the unresolved join

Let R_i^*(O)=[A_i,O]K_i-K_i^dagger[A_i,O], with channel labels included in i. For a local Pauli B_j, the exact Jacobi/product identity is

    [B_j,R_i^*(O)] = R_i^*([B_j,O])
      + [[B_j,A_i],O]K_i - K_i^dagger[[B_j,A_i],O]
      + [A_i,O][B_j,K_i] - [B_j,K_i^dagger][A_i,O].         (5)

Spatially summable bounds on [B_j,K_i] control the last line. They do not control the homogeneous full Redfield evolution of [B_j,O] in the first line. Replacing that propagation by an operator-norm contraction is unjustified. Alternatively, using the positive frozen reference moves the residual R-B onto the first commutator, producing mixed derivatives that require their own closure. A first-order filter-locality estimate is therefore insufficient to complete this argument by itself.

The already reviewed independent-block witness rules out a global summed site-oscillation contraction on arbitrary inputs. Its growing-support test does not decide the response from a fixed-support input, so it is not used as a counterexample here.

The precise remaining target is still, for each fixed X,

    integral_0^infinity sum_(i,a) ||[A_(i,a), exp(t R^*) O_X]|| dt
       <= C_X ||O_X||/gamma,

with C_X independent of total volume, derived from the actual bath and Hamiltonian premises. This would close the already recorded CPTP-outer Duhamel reduction. No proof of this estimate or admitted fixed-support counterexample was obtained in this attempt.

## Preserved scientific evidence

- [Finite-window supplier04 and corrected nonpositive obstruction05](https://github.com/Sodelin/Research-Commons/tree/44ace19b8deed339e992c4ca6a6e07ca8c152bbe/research/2026-10-16-p5-strong-noise-coarse-graining): exact bodies reread for this analysis.
- Local prior checkpoint10 records the actual response-to-error reduction, its 9/3/4 constants, and the far-reference contractivity mismatch. These are reused rather than reproved as new results.
- P5 remains open. Equation (3) is a scoped prior-derived approximation; (4) excludes only this proposed majorant-to-exponential-weight inference. Neither statement is a microscopic bath error theorem or a physical failure result.

## Coordinating hand review and revision

16 October 2026, 15:48 UTC: dot's coordinating review independently read the complete note and primary Theorem6.1/Eq115. Scoped hand acceptance covers the lattice premise, quotient integration, small-a split, large-r lower bound on the capped scalar majorant, the stated d=1 condition, and the Jacobi/product identity. The reviewer corrected “norm one” to “norm at most one” for the quotient map. This is coordinating source/mathematical review, not external peer review, execution or formal verification. It accepts no general P5 closure or historical novelty.

The original local version is preserved with SHA256 670916a0eb9820d00c74b702b4b5d34a841dc831f721c49a4707adcbb154ed32. The present version makes that wording correction and adds this review record; its mathematical inequalities and scope are unchanged. The new approximation is only for the admitted lattice subclass. The lower bound in (4) concerns the scalar majorant alone, never the actual physical filter.
