# The shared-prime covariance is below the conductor-23 off-line scale

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof for the actual centered split-prime detector with the existing abelian centering comparison. No new Lean verification, numerical check or estimate of the remaining distinct-prime covariance.

The earlier off-diagonal reduction controls contributions with the same **companion** index. It leaves open whether two very different companions sharing the same split prime can generate the required signal. In the smoothed two-shell detector they cannot. Sum the signed companions first, before squaring, and use that the same L-function from the inverse coefficients is entire.

## Signed single-prime estimate

Use fixed B,d and the positive compact smoothing of the [aligned grid](2026-11-25-conductor23-aligned-fourier-grid.md). Write J(v)=R*mu_tilt(v) for its effective compact log kernel, W(t)=J(log t), and b for a fixed constant with supp W contained in [1,exp(b)]. Let U=floor(Y^u), P=Y^alpha and Y<=x<=X=Y^(1+o(1)), with the same admissible locking as the previous detector, shortening the upper endpoint for fixed shifts if needed. Write beta=sup Re rho for the Artin zero supremum and beta_U=mu_{L,>U}*a, where a is the coefficient sequence of L and mu_L the inverse sequence. Define
    V_p(x)=sum_{h>U} beta_U(h) W(ph/x).
The sum is exactly zero unless p<=exp(b)x/U. For p on its active support put H=x/p, so H>=exp(-b)U and H<=X. For every eps>0, uniformly on this support,
    |V_p(x)| <<_{L,W,eps} U^beta X^eps.                         (1)

To prove (1), use beta_U=delta_1-mu_{L,<=U}*a, including every term in the completed convolution. Thus V_p(x)=W(1/H) minus the inverse Mellin integral of
    M_U(s) L(s) H^s Wtilde(s),   M_U(s)=sum_{m<=U} mu_L(m)m^(-s).
Here Wtilde(s)=int_0^infinity W(t)t^(s-1)dt. It is entire; on any fixed strip it decays faster than any fixed power of height. Indeed the effective compact log kernel is the convolution of a piecewise smooth compact kernel with infinitely many compact uniforms (tilted by exp(-t/2)); using only a fixed finite number of uniform factors already gives any desired polynomial decay, also uniformly on fixed vertical strips. Use Mellin inversion initially on Re s=2. Move to a fixed 0<sigma<min(1/2,eps/4), with no poles from L, M_U or Wtilde. Fixed-degree polynomial bounds on L justify the shift. The [prior twisted inverse-prefix bound, (2)](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd), using the actual supremum beta, bounds the result by H^sigma U^(beta-sigma+eps/4) times a finite fixed Mellin integral. This is O(U^beta X^eps). The single W(1/H) term is bounded independently. No sharp truncation in the companion inside V_p is inserted besides the exact beta_U support; an independent sharp companion mask would require a separate justification.

## Removing nearby primes from the discrete-discrete term

Put d_p(x)=x^(-1/2)(log p)V_p(x) for p>P splitting completely (zero otherwise). This is the discrete prime component of the normalized statistic after summing companions. Keep all mixed and continuous-centering terms exactly as before. The part of its squared discrete component with p=q is sum_p d_p². By (1) and the active support,
    sum_p |d_p(x)|² <<_eps U^(2beta-1) X^eps.                  (2)
Indeed at most exp(b)x/U integers are active, x cancels against normalization and log² X is absorbed by reducing the auxiliary eps in (1). More generally, for any W_0>=1, any mask on ordered pairs supported on |p-q|<=W_0, and with mask bounded by one in absolute value, sum of |d_p d_q| over its pairs is O_eps((1+W_0)U^(2beta-1)X^eps), by 2|d_p d_q|<=|d_p|²+|d_q|² and the maximum row and column counts. This is a bound on absolute mass *after* the signed companion summation per prime, not on individual h,k placements.

On the sufficient detector grid there are subpower many nodes, so summing (2) there is still O_eps(U^(2beta-1)X^eps); the same holds on integration over the subpower-length log window. If W_0=X^o(1), all bounded masks on that nearby-prime band have this same cost including p=q. When beta=1/2 it is subpower. When beta>1/2 and u<1 it is smaller than X^(2beta-1) by a fixed power, since U=X^(u+o(1)). More generally a polynomial band W_0=X^w may be removed from an off-line lower signal when w<(1-u)(2beta-1); no subpower GRH upper bound on that larger mask is asserted. The same estimates apply at any single node that detects a signal.

Consequently, after the exact expansion of the centered square and removal of a prescribed subpower near-prime band from its discrete-discrete term, the remaining **signed** expression still has the off-line lower growth and the on-line subpower upper bound of the full square on the previously sufficient windows/grid. This is a second, independently justified pruning from the prime side. It cannot automatically be combined with arbitrary companion-pair masks: such masks may break the inner signed sum used in (1). It does not justify dropping the centering terms, and it leaves the distinct, separated-prime covariance open.
