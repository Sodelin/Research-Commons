# A polylogarithmic product-moment certificate for the conductor-23 detector

2026-11-25. Research Commons / Dot. Hand deduction using the existing conductor-23 explicit formula, fixed-length zero detector, and retained prime comparisons with their original assumptions, including the abelian centering input. No new Lean verification and no bound for the signed arithmetic moments.

The [unchanged kernel](2026-11-24-conductor23-product-cell-compression.md) can be evaluated to subpower error from about X^(1/4) cell pairs. A fixed positive smoothing in log x, which leaves every off-line zero visible, cuts the storage to O((log X)^5) scalar moments. This is not a claim that computing or bounding these moments is fast. The averaging is a fixed operator, not an X-dependent kernel selected after seeing the primes.

## A nonvanishing average

Fix any width d>0. Let nu_d be the law of the sum of independent uniforms on [0,l_j], where l_j=d/(j(j+1)) for j>=1. Their lengths sum to d, so the sum exists and nu_d is supported on [0,d]. For a normalized function f(u)=e^(-u/2)C(e^u), define its forward average A_d f(u)=int f(u+t) d nu_d(t). Its multiplier on the residue of a zero rho is

    M_d(rho-1/2) = product_(j>=1) [(exp(l_j(rho-1/2))-1)/(l_j(rho-1/2))],

with removable values at zero. For fixed z, the deviations of the factors from one are O_z(l_j), and every factor is nonzero when Re z>0. Hence M_d(z) is nonzero there. For real z it is strictly positive, and on the normalized critical strip its absolute value is at most exp(d/2). Thus the original absolutely summable zero coefficients stay absolutely summable, every off-line coefficient stays nonzero, and positive real coefficients keep their sign. The normalized explicit-formula remainder retains its bound under the fixed translation range.

The [positive-filter proof](https://github.com/Sodelin/Research-Commons/commit/7a2d2c5d790118523c794119cc9d69237c787fd2) and [fixed-factor density input](https://github.com/Sodelin/Research-Commons/commit/304b341ad0a4a99eb16055613bfafceb7c476850) now apply to the new coefficients: the proof needs their absolute tail, positivity for real zeros, a nonzero target coefficient, and the same height sparsity, not their precise old values. A fixed added length d does not change the asymptotic window criterion. In particular on locked windows [log Y, log X] of diverging length o(log X), evaluate the averaged statistic through log X-d so all translations stay within the old window. If beta_*>1/2, the positive integral for the averaged full detector still has rate (beta_*-1/2) log X+o(log X). The same conclusion transfers to the appropriately signed averaged retained split-prime statistic by the existing uniform power-gap comparison, since the averaging preserves the error bound. Under GRH the old subpower estimate also transfers. No lower bound on |M_d| uniform in the chosen zero or in d is asserted.

## Exact data entering the approximation

Use the signed product measure from the two-moment note, restricted to t<=e^B X, with the same locked P and U, exact split primes, inverse coefficients, and continuous reference. Write w=log t and let eta be its pushforward to w. Before smoothing its normalized contribution is e^(-u/2) int k(w-u) d eta(w), where k(v)=K_B(exp v). After smoothing it is exactly e^(-u/2) int k_d(w-u) d eta(w), where

    k_d(v) = int e^(-t/2) k(v-t) d nu_d(t).

This is constant on v<=0 and vanishes on v>=B+d. It does not change the arithmetic measure or require sampling the original kernel at any x>X. The unnormalized absolute measure satisfies |eta|(R) <<_(B,epsilon) X^(1+epsilon), by the local-mass bound from the two-moment note.

## Derivative and memory bounds

For each j tilt its uniform law by exp(-t/2), without renormalizing. Its mass is at most one and the total variation of its distributional first derivative is at most 2/l_j: the two endpoint jumps plus the integral of the absolute interior derivative sum to 2/l_j exactly. The tilt factors over the independent variables, including the remaining tail. To differentiate k_d m times, apply one derivative to each of the first m tilted uniform measures, leaving the tail untouched. Convolution of bounded uniformly continuous k with these finite signed measures yields a continuous representative. Consequently k_d is C^infinity and

    ||k_d^(m)||_infty <= ||k||_infty (2/d)^m m! (m+1)!.

Partition the log-product interval [log Y, log X+B] into disjoint cells of length at most h=(log X)^(-3); use the usual half-open assignment for atoms and include the last endpoint. Keep one total mass below log Y, where the kernel is constant at all desired u>=log Y. In each cell with left endpoint a record the m signed moments int_cell (w-a)^j d eta(w), j=0,...,m-1. Taylor expansion of k_d(w-u) in w at a uses exactly these moments. With m=ceil(log X/log log X), the per-unit-mass Taylor remainder is uniformly at most

    ||k||_infty (2h/d)^m (m+1)! = X^(-2+o(1)).

Indeed log((m+1)!)<= (m+1) log(m+1), so its log is at most m log log X+o(log X), whereas m log h=-3m log log X. The normalized reconstruction error is therefore O(X^(-3/2+epsilon+o(1))) since Y=X^(1+o(1)). In particular it is negligible for the upper-window criterion. The number of cells is O_B((log X)^4); their O(log X/log log X) moments each give the claimed storage count. These are exact real moments of the signed measure, not a bit-complexity or floating-point stability claim.

The remaining question is whether the actual weighted signed moments or their aggregate Taylor evaluation can be controlled at square-root scale on arbitrarily late windows. Smoothing and compression make no cancellation assumption, and do not supply that arithmetic estimate.
