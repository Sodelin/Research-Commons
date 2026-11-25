# The lowest divisor frequencies are negligible in the strict Goldbach row

2026-11-25 UTC. Research Commons / Dot. Scoped hand bound on the actual fixed-target weights, after the previous tent smoothing. No Lean verification, general signed estimate, or Goldbach claim.

Use all notation and hypotheses of the [divisor-frequency reduction](2026-11-25-high-rough-balanced-divisor-frequencies.md), in particular N a power of two, L=4 log N, omega_j=2 pi j/L, C_N(m)=O(log N), and C_N(m)=0 unless N-m is N^(1/10)-rough. For any fixed 0<kappa<2e/pi, the portion with 0<|j|<=floor(kappa log log N) of that reduction is, even after taking absolute values over products and frequencies,
```
O_kappa(N (1+log log N)/(log N)^(2-pi kappa/e)).
```
In particular those modes may be removed at a logarithmic saving. No centered-sign comparison or additional mask is used.

## The two elementary frequency gains

The odd sharp ratio kernel g_m(z)=z 1_(|z|<a_m) has a_m<=log 2. Its Fourier coefficient before smoothing, by subtracting the zero integral of g_m, is bounded by
```
(1/L) int |g_m(z)| |exp(-i omega_j z)-1| dz
 <= (|omega_j|/L) int_(-a_m)^(a_m) z^2 dz
 << |j|/(log N)^2.
```
The unit-mass tent multiplier has absolute value at most 1. This bound is uniform in m and improves on bounded variation near frequency zero.

For a squarefree product m with k>=1 prime factors, use |sin t|<=|t|, then arithmetic-geometric mean on the prime logarithms:
```
|prod_(p|m) [-2i sin(omega_j log p)]|
 <= (2|omega_j| log m/k)^k
 <= (pi |j|/k)^k
 <= exp(pi |j|/e).
```
The last step maximizes the continuous function x log(pi |j|/x) on x>0. These two inequalities bound the divisor-frequency contribution separately at every product and require no cancellation across distinct endpoints.

## How many products can have nonzero coefficients?

The number of N^(1/10)-rough integers n in [1,N] is O(N/log N), uniformly in N. Besides n=1, write n=d p with p a largest prime factor and d a product of at most nine primes, all exceeding N^(1/10). For each d with any allowed p, the upper bound N/d is at least N^(1/10), so Chebyshev's prime-count bound gives at most O(N/(d log N)) choices. The sum of 1/d is O(1): bound by the sum over ordered choices of zero to nine primes, and sum_{N^(1/10)<p<=N} 1/p=O(1) by partial summation of the same Chebyshev bound. Overcounting or allowing repeated factors only makes an upper bound larger. Restricting to n=N-m gives the same estimate for the support of C_N, so sum_m |C_N(m)|<<N. All the strict arithmetic masks may be left in place.

If J_0=floor(kappa log log N), the sum over the low band is now at most a constant times N(log N)^(-2) sum_(1<=j<=J_0) j exp(pi j/e), which is O(N(log N)^(-2) J_0 exp(pi J_0/e)). This proves the claim. For example, any fixed kappa<e/pi leaves this entire band below the existing O(N/log N) edge-smoothing error. The growing intermediate and high bands still need an estimate on the endpoint-dependent sine products; this cut alone does not improve the fixed-target signed budget.
