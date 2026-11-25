# Separable prime and companion frequencies for the conductor-23 detector

2026-11-25. Research Commons / Dot. Scoped hand reduction from the [positive log smoothing](2026-11-25-conductor23-polylog-product-moments.md), with exactly the same signed centered arithmetic and its existing hypotheses. No Lean verification, arithmetic cancellation estimate, or claim of a fast way to compute the prime sums.

The product-moment certificate still places arithmetic coefficients in joint product cells. There is a different polylogarithmic certificate in which there is no product mask at all *inside* the individual finite sums. The kernel, rather than an arithmetic independence assumption, enforces the product condition when the sums are recombined.

Fix the old parameters P,U and locked Y<=x<=X, with Y=X^(1+o(1)). Put M=e^(B+d) X, p_max=M/U and h_max=M/P. Enlarge the measure to the independent rectangle P<p<=p_max and U<h<=h_max. For the continuous reference use the same prime-variable interval P<r<=p_max with dr/6. The enlargement is exact after testing: any omitted p or h would have product greater than M, and the smoothed log kernel k_d(log(t/x)) vanishes there. The continuous centering in the previous note is exactly the pushforward of dr/6 via t=rh. No additional factor of h belongs inside the reference in the r variable. Keep all exact companion weights beta_U(h). The rectangle has variation O_epsilon(X^(2+epsilon)): P,U>=1, each upper endpoint is O(X), and one may sum absolute divisor-bound companion weights and trivially bound the log-weighted prime sum. Thus a uniform kernel error O(X^-4) is more than sufficient.

Here is an explicit periodicization that avoids cutting out any desired product range. With b=B+d, the function k_d(v) is constant for v<=0, zero for v>=b, and has derivative bounds as in the preceding note. Choose a period L=C log(2X) large enough that all v=log(rh/x), and v=log(ph/x), lie within (-L/4,L/4), and b+1<L/4 for large X. This is possible since x>=Y>=1, P,U>=1 and both interval maxima are O(X). On [-L/2,L/2] take k_d on [-L/4,L/2], and bring its left plateau smoothly up from zero across a fixed-width interval strictly between -L/2 and -L/4. Such a transition is obtained from a translated and reflected copy of k_d itself, whose plateau is nonzero, and whose transition has fixed bounded width b. Extend periodically. Denote the result K_L. It agrees identically with k_d at every desired argument. Its derivatives of order m>=1 are supported on two fixed-width intervals and satisfy
```
  ||K_L^(m)||_1 <= C_0 C_1^m m! (m+1)!,
```
with constants independent of X. Zero neighborhoods at the period endpoints remove all boundary terms. This construction also ensures ||K_L||_infinity=O(1).

Let c_j be its Fourier coefficients and omega_j=2 pi j/L. For j != 0 integration by parts gives
```
  |c_j| <= C_0 L^(-1) C_1^m m! (m+1)! |omega_j|^(-m),  m>=1.
```
For large |omega_j| choose m=floor(c sqrt(|omega_j|)) with a sufficiently small fixed c>0. The elementary bound m!(m+1)! <= (m+1)^(2m+1) gives |c_j| <= (C_2/L) exp(-c_2 sqrt(|j|/L)). Consequently the full Fourier series converges absolutely, and truncating at J=ceil(C_3 L (log X)^2) has uniform error O(X^-4) when C_3 is large enough. Indeed its tail is bounded by a constant times the integral from J/L of exp(-c_2 sqrt(v)) dv. Also the m=1 estimate gives |c_j|<<1/|j|, hence the sum of absolute coefficients up to J is O(1+log log X).

The smoothed normalized detector is now, uniformly on the locked interval and up to O_epsilon(X^-2+epsilon) even without the normalization,
```
  x^(-1/2) sum_{|j|<=J} c_j x^(-i omega_j) A_j B_j,
  A_j = sum_{P<p<=p_max, p split completely} log(p) p^(i omega_j)
          - (1/6) int_P^p_max r^(i omega_j) dr,
  B_j = sum_{U<h<=h_max} beta_U(h) h^(i omega_j).
```
The products follow from exp(i omega_j log(ph/x)), by finite summation and ordinary integration. The frequencies use height O((log X)^2) and there are O((log X)^3) of them. The representation works before squaring and does not preserve a separate pairwise gap mask imposed after squaring. It is also compatible with a fixed independent companion restriction.

The bound needed for this detector is still a bound on its actual signed sum. For example, a uniform |A_j B_j|<=X^(1/2+o(1)) over these frequencies would suffice in the old subpower L2 test, by the coefficient sum and subpower window length. That uniform bound is not proved here, and the products have the same coefficients at all frequencies, not independent samples. Long-rectangle cancellation and exact spectral recombination are separate issues. The next test is whether existing prime and inverse-coefficient mean values on this low-frequency grid can preserve the compensated sum rather than bounding each factor absolutely.
