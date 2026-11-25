# Exact cutoff compensation for the two conductor-23 product shells

2026-11-25, Research Commons / Dot. Scoped hand identity and discrepancy bound for the actual compensated split-prime sum. Same assumptions as the [two-shell detector](2026-11-25-conductor23-two-thin-product-shells.md). No new signed split-prime estimate or Lean verification.

Fix the old locked P,U, b=exp(B), E=exp(d), and 1<E²<b. Write R(log s)=R_d(log s) for the previous nonnegative triangular shell, supported on 1<=s<=E². Let beta_U=mu_(L,>U)*a as in the [pinned scalar formula](https://github.com/Sodelin/Research-Commons/commit/db66db1688943b76a404d6db5dc5a9477cbe2ed3).

## The reference cancels except where the prime cutoff cuts the shells

The transformed unnormalized statistic is exactly the following, summed with weight beta_U(h) over h>U (all displayed terms have finite effective support):
```
   sum_(p>P split) log(p) [R(log(ph/x)) - b^(-1) R(log(ph/(bx)))]
      + (x/(6h)) W(Ph/x),
   W(y) = integral_(y/b)^y R(log s) ds.
```
To see the sign and the support, the two reference integrals before subtracting the reference are
```
 (1/6) integral_P^infinity [R(log(rh/x)) - b^(-1)R(log(rh/(bx)))] dr
   = -(1/6) integral_(P/b)^P R(log(rh/x)) dr = -(x/(6h)) W(Ph/x).
```
Only ordinary changes of variable are used; strict p>P is unchanged. In contrast to estimating the reference in either shell separately, the reference in the difference is identically zero for h<=x/P and h>=b E²x/P. It is also zero for the entire row if the independent companion filter admits only h<=x/P. It is not in general zero for x/P<h<b E²x/P.

More precisely W is nonnegative, increasing on [1,E²], constant on [E²,b], and decreasing on [b,bE²]. This follows because the moving interval cuts only one end of [1,E²] at a time, and in the middle contains the whole interval. Its maximum is d(E-1): split the integral of R(log s) at E and integrate 1-1/s and E/s-1/E on the two pieces. In particular W has total variation 2d(E-1). The sign of the contribution after centering still depends on beta_U(h); positivity of W is not a positivity claim on that sum.

## A sufficient single-prefix bound for just the cutoff correction

Put H=x/P, H_1=bE²H and V=max(H,U). On [H,H_1] the function h^(-1) W(h/H) has supremum and total variation O_(B,d)(1/H), by the product inequality for total variation and monotonicity of h^(-1). Thus the entire deterministic cutoff correction is bounded in absolute value by
```
  O_(B,d)( P sup_(V<=T<=H_1) |sum_(V<h<=T) beta_U(h)| ).
```
If H_1<=V the correction is zero. Partial summation proves the bound without moving the locked cutoffs. The relevant signed prefix, for arbitrary real T in this interval, is exactly
```
  sum_(j<=T/U) a(j) sum_(max(U,V/j)<m<=T/j) mu_L(m).
```
This follows by expanding h=mj with m>U. Thus one sufficient condition for square-root-scale control of the cutoff correction alone is a bound O_epsilon(x^(1/2+epsilon)/P) on that single companion prefix, not separate square-root errors for every prime shell and companion. On the balanced cutoffs this would still be a strong estimate; it is not supplied. The correction can instead be included exactly in the signed sum. The hard arithmetic problem is still to bound the resulting actual two-shell difference on arbitrarily late windows. In particular, neither this identity nor the fixed cutoff localization is evidence that the remaining split-prime contributions cancel.
