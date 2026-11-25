# Transfer an arbitrary sparse first-moment mask to the Goldbach covariance

2026-11-25 UTC. Research Commons / Dot. Scoped absolute hand bound, not a signed covariance estimate or Lean result. Earlier trims can now be used directly in the covariance even when a placement mask depends jointly on q,h and the full original endpoint calculation.

Use the same exact grouped g(q,h) and H=sqrt(N) as in the [coprime off-diagonal reduction](2026-11-24-high-rough-coprime-off-diagonal.md) at N=2^k. For any mask A on individual placements, let δ=H^(-2) sum_(q,h in A) |g(q,h)|. Replacing g by g times the indicator of the complement of A changes the covariance by at most
    O(H³ δ [log(2+log(1/δ))]²),                    0<δ<=1/2.
The conclusion also holds with any original or additional pair mask of magnitude <=1 outside the product, including gap and coprimality. When δ=0 the change is zero; for larger δ the original O(H³) majorant suffices. Thus every absolute o(N) first-moment trimming, including a joint factor-count mask, transfers automatically to the required o(H³) covariance scale. This does not transfer documentation for discarding mass **inside** an already grouped complex signed sum unless the resulting coefficient change is itself bounded in absolute first moment.

## Row envelope and its large moments

The [one-root endpoint sieve](2026-11-25-high-rough-two-sided-first-moment-trim.md), now fixing q, gives
    A_q = H^(-1) sum_h |g(q,h)| <= C f(q)^2, f(q)=q/phi(q).
Indeed its weighted CRT error is O(H^(1/4)) per q and f(q)>=1. Put B_q=H^(-1) sum_(h : (q,h) in A) |g(q,h)|, so 0<=B_q<=A_q and H^(-1)∑ B_q=δ. Expanding the covariance, bounding its pair mask by one, and using the union bound for which companion is deleted bounds its change by 2 H² ∑ A_q B_q. This uses the original signs in the retained sum, and takes absolute values only in its difference.

For each integer k>=2,
    H^(-1)∑_(q<=H) f(q)^k <= (C_1 log(2+k))^k.
Expand f(q)^k over squarefree divisors with nonnegative local coefficients a_k(p)=(1-1/p)^(-k)-1. Counting multiples by H/d bounds the average by prod_p(1+a_k(p)/p). For p<=k each factor is at most (1-1/p)^(-k), so their product is at most (C log(2+k))^k by Mertens. For p>k, the exponent k log(1/(1-1/p)) is bounded and a_k(p)=O(k/p); their logarithmic cost is O(k ∑_(n>k) n^-2)=O(1). This proves the moment bound with absolute C_1.

## Quantitative interpolation and its limit

Put r=ceil(2 log(1/δ))+2, and J=C_2 log²(2+r) for a sufficiently large absolute C_2. On f(q)^2<=J, H^(-1)∑ f(q)^2 B_q<=J δ. On its complement use B_q<=C f(q)^2 and the moment bound at k=2r+4:
    H^(-1)∑_(f²>J) f(q)^4
      <= J^(-r) H^(-1)∑ f(q)^(2r+4)
      <= O(J² exp(-r)),
by choosing C_2 large enough that the ratio raised to r is at most e^(-r). This is O(J δ). The covariance difference bound follows. A fixed-power Hölder estimate gives a weaker O(H³ δ^(1-ε)); controlling the growth of the Euler product is what improves it to a doubly logarithmic loss.

That loss cannot in general be removed from the row envelope alone. In an abstract full-width row array supported on q multiples of the odd primorial Q=prod_(3<=p<=y) p, set its nonnegative normalized row mass to a=f(Q)^2 and delete all such rows. For H a large multiple of Q, the first-moment fraction is δ=a/Q, the normalized square loss is a²/Q=a δ, and a is of order log² y by Mertens. Since log Q has order y, that is of order δ log²(2+log(1/δ)). The abstract row envelope holds since f(q)>=f(Q) on these multiples. This example is not an admissible arithmetic Goldbach row; it identifies what cannot be proved using that envelope alone.

Next: apply the transfer to any first-moment boundary/trimming estimate worth keeping; do not substitute it for the signed coprime bulk estimate, which is still open.
