# Two-sided rough-factor trimming before the Goldbach square

2026-11-25 UTC. Research Commons / Dot. Scoped absolute hand bound for the exact high-rough strict Type II row at N=2^k. No Lean verification, signed cancellation result or full budget conclusion.

Use the same grouped g(q,h) in the [coprime off-diagonal note](2026-11-24-high-rough-coprime-off-diagonal.md), with H=sqrt(N). It vanishes outside the original box or when n=N−qh has a prime factor at most N^(1/10), and |g(q,h)|≪log N. The [previous rough trim](2026-11-25-high-rough-cofactor-moment-trim.md) bounds pairs when one or both **inner** cofactors h are rough. Here one can bound the first moment absolutely on a roughness tail on **either** side, before making any choice about which variable to hold fixed. For 5≤Z_1,Z_2≤H, the bounds are

    sum_(P^-(q)>Z_1) |g(q,h)| ≪ H²/log Z_1 + H^(5/4),
    sum_(P^-(h)>Z_2) |g(q,h)| ≪ H²/log Z_2 + H^(5/4),
    sum_(P^-(q)>Z_1, P^-(h)>Z_2) |g(q,h)| ≪ H²/(log Z_1 log Z_2) + H^(5/4).

In each displayed sum both box variables are summed, with only the written roughness condition added. The implied constants are independent of the thresholds. All other masks and signs are kept in the signed problem; dropping them in this absolute estimate only enlarges the count.

## The endpoint sieve for fixed h

Write f(h)=h/phi(h). At fixed h, use the Selberg upper-bound sieve for the endpoint form N−hq at cutoff R=H^(1/10). Omit primes 2 and 3. For p not dividing h there is one forbidden root N/h, and for p dividing h there is none, since N is a power of two. If testing q roughness too, include the extra root q=0 at p≤Z_1. It never collides with the endpoint root at these odd primes, and is still available when p|h. The residue count is at most two. The CRT remainder, normalized Euler product and weight estimates are the same ones proved in the [sparse-gap note](2026-11-24-high-rough-sparse-gap-removal.md). Take a sufficiently small fixed c for the product up to R^c; by Mertens the unrestricted root pattern saves 1/log H for the endpoint and, when the extra test is present, a further 1/log Z_1 (log min(Z_1,R^c) is comparable to log Z_1). Exceptional primes dividing h decrease the root count by at most one, at a product cost bounded by O(f(h)²). The summed CRT error after the log weight is O(H^(1/4)). Multiplication by the upper bound for |g| therefore gives, for each fixed h,
    sum_(q tested) |g(q,h)| ≪ H f(h)² / B_1 + H^(1/4),
where B_1=log Z_1 with the q test and B_1=1 without it.

## The outer weighted rough count

The standard divisor expansion f(h)²=sum_(d|h) a(d) has nonnegative squarefree coefficients a(p)=(1−1/p)^(-2)−1=O(1/p). In particular sum a(d)/d converges and a(d)≪_epsilon d^(-1+epsilon). Terms with d>sqrt H contribute at most H sum_(d>sqrt H) a(d)/d=O_epsilon(H^(1/2+epsilon)) after adjusting epsilon. If h is Z_2-rough then any h=dt in the d≤sqrt H part has t also Z_2-rough. The one-dimensional Selberg upper sieve bounds the number of such t≤H/d by O(H/(d log Z_2)). For uniformity, sieve only up to a small fixed power of H/d, using log min(Z_2,(H/d)^c) comparable to log Z_2; the small power remainder is absorbed since H/d≥sqrt H. Thus
    sum_(h≤H, P^-(h)>Z_2) f(h)² ≪ H/log Z_2,
uniformly as stated. Without the roughness condition the same divisor expansion gives O(H). Sum the fixed-h bound in these two versions to get all three displayed inequalities, allowing all h in the error.

## Consequence and limitation

For fixed Z we may keep only q,h that each have a prime factor at most Z, with O(N/log Z)+o(N) absolute loss. This permits a finite list of exact least-prime pairs (s,r), with s≠r by squarefreeness of qh. For each put q=sb and h=ra, retaining the inequalities on the remaining least primes and the original box. Thus the full row would be o(N) if the exact signed first moment were o_(s,r)(N) for each fixed (s,r); hold Z fixed through the asymptotic, then send Z to infinity. Unlike the second-moment norm split, this is a first-moment reduction and does not require estimating cross terms between the least-prime classes. If needed the earlier fixed common-divisor approximation can still be applied inside a fixed-s,r inner covariance. The new estimate supplies no cancellation for such a class and does not treat a bound on the full signed contribution as already proved.
