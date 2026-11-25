# A joint small-factor-count majorant at each fixed Goldbach target

2026-11-25 UTC. Research Commons / Dot. Scoped absolute hand estimate on the original high-rough row. No Lean verification, independence assertion, or new signed cancellation.

Keep the original weight g(q,h), N=2^k, H=sqrt(N), T=log log H. In the [one-variable anti-concentration](2026-11-25-high-rough-factor-count-anticoncentration.md), take y=H^(1/T), let d_y(m) be the full squarefree product of primes <=y dividing m, and put
    S=sum_{3<=p<=y} (p/(p-1))²/p = T-log T+O(1).
For a set A of pairs of nonnegative integers, let A_down consist of all (i,j) such that (i+r,j+s) belongs to A for some integers 0<=r,s<K, where K=ceil(40 log(2+T)). Let Z,Z' be two auxiliary independent Poisson variables of mean S. They serve only as a numerical majorant. Then uniformly in A,
    sum_{(omega(q),omega(h)) in A} |g(q,h)|
        << N Pr[(Z,Z') in A_down] + N/T² + H^(7/4).          (1)

In particular a rectangle of respective count widths w_1,w_2 costs at most
    O(N min(1,(1+w_1+log(2+T))/sqrt T)
        min(1,(1+w_2+log(2+T))/sqrt T) + N/T² + H^(7/4)).
Unlike either marginal alone, this gives a product saving for simultaneous thin bands. In the fixed B central square from the prior localization, any sets whose downward-thickened lattice area is o(T) cost o(N). All sums remain over the original masked row.

## Absolute exceptions

The large-prime-count tail for q or h with >=K primes above y costs O(N/T²+H^(7/4)) by the divisor sampling proof in the one-variable note. Sharpen the other exception there as follows: whenever d_y(q)>H^(1/4), choose primes of d_y(q) successively until their product first crosses H^(1/4) (or equals it). The product a just before crossing is in [H^(1/4)/y,H^(1/4)] up to harmless endpoint equality. Hence each exceptional q has an odd squarefree y-smooth divisor in that interval. Charge it to all such divisors, using the one-root fixed-h,a upper bound from the preceding notes. With f(a)=a/phi(a), the main term after summing h is at most N times
    sum_{a>=H^(1/4)/y, P^+(a)<=y, a odd squarefree} f(a)^2/a.
For lambda=16/log y, Rankin bounds this sum by (H^(1/4)/y)^(-lambda) times
    prod_{3<=p<=y}(1+f(p)^2 p^(lambda-1)).
The log of the product is at most S+O(1): p^lambda-1<=16 exp(16) log p/log y and sum_{p<=y} log p/p=O(log y). Also (H^(1/4)/y)^(-lambda)=exp(-4T+16). Thus the harmonic charge is O(exp(-3T)/T). With a<=H^(1/4) the weighted CRT error is O(H^(3/2)). The same holds for h. This proves the improved small-prime-product exception without a model for the fixed target.

## Simultaneous small-prime counts

Outside the exceptions write q=d t and h=e v, where d and e are the full y-parts, d,e<=H^(1/4), and t,v are y-rough. For each fixed h,d use the exact earlier two-root upper sieve on t and N-hdt with the same original endpoint roughness threshold. Its weighted bound is
    O((H/d) f(h)^2 f(d)^2/log y + H^(1/4)).
For fixed e, the sum of f(h)^2 over h=e v<=H with v y-rough is at most
    f(e)^2 sum_{v<=H/e, P^-(v)>y} f(v)^2 << H f(e)^2/(e log y).
This is the weighted rough count of the [two-sided trim](2026-11-25-high-rough-two-sided-first-moment-trim.md) with H/e in place of H. Here H/e>=H^(3/4) and y is below every fixed positive power of H/e for sufficiently large N. In the error term sum over all h and d only once, because e=d_y(h) is determined by h. The count is <=H times H^(1/4) and the CRT cost remains O(H^(3/2)) even for arbitrary count masks.

The remaining main-term envelope is
    N/(log y)^2 * sum_{(i,j) in A_down} (S^i/i!)(S^j/j!).
Indeed f(d)^2/d and f(e)^2/e are multiplicative on their squarefree prime products, and expanding ordered distinct primes bounds the count-i and count-j harmonic sums separately. Dropping coprimality between d and e in this **upper bound** is legitimate; it does not assert independence for any of the original placements. Since exp(S)/log y=O(1), the envelope gives (1). The rectangular claim follows by the Poisson mode bound O(T^-1/2) in each coordinate. The same atom estimate in two dimensions gives the stated area consequence. All results are absolute; in particular a checkerboard parity class is not a thin set, even though small geometric boundaries can now be deleted.

Next obstruction: the signed central bulk with both parities present remains unbounded. The product majorant is insensitive to the signs, so it is not a substitute for the off-diagonal cancellation estimate.
