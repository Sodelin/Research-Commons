# Thin factor-count bands in the exact fixed-target high-rough row

2026-11-25 UTC. Research Commons / Dot. Scoped absolute hand proof, no Lean verification or signed cancellation result. Combines the [two-sided endpoint sieve](2026-11-25-high-rough-two-sided-first-moment-trim.md) and the [divisor-multiplicity argument](2026-11-25-high-rough-upper-factor-count-tail.md) without a distribution assumption about the fixed target.

Keep H=sqrt(N), T=log log H, N=2^k, f(d)=d/phi(d), and exactly the same g(q,h) as in the [central-scale result](2026-11-25-high-rough-central-factor-count-window.md). Uniformly in a real interval I of length w>=0, for sufficiently large N,
```
sum_{omega(q) in I} |g(q,h)|
  << N min(1, (1+w+log(2+T))/sqrt(T)) + H^(7/4).
```
The identical result holds for h. In particular, any interval of o(sqrt(log log N)) factor counts costs o(N) absolutely, uniformly in its location, including a single prescribed count. A whole parity class is not such an interval and is not removed.

## Count only small primes, without taking a mean-value model for the endpoint

Put y=H^(1/T) and let d_y(q) be the complete squarefree product of primes p<=y dividing q on this support. Its logarithm is the sum of log p over such p. For fixed h,p, the one-root sieve in q=pt gives absolute bound O((H/p)f(hp)^2+H^(1/4)), already including the O(log N) weight of g. Enlarge the support only in the upper bound. Therefore
```
sum_{q,h} |g(q,h)| log d_y(q)
  << N sum_{p<=y} f(p)^2 log(p)/p
       + H^(5/4) sum_{p<=y} log p
  << N log y + H^(5/4)y.
```
Here sum_h f(h)^2=O(H), f(hp)<=f(h)f(p), and the last bounds use the standard prime harmonic estimate with log weight and Chebyshev. Markov at log d_y(q)>(log H)/4 shows that d_y(q)>H^(1/4) costs O(N/T+H^(5/4+o(1))).

For the other terms, write q=dt with d=d_y(q)<=H^(1/4); then t is y-rough. At a fixed value j of omega(d), the two-root sieve in t and N-hdt used in the [lower-tail proof](2026-11-25-high-rough-low-factor-count-tail.md) gives
```
sum_{omega(d_y(q))=j, d_y(q)<=H^(1/4)} |g(q,h)|
 << (N/log y) S^j/j! + H^(3/2),
S=sum_{3<=p<=y} f(p)^2/p=T-log T+O(1).
```
The weighted CRT errors cost O(H^(3/2)) even if all d are counted in one bound; multiplying this error by the number of j-values is therefore unnecessary for an interval. Since e^S/log y is bounded and the mode of a Poisson law of mean S has mass O(1/sqrt(S)) by Stirling's formula, each small-prime count contributes at most O(N/sqrt T) in the main term. For a union of j-values, one can sum just those Poisson masses and retain one CRT error.

## Few large prime factors, with a stronger tail than a first moment

Let K=ceil(40 log(2+T)) and l=floor(K/4). If q has at least K distinct prime factors greater than y, sample l of those factors uniformly without replacement. The expected log of their product is at most (l/K) log H. At least half of those subsets produce a divisor a<=H^(1/2). For each q this supplies at least binom(K,l)/2 eligible divisors a all of whose primes exceed y. Apply the one-root sieve at each fixed h,a, and divide by the guaranteed count, just as in the upper-tail proof. The error is O(H^(7/4)). The harmonic sum for these primes satisfies
```
S_large=sum_{y<p<=H} f(p)^2/p=log T+O(1).
```
Thus the main term is O(N [S_large/(K-l+1)]^l), at most O(N/T²) uniformly for large T (eventually the ratio is at most 1/10 and l>=9 log T). There is no assertion that the large and small counts are independent.

Outside the two exceptional sets, omega(q)=omega(d_y(q))+j_large with 0<=j_large<K. If omega(q) is in I, then omega(d_y(q)) lies in the inflated interval with the same upper endpoint and lower endpoint decreased by K. The number of possible integer counts there is O(1+w+log(2+T)). Apply the Poisson atom bound and the shared CRT error. For wider intervals apply the original unconditioned O(N+H^(5/4)) first-moment majorant instead. This proves the display.

The result permits deletion of a few narrow transition bands in the exact signed problem. It does not control a block of width comparable to sqrt(T), prove a local limit law, or pair even and odd counts. The signed bulk estimate is still open.
