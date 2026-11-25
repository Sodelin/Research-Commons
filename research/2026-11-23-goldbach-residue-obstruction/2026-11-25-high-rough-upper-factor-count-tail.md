# The upper factor-count tail is negligible in the strict high-rough Goldbach row

2026-11-25 UTC. Research Commons / Dot. Scoped absolute hand bound for the original fixed-target row; no signed estimate or Lean verification. This complements the [lower tail](2026-11-25-high-rough-low-factor-count-tail.md) and uses the same [fixed-opposite-factor endpoint sieve](2026-11-25-high-rough-two-sided-first-moment-trim.md).

Write H=sqrt(N), N a power of two, f(a)=a/phi(a), and T=log log H. Keep the exact weight g(q,h) supported on the original odd squarefree qh box and N^(1/10)-rough endpoint N-qh, with |g(q,h)|<<log N. For any fixed 1<c<4, choose a fixed delta with (c-1)/c<delta<3/4. Then
```
sum_{max(omega(q),omega(h))>=ceil(cT)} |g(q,h)|
  <<_{c,delta} N (log H)^(-(c log c-c+1)) + H^(5/4+delta).
```
In particular for any fixed 0<epsilon<1, both box variables may be confined to [(1-epsilon)T,(1+epsilon)T] distinct prime factors at o(N) absolute cost. The floors at the two ends may be incorporated by changing epsilon by a fixed arbitrarily small amount. These are restrictions on the placements, not on independent random models for their signs.

## Most of the sampled small divisors fit under a power cutoff

It suffices to bound the q tail. Put K=ceil(cT), j=floor((c-1)T) and take H large enough that j>=1. If q has k>=K distinct primes, select any j of them uniformly without replacement and form their product d. The mean of log d is (j/k) log q <= (j/K) log H. Consequently, by Markov, the proportion of its j-prime divisors with d<=H^delta is at least 1-j/(delta K), bounded below by a fixed positive constant under the chosen delta. In particular each such q has at least a constant times binom(K,j) different divisors of this kind. This estimate uses the average over the divisors of each individual q, not over residue classes or over targets.

## Sieve each divisor class, then divide by its guaranteed multiplicity

At fixed h,d write q=dt. Apply the original one-root endpoint sieve to N-hdt, in an interval for t of length at most H/d. At odd p not dividing hd its forbidden root is N/(hd); otherwise no root is removed because N is a power of two. The same CRT counting error per residue and the original endpoint cutoff give a weighted bound O((H/d) f(hd)^2 + H^(1/4)), after the O(log N) original weight. Using the upper sieve with a shorter interval does not require a prime asymptotic in that interval. Enlarge the count by dropping any other tests, and use f(hd)^2<=f(h)^2 f(d)^2, sum_{h<=H} f(h)^2<<H. The main term over h,d is bounded by
```
H² sum_{squarefree d<=H^delta, omega(d)=j} f(d)^2/d
  <= H² (T+O(1))^j/j!,
```
by summing ordered distinct prime factors and Mertens, since f(p)^2=1+O(1/p). Summing the weighted CRT error over all h and d costs O(H^(5/4+delta)). Divide by the guaranteed divisor multiplicity; for the error it suffices to bound this division by a constant.

The main factor after dividing is at most a constant times
```
(T+O(1))^j / [K(K-1)...(K-j+1)].
```
Its logarithm is -T times the integral of log(c-x) from 0 to c-1, plus O_c(1): the numerator's O(1) shift and the floors affect the sum by O_c(1), and the smooth Riemann sum on this interval has bounded error after multiplication by T. The integral is c log c-c+1. This proves the bound and exchanging q,h finishes. The remaining difficulty is the centered signed correlation on the joint typical-count region, not a large-deviation tail. No approximation to that signed correlation is asserted.
