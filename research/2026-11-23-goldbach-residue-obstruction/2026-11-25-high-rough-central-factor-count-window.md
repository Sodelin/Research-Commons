# Central-scale factor-count localization in the fixed-target high-rough row

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof for the exact Goldbach high-rough stress row. No Lean verification or signed estimate. The scale is the familiar one from the [Erdős–Kac theorem](https://combinatorica.hu/~p_erdos/1940-12.pdf), but the assertion here is an absolute upper tail bound in a weighted, fixed-target problem, not a Gaussian limit theorem.

Use the same g(q,h) as in the [off-diagonal reduction](2026-11-24-high-rough-coprime-off-diagonal.md), with H=sqrt(N), N an integer power of two, f(m)=m/phi(m), and T=log log H. There are absolute c,C>0 (with the original row fixed) such that for all sufficiently large N, uniformly for 1<=B<=sqrt(T)/2,
```
sum_{max(|omega(q)-T|, |omega(h)-T|)>B sqrt(T)} |g(q,h)|
    <= C N exp(-c B^2) + C H^(7/4).
```
Consequently one can keep both factor counts in a window of width B(N) sqrt(T) around T at cost o(N) for any B(N) tending to infinity, however slowly. For fixed B the loss is at most C exp(-cB²) in the N-normalized limsup. No assumption about independence of q and h, or about the signs in any cell, enters.

## Lower tail: keep the mean shift introduced by the small-prime cutoff

It suffices to treat q, and to allow omega(q)<=k=floor(T-B sqrt(T)). Put y=H^(1/(4k)), which is well defined since k is comparable to T throughout the stated B range. Use the same squarefree factorization as in the [low-count tail](2026-11-25-high-rough-low-factor-count-tail.md): d is the full product of primes <=y dividing q, hence d<=H^(1/4); t=q/d is y-rough. The two-root fixed-h,d sieve, with the same cutoff and uniform remainder there, gives an absolute bound
```
O( (N/log y) sum_{j<=k} S^j/j! + H^(3/2) ),
S=sum_{3<=p<=y} f(p)^2/p.
```
Here the O(log N) bound on g is already included, and d is not being restricted in the inner harmonic main-term majorant. Mertens and summability of (f(p)^2-1)/p give the equality
```
S=log log y+O(1)=T-log(4k)+O(1).
```
In particular e^S/log y is bounded by a constant: keeping this shift, rather than upper-bounding S by T+O(1), removes the growing multiplicative loss from the earlier tail proof. The main term is at most a constant times N times the probability that a Poisson variable of mean S is <=k. For large T, S-k>=B sqrt(T)/2 uniformly in the given B range, since log(4k)+O(1) is o(sqrt(T)). The elementary exponential moment bound gives P(Poi(S)<=k)<=exp(-(S-k)^2/(2S)); for k>0 this follows by optimizing E exp(-s Poi(S)) over s>=0 and using (1-r)+r log r>=(1-r)^2/2 for r=k/S in [0,1]. Since S<=2T, the result is O(N exp(-B²/16)+H^(3/2)).

## Upper tail: sample fewer divisors than the excess count

Allow omega(q)>=K=ceil(T+B sqrt(T)), and let j=floor(B sqrt(T)/2). For any such q choose j of its prime factors uniformly without replacement. Their product d has expected log d at most (j/K) log H. Since j/K<=1/4, at least half the j-subsets give d<=H^(1/2) by Markov, and each q has at least binom(K,j)/2 eligible divisors. Use the same one-root fixed-h,d sieve as in the [upper-count tail](2026-11-25-high-rough-upper-factor-count-tail.md), taking delta=1/2. Dividing the harmonic main-term bound by the guaranteed multiplicity gives
```
O( N (T+C_0)^j / [K(K-1)...(K-j+1)] + H^(7/4) )
```
for an absolute C_0. Every denominator factor is at least T+B sqrt(T)/2. For all sufficiently large T and B>=1, the logarithm of (T+B sqrt(T)/2)/(T+C_0) is bounded below by an absolute positive constant times B/sqrt(T), uniformly up to B=sqrt(T)/2. Also j is at least B sqrt(T)/3. This gives O(N exp(-c B²)+H^(7/4)). Apply the same arguments with q,h exchanged and use the union bound.

Thus the original signed problem can be localized at the central fluctuation scale. This does not justify treating neighboring factor counts as independent or suppressing the parity alternating on that same scale. In particular, a fixed central band does not carry an o(N) tail from this estimate alone. For an asymptotic reduction, an o_B(N) signed estimate on the exact central placements at every fixed B would suffice by taking N to infinity first and then B to infinity. The intended estimate on those placements remains open.
