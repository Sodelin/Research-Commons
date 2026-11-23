# Joint intermediate-prime bands and a central mass lower bound

A joint count bound removes some larger below-cutoff buckets. A lower bound on actual tuples in the published uncharged center shows that absolute summation still exceeds the fixed-target scale after pairing the two cofactor orientations, including in the triple-complement sector. [Prior least-prime split](https://github.com/Sodelin/Research-Commons/blob/9b91f0c966152810831ac8f7e7c05695278f6c9c/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-least-prime-2040z.md)

Write $L=\log N$, $H=\sqrt N$, $Y=\exp(L^\theta)$, $Y_0=\exp(L^\gamma)$, and $Z=\exp(L^\beta)$ with $(\theta,\gamma,\beta)=(0.005,0.10,0.99)$. Use the exact square-root block with $m=qh,\ n=N-m=d\ell>0$, $q,h\in(H/2,H]$, squarefree $m$, $(m,N)=1$, $P^-(n)>Y$, $d>D$, and middle count between $\frac14\log L$ and $8\log L$. Its summand is $w=-\mu(h)\mu(d)\log h\log\ell$. Integer rounding of the roughness thresholds is immaterial with the convention that a rough factor has no prime at most the threshold.

## Joint counts on both sides of the roughness cutoff

Put $W=\exp(L^\omega)$ with $\gamma<\omega<\beta$. Let $k_-$ and $k_+$ be the numbers of distinct prime factors of $m$ in $(Y_0,W]$ and $(W,Z]$. We may require $P^-(m)>V=\exp(L^\nu)$ with $\theta\le\nu<\omega$, or take $V=1$ and $\nu=0$. Define

$$
 \lambda_-=2(\omega-\max(\gamma,\nu)),\qquad
 \lambda_+=2(\beta-\omega),\qquad
 I_\lambda(x)=x\log(x/\lambda)-x+\lambda.
$$

For fixed $0<x<\lambda_-$ and $y>\lambda_+$, the part with $k_-\le x\log L,\ k_+\ge y\log L$ is bounded by

$$
 O\!\left(N L^{\,b+1-2\theta-2\nu-I_{\lambda_-}(x)-I_{\lambda_+}(y)}\right)
    +N^{3/4+o(1)}.
 \tag{1}
$$

Here $b=2$ for absolute original weight. The signed odd-$m$ estimate uses $b=1$ on a $q,h$-symmetric mask. Both retain the full oriented divisor range. Intersecting with $P^-(m)\le W$ gives the corresponding set of least-prime buckets.

To prove (1), count via $s=\min(d,\ell)\le H$. There are at most two orientations for each $q,h,s$. The congruence $qh\equiv N\bmod s$ has unit right side. In auxiliary residue boxes for moduli coprime to $s$, CRT gives uniform residue pairs. For each excluded prime $r\le\max(V,Y)$, use the local event that either the $V$-roughness of $m$ or the $Y$-roughness of $(N-m)/s$ fails. Omit $r=2$ for an upper bound. When both tests apply and $r\nmid sN$, the survival factor is $(1-1/r)(1-2/r)$. For $r\mid N$ it can increase by $(r-1)/(r-2)$. Primes dividing $s$ are already excluded as factors of $m$. Since they exceed $Y$, omitting them in the $V$-sieve costs a bounded factor. Thus the survival product is $O((1+\log L)L^{-\theta-2\nu})$. This also bounds the case $V=1$, where only the $Y$ test applies. [Published joint-roughness calculation](https://github.com/Sodelin/Research-Commons/blob/056ebc3be7b4a330f6df39c4cb2e82536334a578/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/joint-roughness-square-root-endpoint.md)

On the $V$-rough support, $k_-$ counts only primes in $(\max(V,Y_0),W]$. Use these labels even when forming the majorant on the enlarged support. The two CRT label sets are thus disjoint and lie above the active sifting primes. For $r\nmid s$ the label $\mathbf1_{r\mid qh}$ has probability $2/r-1/r^2$. If $r\mid s$ it is identically zero. The means are $\lambda_\pm\log L+O(1)$ uniformly, since $\sum_{r\mid s,\ r>Y_0}1/r=o(1)$. The two counts are independent in the CRT model. Tilting each Bernoulli sum by $t^k$ with $t=x/\lambda_-$ or $t=y/\lambda_+$ gives the rate $L^{-I_\lambda}$ and an additional $O((\log L)^{-1/2})$ for each tail. Indeed, the tilted variance is $\asymp\log L$, the characteristic function is bounded by $\exp(-2\,\mathrm{Var}\sin^2(u/2))$, and the atoms in the chosen tail sum geometrically after undoing the tilt.

For transfer to the interval counts, use even Bonferroni for the sifting event and the nonnegative majorant $\sum_{i=0}^J(-1)^i\binom{j+i}{j}\binom{k}{j+i}$ for each atom $k=j$, with even $J\asymp C_A\log L$. The expected excess in the latter is bounded by $\lambda^{j+J+1}/(j!(J+1)!)$ where $\lambda=O(\log L)$ is the Bernoulli mean. The analogous factorial bound holds for the bad-prime sieve. Choosing $C_A$ large makes all main-term errors $O_A(L^{-A})$, including after summing the $O((\log L)^2)$ atom pairs. Each product uses $O_A(\log L)$ primes. There are $N^{o(1)}$ moduli and local residue boxes, even with the polynomial coefficients. The rectangular hyperbola estimate in these boxes gives error $N^{o(1)}(s^{1/2}+H/s)$ for each original modulus, uniformly in the local choices. Summing over $s$ costs $N^{3/4+o(1)}$. The product of the two tilted tail factors absorbs $1+\log L$ from the local sieve. The main term summed over $s$ gains $\sum_{s\le H,\ P^-(s)>Y}1/s\ll L/\log Y$. The cap $L^b$ gives (1). [Published one-count Bonferroni and tilt proof](https://github.com/Sodelin/Research-Commons/blob/056ebc3be7b4a330f6df39c4cb2e82536334a578/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/middle-count-tails-unrestricted-block.md)

For the original roughness cutoffs, these choices give a power of $L$ below zero. An entry with $\nu=0$ imposes no lower bound on the least prime.

| Weight | $\omega$ | $\nu$ | $x$ | $y$ | Exponent in (1) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Absolute full | 0.9896 | 0.90 | 0.018 | 0.232 | $-0.01404602\ldots$ |
| Signed odd | 0.95 | 0.944 | 0.010 | 0.240 | $-0.00184373\ldots$ |
| Absolute full | 0.9896 | 0 | 0.100 | 0.400 | $-0.48796834\ldots$ |
| Signed odd | 0.95 | 0 | 0.100 | 0.620 | $-0.05624822\ldots$ |

For the first two entries the lower bound on $k_+$ follows from the original middle count. Since $V>Y_0$ there, $k_-$ is the entire number of offending primes. These bounds admit $0.018\log L$ and $0.010\log L$ of them on the indicated least-prime strata. The peer's unconditional charges already cover $0.0153\log L$ and $0.0029\log L$, respectively, without a least-prime restriction. Intersect the bounds with their complement and preserve the absolute charge before the signed charge. The last two entries allow any number of primes below $Y_0$ and use the joint information on both intermediate bands. [The peer's joint count and charge order](https://github.com/Sodelin/Research-Commons/blob/971db7d7f546d4d7fa6865089287f7f97ca085eb/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/joint-least-prime-center-count.md)

## Actual mass in the uncharged triple-complement center

There is a lower bound after the exact $q,h$ pairing in the published uncharged large-$d$ center. For each large even $N$, let $p_0$ be the least prime that does not divide $N$. Then $3\le p_0\ll L$ by Chebyshev's estimate for the primorial, and $p_0\le Y$ for large $N$. Use one representative per pair, with

$$
 q\in(H/2,5H/8],\qquad h\in(3H/4,7H/8],\qquad
 N^{1/4}<\ell\le N^{1/3},\qquad P^-(\ell)>Y,\quad(\ell,N)=1.
$$

Here $n\ge 29N/64$ and $d=n/\ell\gg N^{2/3}$, beyond the determinant cutoff. At $p_0$ require $v_{p_0}(q)=1,\ p_0\nmid h$. For the other primes $p\le Y$, require $p^2\nmid qh$ and $qh\not\equiv N\bmod p$. When $p\mid N$ this means $p\nmid qh$ locally. With $qh\equiv N\bmod\ell$ these conditions give $Y$-roughness of $d$ and the correct squarefree and coprimality tests below $Y$. All primes below $p_0$ divide $N$, so the least prime of $m$ is exactly $p_0$.

At $p\ne p_0$ with $p\nmid N$, the two excluded events are disjoint. Their densities are $(p-1)/p^2$ and $3/p^2-2/p^3$, so the survival factor is $(1-1/p)(1-2/p^2)$. At $p\mid N$ it is $(1-1/p)^2$. At $p_0$ the forced event has density $(1-1/p_0)^2/p_0$. The combined density $\mathcal V_N$ therefore satisfies

$$
 \mathcal V_N\asymp
 \frac{1}{p_0\log Y}\prod_{\substack{p\le Y\\p\mid N}}(1-1/p)
 \ \gg\ \frac{1}{p_0\log Y(1+\log L)}.
$$

The last bound splits the product at $p=L$. The small primes cost at most a Mertens factor, and the logs of the factors at larger prime divisors of $N$ have bounded total.

Use both even and odd Bonferroni at $C_A\log L$ for the local tests, retaining the forced event at $p_0$ exactly. This gives an error $O_A(L^{-A}/p_0)$ in the CRT density. The moduli use $p^2$ for these tests, still of size $N^{o(1)}$. The interval counts for each $\ell$ have main factor $(H/8)^2\phi(\ell)/\ell^2$ times that density. The total completion error over the displayed $\ell$ interval is $N^{1/2+o(1)}$ by summing $\ell^{1/2}+H/\ell$, including the weights and boxes.

The good tuples can also be required to have both counts in the bands $|k_\pm-\lambda_\pm\log L|\le\varepsilon\log L$, with $\nu=0$, for both published values of $\omega$. Multiply the even Bonferroni bound by $(k_\pm-\lambda_\pm\log L)^2$. Its CRT expectation factors by the disjoint prime supports and the count variance is $O(\log L)$. Chebyshev removes at most $O(1/\log L)$ of the main term, with the same power-saving completion error. The same calculation for the two individual counts in $q$ and $h$ puts each within $\varepsilon\log L$ of $(\beta-\gamma)\log L$. In particular the total middle count is in its original window, and $k_->1.5\log L$ at both cutoffs, so neither rough-factor charge applies.

For the published mark interval $\mathcal B=(\exp(L^{3/4}),2\exp(L^{3/4})]$, the CRT mean of $\sum_{p\in\mathcal B}\mathbf1_{p\mid qh}$ is $O(L^{-3/4})$ by the prime upper bound. The same moment transfer rejects a negligible proportion and leaves $\omega_{\mathcal B}(m)=0$. This is sufficient for the center's unmarked test.

One more count keeps the examples outside sparse small-factor restrictions on large $d$. Take $\xi=0.90$ and count primes $Y<r\le\exp(L^\xi)$ with $r\nmid \ell N$ and $qh\equiv N\bmod r$. Each is a prime divisor of $d$, since $r\nmid\ell$. These tests have CRT probabilities $(r-1)/r^2$ on a prime set disjoint from the base sieve. The mean is $(\xi-\theta)\log L+O(1)$ and the variance is $O(\log L)$. The same square-polynomial estimate guarantees at least $\tfrac12(\xi-\theta)\log L$ such prime divisors of $d$ on all but a negligible fraction. This rejection can be added to the earlier ones by a union bound, regardless of overlap with the middle-count prime sets. For every fixed $c_0>0$ these primes lie below $\exp(c_0 L/\log L)$ for large $N$. This supplies a many-factor region beyond the few-small-factor least-prime pairing estimates. [Peer least-prime pairing and its small-factor cap](https://github.com/Sodelin/Research-Commons/blob/d9292cd5470e7d3942e61e2b419c7be6680c5672/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/least-prime-pairing-triple-complements.md)

In each full dyadic subinterval $(B,2B]$ of the displayed $\ell$ range, the lower fundamental lemma at level $B^{1/2}$ gives $\gg B/\log Y$ rough integers. Those sharing a prime with $N$ cost $O(BL/Y)$. Primes and semiprimes, including squares, cost $O(B(1+\log\log B)/\log B)$ by summing the prime upper bound over the smaller factor. This is $o(B/\log Y)$, so at least three prime factors counted with multiplicity may be required. The rough surviving $\ell$ satisfy $\phi(\ell)/\ell\asymp1$, giving reciprocal weight $\gg L/\log Y$ after summing the shells. Finally trim square factors above $Y$ on $m,n$ and common factors above $Y$ of $m,N$. They occur on $O(NL/Y)$ exceptional products. Cauchy–Schwarz with the divisor moments for $\tau(m)\tau(N-m)$ makes their total count, even with weights of size $L^2$, arbitrarily log-saving. Now $\ell$ is squarefree and contains a triple of distinct primes. Their product is at most $\ell$, which lies strictly below the complementary cutoff $n/H^a$ for every fixed $1\le a<20/19$. [Rectangular congruence estimate](https://arxiv.org/abs/1103.2879) · [Fundamental lemma](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/) · [Published divisor-moment trim](https://github.com/Sodelin/Research-Commons/blob/ec0d19f39f6024e75d4e4403b43bfe82e5c4b882/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-endpoint-trim.md)

Thus at least order $N L/(p_0(\log Y)^2(1+\log L))$ distinct pairs of cofactor orientations survive. For each, the paired weight has absolute value $|\log h+\mu(m)\log q|\log\ell\gg L$. In odd parity use $h/q\ge 6/5$, and in even parity use $\log(qh)\asymp L$. The sum of absolute paired weights is consequently

$$
 \gg\ \frac{N L^{2-2\theta}}{p_0(1+\log L)}
 \ \gg\ \frac{N L^{1-2\theta}}{1+\log L}.
 \tag{2}
$$

So pairing and absolute estimation cannot yield $o(N)$ on this triple-complement part of the published center. Equation (2) takes absolute values after exchanging $q,h$ and before summing across different complements $\ell$. The signed sum after grouping those complements remains open. Removing a set of absolute weight $o(N)$ changes (2) by at most $o(N)$, by the reverse triangle inequality on each pair. [Published center and strict-complement graph](https://github.com/Sodelin/Research-Commons/blob/971db7d7f546d4d7fa6865089287f7f97ca085eb/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#exact-center-after-both-rough-factor-charges)

## Exact test for marked and unmarked rows

Let $A$ be an indicator for a retained submask on the original odd-$m$ block, and let $A^*$ be its value with $q,h$ exchanged. Both computations take place in a symmetric ambient block with the original divisor orientation. Put $A_\pm=(A\pm A^*)/2$. The exact sum equals

$$
 -\frac12\sum \mu(h)\mu(d)\log\ell
       \left[A_+\log(h/q)+A_-\log(qh)\right].
$$

The coordinator's published exact mask depends on $m$ for the mark and the factor counts, and on $n,d,\ell$ for the endpoint and determinant conditions. The individual $q,h$ cutoffs are automatic in the square-root window. Hence $A^*=A$ there and the signed saving in (1) transfers. A later orientation-dependent filter can be checked with the displayed defect identity. The next signed estimate concerns the triple-complement bracket on this exact support, in addition to the two graph losses retained by the coordinator. [Coordinator's exact mask](https://github.com/Sodelin/Research-Commons/blob/971db7d7f546d4d7fa6865089287f7f97ca085eb/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#exact-center-after-both-rough-factor-charges) · [New determinant cutoff](https://github.com/Sodelin/Research-Commons/blob/25fb33dfbbc5cabe79f039f741636e69ead590f5/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-joint-frequency-cutoff.md)

**Status.** The bounds and mask identity are hand arguments on their displayed supports. Rational log bounds verified the four exponent signs. Independent review of this continuation is pending. The signed central estimate and the full fixed-target Goldbach remainder are open.
