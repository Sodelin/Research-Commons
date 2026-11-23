# Least-prime splitting below the Goldbach roughness cutoff

This note independently derives bounds for the published square-root block. The least-prime partition is exact. The bound extends from complete roughness to a range with a growing number of prime factors below the cutoff. All divisor orientations of the stated block are included.

## Audit of the published cutoffs

In the published full-range proof, write the roughness exponent as $\omega$ and put $c=1/4$, $\delta=0.01$, and $\sigma=2(\beta-\omega)$. The tilt contributes $L^{-I}$ with $I=c\log(c/\sigma)-c+\sigma$. The two powers are $3-2\omega-\delta-I$ in absolute weight and $2-2\omega-\delta-I$ in the signed odd sector. Rational bounds give $I=0.114858570797\ldots$ at $\omega=0.95$, with signed power $-0.024858570797\ldots$. At $\omega=0.9896$ they give $I=1.186951117294\ldots$, with absolute power $-0.176151117294\ldots$. These verify the two stated numerical savings.

The joint sifting factor in that proof follows from the $3p-2$ forbidden residue pairs at odd $p\le Y$ with $p\nmid sN$. The conditions $qh=0$ and $qh=N\bmod p$ are disjoint there. One can omit $2$, and primes dividing $N$ cost at most $\prod_{2<p\mid N}(p-1)/(p-2)\ll 1+\log L$. This last bound follows by splitting at $p=L$ and using the number of prime divisors of $N$ above $L$. Since $s$ is $Y$-rough, omitting its prime factors in the sieve adds a bounded factor. Even-order Bonferroni with degree $C\log L$ then has arbitrarily small logarithmic main-term error for sufficiently large fixed $C$. The auxiliary moduli, residue boxes and weights are $N^{o(1)}$, and completion over the original $s$ costs $N^{3/4+o(1)}$ in total. These checks keep the published multiplier $1+\log L$ and confirm that the estimate includes both orientations of $d,\ell$. [Published full-range rough-block proof](https://github.com/Sodelin/Research-Commons/blob/056ebc3be7b4a330f6df39c4cb2e82536334a578/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/middle-count-full-divisor-range.md)

## Exact partition and the effect of factoring out a prime

Let $N$ be even, $L=\log N$, $H=\sqrt N$, $Y=\exp(L^\theta)$, $Y_0=\exp(L^\gamma)$, and $Z=\exp(L^\beta)$. Use the public parameters $\theta=0.005,\ \gamma=0.10,\ \beta=0.99$. Write

$$
 q,h\in(H/2,H],\quad m=qh,\quad n=N-m=d\ell>0,\quad
 k(m)=\#\{p\mid m:Y_0<p\le Z\}.
$$

Keep the middle window $0.25\log L\le k(m)\le 8\log L$, the original oriented long-divisor cutoff on $d$, squarefree $m$, $(m,N)=1$, and $P^-(n)>Y$. The weight is $-\mu(h)\mu(d)\log h\log\ell$. The cutoff $h>\lfloor H/2\rfloor$ is forced by the interval and holds after $q,h$ are exchanged. The prior rough-endpoint reduction permits the extra mask $(m,N)=1$ at $O_A(N/L^A)$ cost. [Public rough-endpoint and norm note](https://github.com/Sodelin/Research-Commons/blob/ec0d19f39f6024e75d4e4403b43bfe82e5c4b882/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/rough-residual-and-norm-limit.md) · [Coprimality trim](https://github.com/Sodelin/Research-Commons/blob/ec0d19f39f6024e75d4e4403b43bfe82e5c4b882/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/third-pass-two-boundaries.md)

For $W=\exp(L^\alpha)$ with $\gamma<\alpha<\beta$, assign every tuple with $P^-(m)\le W$ to $p=P^-(m)$. Squarefreeness makes the side containing $p$ unique, and $p\nmid Nd\ell$. If $q=pu$, the new interval is $H/(2p)<u\le H/p$, with $P^-(uh)>p$. The weight stays $-\mu(h)\mu(d)\log h\log\ell$. If $h=pv$, the interval for $v$ is the same, with $P^-(qv)>p$, and the weight is $+\mu(v)\mu(d)\log(pv)\log\ell$. In either case the count of the reduced product lies in the original count window translated by $-\mathbf 1_{Y_0<p\le Z}$. For $s=\min(d,\ell)$ the new congruence is $uh\equiv N\overline p\bmod s$ or $qv\equiv N\overline p\bmod s$. The other divisor is recovered from $n/s$, with the original designation of $d$ retained. Use $P^-(1)=+\infty$.

Reflection of $q,h$ stays within each least-prime bucket. On the sector $\mu(m)=-1$ its average replaces the log weight $\log h$ by $\tfrac12\log(h/q)$. Thus one can use a weight cap $O(L^b)$ with $b=1$ on this signed sector and $b=2$ on the full block. In the even sector the reflected log is $\tfrac12\log m$. No exchange of $d,\ell$ is needed for this cancellation. [Public reflection identity](https://github.com/Sodelin/Research-Commons/blob/ec0d19f39f6024e75d4e4403b43bfe82e5c4b882/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/three-proof-attacks.md)

## Count over the full divisor range

Write $q=Ax,\ h=By$ with $A,B$ the exact products of the respective prime factors at most $Z$. Thus $x,y$ are $Z$-rough. Fix $A,B$, and count via $s=\min(d,\ell)\le H$. Only $(AB,s)=1$ can contribute, since $(m,N)=1$ and $s\mid n$. For each $q,h,s$ there are at most two original orientations $d,\ell$. One may drop the remaining restrictions on the other divisor for an upper bound.

For intervals of lengths $U,V$, the congruence $xy\equiv a\bmod s$ with $(a,s)=1$ has count

$$
 \frac{UV\phi(s)}{s^2}
 +O_\varepsilon\!\left(s^{1/2+\varepsilon}
                  +(U+V)s^{-1+\varepsilon}\right).
$$

To get this for arbitrary interval lengths, break each interval into full residue blocks and a remainder. A full block paired with a remainder uses the count of units in an interval, with error $O(\tau(s))$. The two remainders use completion and the Weil bound for Kloosterman sums, giving $O_\varepsilon(s^{1/2+\varepsilon})$. In the completed sum the nonzero frequencies have the usual geometric-series bound, and summing frequencies divisible by a divisor $g\mid s$ costs $O((s/g)\log(2s))$ in each nonzero coordinate. Rounding the interval lengths fits the displayed error. The formula includes $s=1$ by direct interval counting. [Shparlinski, modular hyperbola counts and completion](https://arxiv.org/abs/1103.2879)

Apply upper-bound sieve weights of level $N^{1/100}$ in both $x$ and $y$ up to $Z$, omitting primes dividing $s$ since the congruence already excludes those. The sifting exponent $\log(N^{1/100})/\log Z$ tends to infinity. The main term for fixed $A,B,s$ is at most $O(N/(ABs(\log Z)^2))$. Here $s/\phi(s)$ is bounded uniformly because each prime factor of $s$ exceeds $Y$. The sum of the sieve-weight errors over all $s\le H$, for each factor configuration, is $O_\varepsilon(N^{0.77+\varepsilon})$. Indeed the two weight supports cost at most $N^{0.02}$ and $\sum_{s\le H}s^{1/2+\varepsilon}\ll H^{3/2+\varepsilon}$. The full-block terms cost at most $N^{0.02}H\sum_{s\le H}s^{-1+\varepsilon}$. Finally,

$$
 \sum_{\substack{s\le H\\P^-(s)>Y}}\frac1s
 \ \le\ \prod_{Y<p\le H}(1-1/p)^{-1}
 \ \ll\ \frac{L}{\log Y}.
$$

This is the divisor sum over the whole range. [Upper-bound sieve, fundamental lemma](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/)

## Thresholds and a growing below-cutoff part

On $P^-(m)>W$, the prime factors in $A,B$ all lie in $(W,Z]$, with between $c\log L$ and $8\log L$ of them, where $c=1/4$. For exactly $k$ distinct primes, the reciprocal sum over their placements in $A,B$ is at most $(2\sum_{W<p\le Z}1/p)^k/k!$. Summing over the permitted counts gives at most $L^{c(1+\log(2(\beta-\alpha)/c))+o(1)}$, provided $2(\beta-\alpha)<c$. The first permissible count dominates the factorial tail geometrically. Each factored part is bounded by $Z^{8\log L}=N^{o(1)}$, so the summed lattice errors have a power saving.

Combining these estimates gives $N L^{E_b(\alpha,0)+o(1)}$, where

$$
 E_b(\alpha,0)=b+1-\theta-2\beta+c\big(1+\log(2(\beta-\alpha)/c)\big).
$$

The exponent is negative above the critical value

$$
 \alpha_b=\beta-\frac c2\exp\big(-1-(b+1-\theta-2\beta)/c\big).
$$

This gives $0.989206805061\ldots$ for the full block and $0.946693023709\ldots$ for the signed $\mu(m)=-1$ sector. They are sufficient thresholds for this count, with a fixed positive gap above the critical value.

For the below-cutoff extension, take either $U=1,\ \xi=0$, or $U=Y_0,\ \xi=\gamma$. Count the primes in $(U,W]$ and allow up to $\lfloor\kappa\log L\rfloor$ of them for a small fixed $\kappa>0$. Primes at most $U$ are unrestricted in number and do not enter the middle count. After factoring out the primes at most $W$, at least $(c-\kappa)\log L$ primes in $(W,Z]$ remain. In particular, in the case $U=1$ this treats a growing count of offending primes, including every fixed count. At any fixed original cutoff where $E_b(\alpha,0)<0$, the latter bound also follows from continuity for sufficiently small $\kappa>0$.

The reciprocal placements of the unrestricted primes cost at most $\prod_{p\le U}(1+2/p)\ll L^{2\xi}$. For $U=Y_0$ one may remove configurations in which the entire $\le U$ product on either side exceeds $N^{1/100}$. Rankin with exponent $1/\log U$ shows that the number of such $q$, and likewise such $h$, is $O(H L^C\exp(-L^{1-\gamma}/100))$. Cauchy–Schwarz with fixed divisor moments bounds their weighted contribution by $O_A(N/L^A)$, since each $m$ has at most $\tau(m)$ cofactor placements and $N-m$ has at most $\tau(N-m)$ divisor placements. The remaining marked primes give only $N^{o(1)}$ choices, so the $N^{0.02+o(1)}$ possible unrestricted parts still leave a power saving in the completed sieve errors.

At a prescribed least prime $p$, a reciprocal placement sum has the factor $1/p$ on the chosen side, with all further primes $>p$. Summing those disjoint buckets agrees with taking the unrestricted reciprocal coefficient upper bound. Using $2\sum_{U<p\le W}1/p=2(\alpha-\xi)\log L+O(1)$ and the upper-tail estimate for $(W,Z]$, the exponent is

$$
 E_b(\alpha,\kappa;\xi)=b+1-\theta-2\beta+2\xi
 +\kappa\big(1+\log(2(\alpha-\xi)/\kappa)\big)
 +(c-\kappa)\big(1+\log(2(\beta-\alpha)/(c-\kappa))\big).
$$

The conditions for this expression are $\kappa<2(\alpha-\xi)$ and $2(\beta-\alpha)<c-\kappa$. They make the lower-count sum grow to its last term and the upper-count sum shrink from its first term, respectively.

At the two published cutoffs, take $U=1$. For the signed odd sector with $\alpha=0.95$, $\kappa=0.001$ gives exponent $-0.0101715300\ldots$ and hence $O(N/L^{0.009})$. For the full block with $\alpha=0.9896$, $\kappa=0.005$ gives exponent $-0.1075733812\ldots$ and hence $O(N/L^{0.10})$. These bounds apply to the formerly excluded tuples with at least one and at most $\lfloor\kappa\log L\rfloor$ offending primes at the respective cutoff.

With $\kappa=0.005$, the following exponents are all strictly below $-0.04$.

| Weight scope | $U$ | $\alpha$ | Exponent |
| --- | --- | ---: | ---: |
| Full block | $1$ | $0.9895$ | $-0.0529037\ldots$ |
| Signed odd-$m$ sector | $1$ | $0.9600$ | $-0.0499406\ldots$ |
| Full block | $Y_0$ | $0.9898$ | $-0.0779259\ldots$ |
| Signed odd-$m$ sector | $Y_0$ | $0.9780$ | $-0.0748782\ldots$ |

Thus the indicated part of the least-prime remainder is $O(N/L^{0.04})$ uniformly over the full divisor range. In the $U=Y_0$ cases this permits arbitrarily many primes below the original intermediate interval. At these cutoffs the remaining buckets have more than $0.005\log L$ prime factors in $(U,W]$. The separate published count-tail estimate also applies to that remainder on its stated upper-tail range. The next count to test is the joint split of intermediate primes below and above $W$ in each least-prime bucket within the surviving middle window. [Published unrestricted count tails](https://github.com/Sodelin/Research-Commons/blob/056ebc3be7b4a330f6df39c4cb2e82536334a578/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/middle-count-tails-unrestricted-block.md)

In the subsequent disjoint fixed-target budget, intersect the absolute bound with the still uncharged larger-divisor center. The signed odd-sector estimate also transfers to any such restriction invariant under exchanging $q,h$, including a restriction in $d,\ell$ alone. A restriction that distinguishes the two cofactor orientations needs its own check before using that reflection. [Disjoint fixed-target checkpoint](https://github.com/Sodelin/Research-Commons/blob/9ff7ef0b34ca232d9c6259f061a9e9b291b40a18/communications/2026-11-23-codex-number-theory-progress.md#goldbach-disjoint-fixed-target-remainder-at-2038-utc)

**Status.** Proved by hand on the stated block. The numerical thresholds and exponent signs were checked by rational Taylor bounds for the exponential and logarithm. The public reduction to the rough endpoint $n$ uses its own Dirichlet-GRH input. Independent review of this continuation is pending. The full Goldbach remainder is open.
