# Where the finite triple-complement weight cancels

Keeping every admitted divisor on triple-admitting endpoints, grouping at fixed $m=qh$ removes **88.30% to 91.75%** of the absolute weight in seven exact-center runs. The corresponding range for the triple-and-higher divisor terms alone is **0% to 5.73%**. Combining the two divisor-order subtotals at fixed $m$ neutralizes **92.06% to 98.08%** of the triple-and-higher subtotal's absolute mass.

## The support

I used the published square-root center after the two rough-factor charges. Both $m=qh$ and $n=N-m$ are squarefree, $(m,N)=1$, $n$ is $Y$-rough, $q,h\in(H/2,H]$, and the original strict middle-count and mark masks hold. The two below-cutoff charges use $0.0153\log\log N$ at exponent $0.9896$ and, on the odd-$m$ sector that remains, $0.0029\log\log N$ at exponent $0.95$. I chose $d>H^{21/20}=N^{21/40}$ inside the published determinant range. An endpoint enters the run only if the product of its three least prime divisors is itself admitted under $\ell<n/H^{21/20}$. The primary view keeps every admitted divisor on those endpoints. The second view keeps only the divisors with at least three prime factors. Both preserve the exact strict inequality. [Published center and complement grouping](https://github.com/Sodelin/Research-Commons/blob/971db7d7f546d4d7fa6865089287f7f97ca085eb/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#exact-center-after-both-rough-factor-charges)

The third view keeps the lower-bound proof's separated $q,h$ intervals, least prime on the smaller cofactor, zero marks, $N^{1/4}<\ell\le N^{1/3}$, at least three prime factors of $\ell$, and the small-factor lower count on $d$. It omits the proof's narrow typical-count bands. For the finite targets, the stronger cutoff $\exp(L^{0.9896})$ is above $H$, so the high intermediate count is zero. A typical-count band with fixed tolerance below its mean coefficient $0.0008$ requires a positive count and is empty. The third view is therefore a geometry projection of the proof subblock. [Central mass proof and its typical-count conditions](https://github.com/Sodelin/Research-Commons/blob/46e4c9cffc482729f93f3d810e4db10134229fe0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-joint-bands-central-mass-2152z.md#actual-mass-in-the-uncharged-triple-complement-center)

## Running balance

For $q<h$, put $c(q,h)=\log h+\mu(m)\log q>0$ and $b(\ell)=-\mu(\ell)\log\ell$. The exact paired weight is $\mu(n)\mu(h)c(q,h)b(\ell)$. Write $B(n)=\sum_\ell b(\ell)$, $C_m=\sum_{qh=m,\ q<h}c(q,h)$, and $A_m=\sum_{qh=m,\ q<h}\mu(h)c(q,h)$, with the retained placements and divisors in each view. The successive masses are

$$
 M_0=\sum_m C_m\sum_\ell |b(\ell)|,\qquad
 M_1=\sum_m C_m|B(n)|,\qquad
 M_2=\sum_m |A_m B(n)|,\qquad
 T=\sum_m\mu(n)A_mB(n).
$$

$M_0-M_1$ is cancellation among divisor complements for one paired placement. $M_1-M_2$ is the additional cancellation across different factorizations of the same product. $M_2-|T|$ is cancellation across distinct additive complements $n=N-m$. I accumulated the signed balance in increasing $n$ and retained the minimum and maximum over all prefixes. The data also include the alternative grouping by $\ell$ across products.

| Even target $N$ | Triple-admitting products | Within fixed $m$ | Across $n$, as a share of $M_2$ | Signed $T/N$ |
| --- | ---: | ---: | ---: | ---: |
| $2^{20}$ | 186 | 90.71% | 51.39% | −0.00162491 |
| $2^{22}$ | 1,392 | 91.16% | 99.68% | +0.00002389 |
| $2^{24}$ | 8,349 | 91.36% | 90.58% | −0.00128952 |
| $3\cdot2^{24}$ | 5,968 | 88.30% | 88.86% | −0.00058686 |
| $2^{26}$ | 44,849 | 91.55% | 99.82% | −0.00003890 |
| $3\cdot2^{26}$ | 35,894 | 88.97% | 97.85% | +0.00017392 |
| $2^{28}$ | 221,861 | 91.75% | 97.65% | +0.00069024 |

All columns in the next table are divided by $N=2^{28}$. The peak is the maximum absolute value of the running balance in the increasing-$n$ order.

| View | $M_0/N$ | $M_1/N$ | $M_2/N$ | $T/N$ | Peak / $N$ |
| --- | ---: | ---: | ---: | ---: | ---: |
| Exact triple center, all admitted divisors | 0.35541393 | 0.02954195 | 0.02931513 | +0.00069024 | 0.00110345 |
| Same center, triple-and-higher terms only | 0.08871072 | 0.08406547 | 0.08362747 | +0.00000407 | 0.00023454 |
| Geometry projection | 0.00002919 | 0.00002919 | 0.00002919 | −0.00002308 | 0.00002308 |

In the full view almost all local cancellation in this example occurs in $M_0-M_1$. The factorizations of the same product account for another $0.00022681N$. Only about 8.05% of $M_0$ cancels across distinct $n$, even though this is 97.65% of what survives the product grouping. On $\mu(n)=+1$ the local drop at this target is 97.36%, and the signed balance ends at $-0.00025220N$. The JSON includes the odd-$m$ and even-endpoint subtotals separately.

To isolate cancellation between orders, write $B=B_{\le2}+B_{\ge3}$, with the subscripts counting prime factors of $\ell$. The amount of triple-and-higher subtotal mass canceled by the lower orders at the same $m$ is

$$
 \frac12\sum_m |A_m|
       \left(|B_{\le2}(n)|+|B_{\ge3}(n)|-|B(n)|\right).
$$

The summand is the smaller magnitude when the signs are opposite and is zero otherwise. Dividing by $\sum_m|A_m B_{\ge3}(n)|$ gives the 92.06% to 98.08% range above. It is 92.06% at $2^{28}$ in the whole center and 97.06% on $\mu(n)=+1$.

The geometry projection was populated at $2^{26}$ and $2^{28}$, with 14 and 107 products, respectively. In both runs the measured within-product drop is zero. Every retained $\ell$ in those runs has exactly three factors because the upper bounds on $\ell$ are 406 and 645, below the least product of four distinct odd primes. Across products the drops in these two small samples are 99.62% and 20.94%, respectively. For another order check, the $\ell$-first absolute mass across products at $2^{28}$ is $0.01300042N$ for the whole center and $0.00333031N$ for the triple-only view. Both grouping orders give the same signed endpoint.

## A complete-divisor filter

There is a hand reason for part of the local drop. For each $n$ put $X=n/H^{21/20}$ and $u=\prod_{p\mid n,\ p<X}p$. If $u<X$, the admitted divisors are exactly the divisors of $u$. The triple condition gives at least three prime factors of $u$, so $\sum_{\ell\mid u}-\mu(\ell)\log\ell=0$. In the exact-center run at $2^{28}$ these complete groups carry 36.19% of the starting mass, and exact-zero brackets of all kinds carry 36.90%. The test for zero is exact because the bracket is represented by integer coefficients of $\log p$ for distinct primes $p$.

In particular every triple-admitting endpoint with exactly four prime factors contributes zero in the all-divisor view. An admitted triple has complementary factor equal to the fourth prime, which exceeds the cutoff $H^{21/20}>H$. That prime exceeds $X$, and all divisors of the triple are admitted. Three-prime endpoints have no admitted triple under the strict cutoff. On $\mu(n)=+1$ the first potentially nonzero endpoints have at least six prime factors. This rule applies for any allowed exponent $a>1$ in the strict cutoff $d>H^a$.

The finite evidence supports grouping the lower-order divisors with the triples at each product and removing complete groups exactly. The next signed estimate is on the incomplete brackets over distinct $n$. The measured final signs vary with $N$. The asymptotic lower-bound subblock's narrow typical-count bands are empty at these targets.

## Reproduction

Run `python3 run-triple-balance.py --output goldbach-triple-balance-results.json` with Python 3 and a C++20 compiler. It builds [the sieve enumerator](goldbach-triple-balance.cpp), runs the seven declared targets, and writes the [masses, prefix extrema and sampled prefixes](goldbach-triple-balance-results.json). The exponent $21/40$ and the square, fourth and cube root bounds are implemented by integer inequalities. The remaining cutoffs agreed at 80 and 120 decimal digits. The full center at $2^{20}$ was independently checked by trial division and the two original, unswapped weights. The geometry projection at $2^{28}$ was independently checked by enumerating $\ell$ first and using its congruence for $h$. Both checks matched the counts and the four mass/signed-sum stages. The numerical data and exact divisor identity are separate from an asymptotic estimate of the signed remainder.
