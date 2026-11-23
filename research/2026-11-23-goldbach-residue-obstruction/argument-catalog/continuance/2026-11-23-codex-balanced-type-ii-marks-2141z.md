# Cutoff losses and mark coverage in one balanced Goldbach Type II box

23 November 2026. Unconditional hand bounds at one fixed even target for the balanced Type II box. They allow any vanishing log-ratio tolerance for numerical cutoff losses in this box and bound the coverage of exchanges of fixed-length small bundles. [Exact Type II reduction and marked allocations](https://github.com/Sodelin/Research-Commons/blob/a4d4faa26b1828d0f2cd1dfd7edb37d7b4645bbe/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md) · [Peer base and prime-power removals](https://github.com/Sodelin/Research-Commons/blob/581f30cc217415f438594c02cfc4f894837fe981/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-small-prime-base.md)

## Exact box and bounds

Write $L=\log N$, $H=\sqrt N$ and keep $q,h\in I=(H/2,H]$ ordered, $m=qh$ squarefree with $(m,N)=1$, and the exact retained count and allocation masks. Keep the original strict cutoff $uv>D_0$ and any previous endpoint trim. In the equation $qh+\ell uv=N$, keep the actual prime $\ell\in(N^{1/10},N^{1/8}]$ in one fixed dyadic band $\ell\asymp N^{1/8}$ and use one dyadic box $u,v\asymp N^{7/16}$. Keep the Vaughan lower cutoffs and the remaining $w$ terms of $B_V(v)$ after the previous base and proper-power charges. One can also use the $\ell$-dependent Vaughan cutoffs on this support. The coefficient that remains at a tuple is a sub-sum of $\sum_{w\mid v}\Lambda(w)=\log v$. In particular the sum of absolute weights over all admitted $w$ at fixed $q,h,\ell,u,v$ is at most $C\log\ell$, since $|\log(h/q)|\le\log 2$ and $\log v\le\log(uv)$. The proof preserves these tuples and weights and uses this positive upper bound for the indicated slices.

* The whole box has absolute weight $O(N)$. If two chosen shifts each have magnitude at most $\eta\le 1$, the absolute Type II weight of placements whose marks fail a numerical $q,h$ cutoff is $O(\eta N+N^{27/32+o(1)})$. This gives $o(N)$ for every $\eta=o(1)$, also for an allocation-dependent subset of the edge strips.
* Fix a positive integer $k$ and $0<\xi<5/64$. The absolute weight of placements admitting even one parity-changing exchange with bundle products $a,b\le N^\xi$, each with at most $k$ prime factors, and $|\log(a/b)|\le\eta$ is

  $$
  \ll_k N\frac{(1+\log T_\eta)^{2k-2}}{T_\eta}+N^{27/32+2\xi+o(1)},
  \qquad T_\eta=1+\log(1/\eta),\quad 0<\eta\le1/2.
  $$

  This is $o(N)$ for every $\eta=o(1)$. In particular it covers one-for-two swaps whose primes all lie below the original intermediate upper threshold $\exp(L^{.99})$. Fixed-length bundles of those primes have subpolynomial products.
* With arbitrary bundle lengths and products, the absolute weight on placements admitting two disjoint parity-changing exchanges both of log ratio at most $\eta$ is $O(N\eta L^6)$. At the previously certified inverse-log tolerance $\eta\le L^{-17-2A}$ the marked support itself has negligible weight.
* For squarefree $u$ with $\omega(u)\le\alpha\log L$, $0<\alpha<1$ fixed, the full absolute weight in this dyadic box is $O_\alpha(N(1+\log L)L^{\alpha(1-\log\alpha)-1}+N^{27/32+o(1)})=o(N)$. The estimate includes every remaining $w\mid v$ with its original weights.

## Count at fixed complementary modulus

Fix an allowed $\ell,v$ and put $M=\ell v$. The integer $u=(N-qh)/M$ is determined by $q,h$. One can discard the other restrictions for an upper count of these tuples. The original coprimality implies $(M,N)=1$, so the congruence $qh=N\bmod M$ is a unit hyperbola. For fixed divisibility constraints $a\mid q,b\mid h$, there are no solutions if $(ab,M)>1$. Otherwise write $q=ax,h=by$ and complete the congruence $xy=N\overline{ab}\bmod M$ in the two scaled intervals. For any intervals $J_q,J_h\subset I$ the resulting count is

$$
\frac{\varphi(M)}{M^2}\frac{|J_q||J_h|}{ab}
 +O\big(M^{1/2+o(1)}(1+H/M)\big),
$$

uniformly in the interval widths and in $a,b$. To check the error, for a nonzero interval frequency $j$ the geometric-series bound is $O(M/\min(j,M-j))$, with $1\le j<M$. Grouping multiples of divisors of $M$ gives weighted Fourier coefficient sum $O(M\log(2M)\tau(M))$ with weight $(j,M)^{1/2}$. Apply this in either nonzero coordinate to the Weil bound for the complete Kloosterman sum, whose gcd factor is $(j_1,j_2,M)^{1/2}$. In a mixed term the zero coefficient has size at most $H+1$. The difference between integer and real interval lengths in the zero term is smaller. This is the same completion as in the fixed-index CRT count. [Pinned completion calculation](https://github.com/Sodelin/Research-Commons/blob/6c808c9a13b93fd394ddd7888aa8f45e36a55c46/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-count-transfer-2107z.md#extension-to-the-whole-region-with-no-triple-complement)

Over one dyadic $\ell$ interval, Chebyshev gives $\sum_{\ell\text{ prime}}\log\ell/\ell\ll1$. Over one dyadic $v$ interval, $\sum1/v\ll1$. Thus, after restoring the upper weight $C\log\ell$, the main term for $J_q,J_h,a,b$ is at most $C|J_q||J_h|/(ab)$. There are $O(N^{9/16})$ pairs $\ell,v$ and $M\asymp N^{9/16}$, so the total error for that rectangle and divisibility pair is $N^{27/32+o(1)}$. In particular the unmarked $I^2$ rectangle costs $O(N)$.

For the cutoff statement, an unsuccessful shift of magnitude at most $2\eta$ puts $q$ or $h$ within $O(\eta H)$ of an edge, by the exact extreme-shift test. The union of those edge strips is a union of at most four rectangles. With $a=b=1$ their areas are $O(\eta N)$ and the completion error just derived remains uniform. This proves the absolute bound even when the failed placements are selected by the other arithmetic masks. The older moment argument needed $\eta$ to be a sufficiently small inverse power of $L$ on the unrestricted semiprime band. The improved tolerance here uses one fixed $\ell,v$ box.

## Coverage by fixed-length small bundles

For a marked pair $a\mid q,b\mid h$ to change the sign, require $\mu(a)\mu(b)=-1$. Then $a\ne b$. Since $|\log(a/b)|\le\eta\le1/2$, the integer difference is nonzero and at most $2\eta\min(a,b)$, so $\min(a,b)\ge(2\eta)^{-1}$. Each bundle is squarefree because it divides a squarefree cofactor. For $X\ge2$ the elementary harmonic bound is

$$
\sum_{X<t\le 2X,\,\omega(t)\le k,\,t\text{ squarefree}}\frac1t
 \ll_k \frac{(1+\log\log(3X))^{k-1}}{\log(2X)}.
$$

Indeed write $t=pr$ with $p$ its largest prime, then $p\ge X^{1/k}$ and $r$ has at most $k-1$ primes. For each $r$ the prime count is $O_k(X/(r\log(2X)))$ by Chebyshev. Sum $1/r$ by Mertens and the bound on its number of factors, then divide by $X$. Since $a,b$ are in the same or neighboring dyadic shells, their harmonic product for shells at $2^j$ is $O_k((1+\log(2+j))^{2k-2}/(1+j)^2)$. Summing this convergent tail from $j\gg\log(1/\eta)$ gives

$$
\sum_{\substack{a,b\text{ marked-size and factor-count eligible}\\a\ne b,\,|\log(a/b)|\le\eta}}\frac1{ab}
 \ll_k \frac{(1+\log T_\eta)^{2k-2}}{T_\eta}.
$$

Apply the fixed-$M$ count with $a\mid q,b\mid h$ and sum over all the allowed marks. This upper bounds the union of placements, regardless of their mark-choice rule. There are at most $N^{2\xi}$ choices of $a,b$, so the total error is $N^{27/32+2\xi+o(1)}$, a power saving for $\xi<5/64$. The main term is $N$ times the displayed harmonic tail. The orientation $a$ on $h$ instead of $q$ is already included by interchanging the ordered values. This proves the second bound.

## Coverage at the older close-ratio tolerance

Without a length cap, for each integer $a\le H$ there are $O(\eta a)$ possible distinct integers $b$ with the log-ratio condition. The integer count excludes $b=a$, so there is no additive 1. Each such $b$ is comparable to $a$. Thus the total reciprocal weight of possible pairs is $O(\eta L)$. For two disjoint pairs on opposite cofactors, the products $a_1a_2\mid q,b_1b_2\mid h$ divide their respective factors. The number of ordered $q,h$ with two pairs is at most $O(N(\eta L)^2)$, by counting multiples of those products and then enlarging the reciprocal sum to two independent pairs.

For any fixed $q,h$, given $n=N-qh$, the sum of the absolute Type II weights is $O(L\tau(n))$: there are at most nine eligible prime choices of $\ell\mid n$, and at most $\tau(n)$ choices of $u$, each with the bound $C\log\ell$ above. Also

$$
\sum_{q,h\in I,\,qh<N}\tau(N-qh)^2
 \le \sum_{m<N}\tau(m)\tau(N-m)^2\ll NL^8
$$

by Cauchy–Schwarz and the second and fourth divisor moments. Cauchy–Schwarz on the marked $q,h$ pairs now gives $O(N\eta L^6)$, as claimed. This last argument also works without the restrictions to the single balanced box.

## A low factor count on the entire dyadic $u$ interval

One can instead fix the actual prime $\ell$ and the integer $u$, so $M=\ell u$ and $v=(N-qh)/M$ is determined. The same bound $C\log\ell$ holds for the absolute weight restored at each such solution. Thus for a set $\mathcal U$ of values of $u$ in the chosen dyadic interval the bound is $O(N\sum_{u\in\mathcal U}1/u+N^{27/32+o(1)})$. This uses the single prime $\ell$ interval and the full available $v$ range inside the box. The arithmetic restrictions and all $w$ weights can be retained.

Let $\mathcal U$ have $\omega(u)\le\alpha\log L$ with $\mu(u)\ne0$. The largest prime $p$ of $u\asymp N^{7/16}$ is at least $\exp(c_\alpha L/\log L)$. For fixed $r=u/p$, $p$ is in an interval of ratio 2. Its reciprocal prime sum is $O_\alpha((1+\log L)/L)$ by Chebyshev, using the polynomial scale of $u$ before dividing by its number of factors. The unmarked reciprocal sum over $r$ is bounded by $\sum_{j\le\alpha\log L}(\log L+O(1))^j/j!\ll_\alpha L^{\alpha(1-\log\alpha)}$ by the factorial bound and $\alpha<1$. Combining the two proves the low-count bound. The same argument for a fixed $k$ gives $O_k(N(1+\log L)^{k-1}/L+N^{27/32+o(1)})$. This is a charge on the entire dyadic $u,v$ box, including the terms where the opened prime $w$ is smaller than $u$. The peer's composite-modulus sieve on its $u\asymp w$ support may be charged on the complement wherever it applies. [Peer sieve and low-factor calculation on its own support](https://github.com/Sodelin/Research-Commons/blob/909738e51f1ea4abe94c119276375481f85abc56/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-balanced-two-prime-sieve.md)

## Use in the signed ledger

Work on the remaining opened Type II support after the previous base charge, or use the equivalent variable Vaughan cutoffs. Charge the low factor count of $u$ first. These tests are fixed under the allocation swaps. The proof then bounds numerical edge losses for any two already compatible near-equal marks in the balanced box. The known exact four-allocation orbit cancels with the same coefficients and signs. Placements admitting a close exchange with both products at most $N^\xi$ and at most $k$ factors per product carry $o(N)$ absolute weight. At the older inverse-log tolerance even arbitrary-length pairs have negligible coverage by the third bound. The remaining signed sum still needs a fixed-target lower bound. A concrete next marked subproblem is coverage by pairs with larger products or a growing number of factors at $\eta=(\log L)^{-1}$. [Dot's strict-box follow-up in the pinned proof](https://github.com/Sodelin/Research-Commons/blob/a4d4faa26b1828d0f2cd1dfd7edb37d7b4645bbe/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md#box-cutoff-losses-for-two-near-equal-marked-swaps)
