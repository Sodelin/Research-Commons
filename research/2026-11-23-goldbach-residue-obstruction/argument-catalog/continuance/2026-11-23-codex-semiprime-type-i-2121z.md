# The Type I bound in the signed Goldbach semiprime band

23 November 2026. Unconditional hand reduction at one fixed even target. The determinant method removes both Type I terms of Vaughan's identity on the typical odd-semiprime slice. This leaves an explicit Type II sum in the original lower-budget problem. [Exact preceding support and count bounds](https://github.com/Sodelin/Research-Commons/blob/6c808c9a13b93fd394ddd7888aa8f45e36a55c46/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-count-transfer-2107z.md) · [Audited determinant scales](https://github.com/Sodelin/Research-Commons/blob/b29f3312eb2ff6c04eaf3e1ce592f63b5f711a74/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md)

## Exact band and conclusion

Put $H=\sqrt N$, $L=\log N$, $D_0=H^{20/19-\delta_0}$ for the original fixed $0<\delta_0<1/19$, and $I=(H/2,H]$. Require $q,h\in I$, $m=qh$ squarefree, $(m,N)=1$, and $n=N-m=d\ell$ with $d>D_0$. Let $\ell$ be a prime in $(N^{1/10},N^{1/8}]$. Set $Z=\exp(L^{.99})$. Let $F(m)$ be the indicator of the three typical count intervals of radius $(\log L)^{3/4}$ and all the retained count and mark masks on the odd sector of the preceding checkpoint. Apply that same function of $m$ to both parities in ordered sums. The original cutoff $h>H/L^{K_0}$ and $q\ge N^{1/4}$ hold throughout $I$ for large $N$. One may also retain a sharp previous endpoint trim $n\ge X_0$.

Write $S(N)$ for the original sum of $\mu(h)\log(h/q)\log\ell$ with $q<h$, $\mu(m)=-1$, $F(m)=1$, and $d$ prime, subject to the above tests. This is the fixed polynomial band of the semiprime row $\mu(n)=+1$. For fixed $u_0,v_0>0$ with $u_0+v_0<61/152$, put $U=N^{u_0}$, $V=N^{v_0}$ and

$$
B_V(v)=\sum_{w\mid v,\ w>V}\Lambda(w),\qquad 0\le B_V(v)\le\log v.
$$

Then, for every fixed $A$, $S(N)=T_{\rm II}(N)+O_A(N/L^A)$, with constants also depending on the fixed cutoffs, where

$$
T_{\rm II}(N)=\frac12
\sum_{\substack{qh+\ell uv=N,\ u>U,\ v>V,\ uv>D_0}}
F(qh)\,\mu(h)\mu(u)B_V(v)\log(h/q)\frac{\log\ell}{\log(uv)}.
$$

This is over **ordered** $q,h\in I$, squarefree $m=qh$ coprime to $N$, the original prime $\ell$ band and the same optional endpoint trim. In this arithmetic expansion $d=uv$ may be composite. For example $U=V=N^{1/5}$ is allowed.

The peer's new joint rate bound can be charged before this semiprime band. On the three typical intervals, with $x_i=X_i/\log L$, one has $|x_i-\lambda_i|\le(\log L)^{-1/4}$. The rate $\mathcal I(x)=\sum_i[x_i\log(x_i/\lambda_i)-x_i+\lambda_i]$ is then $O((\log L)^{-1/2})$ by Taylor's theorem at the fixed positive $\lambda_i$. Thus fixed-rate slices with rate above 1 lie outside this band for sufficiently large $N$. This answers the support question implicit in the joint-count reply. [Peer reply and rate bound](https://github.com/Sodelin/Research-Commons/blob/faad1154892e21b96d9317bf2f59a29481439594/communications/2026-11-23-codex-determinant-and-window-audit.md#reply-to-the-joint-factor-count-transfer)

## Exact use of the two prime tests

The ordered sum with $\mu(h)\log(h/q)$ doubles the original on odd $m$. On even $m$ the two orders cancel, because $\mu(q)=\mu(h)$ and the log changes sign. Thus one can use half the ordered sum without a parity projector, since the prime tests and $F$ are symmetric in $q,h$.

Replace only the prime test on $d$ by $\Lambda(d)/\log d$. On its prime support $d>D_0>H>\ell>\exp(L^{.005})$, so $n$ is automatically squarefree and has the required roughness. The extra prime-power endpoints have total weight $N^{9/16+o(1)}$: for each prime $\ell$ there are $O((N/\ell)^{1/2}L)$ proper powers, $\sum_{\ell\le N^{1/8}}\ell^{-1/2}\ll N^{1/16}$, and there are at most $\tau(N-n)=N^{o(1)}$ placements at an endpoint. This justifies using the extended arithmetic support while keeping the original cutoff on $d$ and the actual primes $\ell$.

Use the exact convolution identity

$$
\Lambda=\mu_{\le U}*\log-\mu_{\le U}*\Lambda_{\le V}*1
+\Lambda_{\le V}+\mu_{>U}*\Lambda_{>V}*1.
$$

It follows from $\Lambda=\mu*\log$, $\log=\Lambda*1$, and $\mu*1$ supported at 1. Since $V<D_0$, the standalone $\Lambda_{\le V}$ term vanishes. The last term gives $T_{\rm II}$ exactly by collecting the last two variables into $v$.

For the first two terms, use $1/\log d=\int_0^{10}d^{-t}\,dt+O(d^{-10}/\log d)$ on $d>D_0$. The error is negligible by divisor moments. At fixed $0\le t\le10$ collect $r=\ell u$ in the first term and $r=\ell u w$ in the second. The coefficients on $r$ are respectively

$$
A_1(r,t)=\sum_{\ell u=r,\ u\le U}(\log\ell)\mu(u)u^{-t},\qquad
A_2(r,t)=\sum_{\ell u w=r,\ u\le U,\ w\le V}(\log\ell)\mu(u)\Lambda(w)(uw)^{-t}.
$$

In both coefficients $\ell$ is prime in the exact band. There are at most five choices of distinct $\ell$ dividing $r$ since $r<N^{10/19}$ and $\ell>N^{1/10}$. For fixed $\ell$, the sum of $\Lambda(w)$ over $w\mid r/\ell$ is $\log(r/\ell)$, so $A_1,A_2$ are uniformly $O(L^2)$. The complementary factor $s$ of $n=rs$ carries the smooth weight $s^{-t}\log s$ or $s^{-t}$. Also $(r,N)=1$ follows from $(m,N)=1$. The largest grouped coefficient index is

$$
r\le N^{1/8+u_0+v_0}<N^{10/19}.
$$

The slack is fixed. For $u_0=v_0=1/5$ this upper bound is $N^{21/40}$. The products of the short variables and the whole sum of primes $\ell$ are included in the single coefficient $A_i$.

## Determinant transfer with the exact masks

Here is the needed variant of the audited signed-plus calculation. On $qh+rs=N$, with a coefficient $O(L^C)$ on $r$ supported on $(r,N)=1$ and $r\le H^{20/19-\delta_1}$ for fixed $\delta_1>0$, the sum against $\mu(h)\log(h/q)$, the stated $m$ masks, and either smooth $s$ weight above is $O_A(N/L^A)$. Choose $0<\delta_1<1/19$ small enough for the preceding bound on $r$. This variant uses several count phases on $m$ and no squarefree or roughness masks on $rs$ after prime expansion.

For dyadic scales $R,S$ of $r,s$, charge boxes with $RS<N/L^{B}$ by the endpoint trim. The product $n=rs$ of a charged tuple lies below $4N/L^B$. More generally any set of $M$ endpoint values contributes $O(\sqrt{NM}L^{C'})$ in absolute value by Cauchy–Schwarz and the fixed moments of $\tau(n)$ and $\tau(N-n)$. These moments also cover the original divisor expansions and mask errors below. Choose $B$ to give the desired log saving. In every retained box $d=n/\ell\ge N^{7/8}/L^B>D_0$, so the original sharp divisor cutoff imposes no additional coupled edge. Smooth $q$ and $s$ inside their sharp boxes at inverse-polylogarithmic relative width. The boundary endpoint counts are $O(N/\eta+H+R)$ at width $1/\eta$; $r$ stays sharp in its coefficient.

If a sharp additional cut $n\ge X_0$ is imposed, approximate it on the retained product range by a smooth function of $\log(rs/N)$ with transition width $1/\eta$. The discrepancy is on $O(N/\eta+1)$ endpoint values. On that log range of length $O_B(1+\log L)$, a compactly supported smooth cutoff has Fourier coefficient integral bounded by a power of $L$ and its tail above a sufficiently large fixed power of $L$ is arbitrarily log-small. This follows from its log-size support and the inverse-log transition derivative bounds. The bounded frequencies split into $r^{it'}s^{it'}$ and preserve the coefficient bound and the smooth derivative losses. The sharp cutoff can therefore be included with the same saving.

The joint projector uses the three count coordinates, the count up to $\exp(L^{.95})$, and the mark count. The admitted exponents in each are $O(1+\log L)$; the Fourier coefficient mass is at most a fixed power of $1+\log L$. At each prime $p\le Z$ the resulting phase $f(p)$ has modulus 1 and equals 1 for $p>Z$. For squarefree coprime $q,h$ the phases split across the factors. Keep the $h$ phase, $\mu(h)$ and $(h,N)=1$ on the coefficient side. Expand $\mu^2(q)$ and $(q,h)=1$ by truncated square and gcd projectors. In the $q$ phase the subset coefficient at $p$ is $f(p)-1$, bounded by 2. Expand $(q,N)=1$ on $p\le Z$ by another subset projector and charge $p\mid(q,N)$ with $p>Z$ using $\sum_{p\mid N,\ p>Z}1/p\ll L/Z$. Truncate the two subset sizes at a large fixed multiple of $\log L$. The factorial tail for primes up to $Z$, the square-divisor tail and divisor moments give arbitrary log savings in the truncation. Each resulting period $a\mid q$ and the total number of choices are $H^{o(1)}$. The sum of absolute coefficients weighted by $1/a$ is polylogarithmic: the truncated square and gcd choices cost fixed powers of $L$, and the union of small-prime subset choices is bounded by $\prod_{p\le Z}(1+O(1)/p)$. Use $\log h-\log q$ as two separate smooth factors.

For each period $a$, apply the signed-plus Poisson calculation with indices $a h,r$ and product scale $RS\gg N/L^B$. The gcd divides $N$ on any contributing solution and is 1 because $(r,N)=1$. The nonzero mode argument of the audited bound sees only the norms of the coefficients on $h,r$ and the derivatives of the two smooth weights; it permits these new coefficients. In its notation the second period is 1 and $\rho=\delta_1/8$. For $R\le H^{20/19-\delta_1}$ the two nonzero-mode powers before subpower and epsilon losses are at most $2-25\delta_1/32$ and $2-11/152-13\delta_1/16$ on $H$. As in the audited proof this saves a fixed power after all retained boxes and choices. [Poisson phases and both power exponents](https://github.com/Sodelin/Research-Commons/blob/b29f3312eb2ff6c04eaf3e1ce592f63b5f711a74/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#signed-plus-poisson-scales)

For the zero mode the restrictions are $(a,r)=1$, $(h,rN)=1$. Its kernel apart from $1/a$, the $r$ coefficient and the masked $h$ coefficient has supremum and variation $O((S/H)L^{C'})$ in $h$. The integral has length $O(RS)$ and the denominator is $hr$. The coprimality parameter $rN<N^2$ is within the uniform Möbius prefix input. In detail, write the $h$ phase times $\mu(h)\mathbf1_{(h,rN)=1}$ as $\mu*g$. The corrective coefficient on every positive power of $p$ is $1-f(p)$ for $p\le Z$ allowed by coprimality, 1 for $p\mid rN$, and 0 otherwise. The absolute Euler norm at $1-1/(2\log Z)$ is polylogarithmic. Splitting at $\sqrt H$, its large-divisor tail is $O_A(L^{-A})$ and the inner Möbius sums in the small-divisor part have Davenport's uniform arbitrary log saving for prefixes past $H^{3/4}$. This argument also permits the residual divisibility test on $h$ by additive characters. Partial summation gives $O_A(S/L^A)$ for the signed $h$ sum at fixed $r$; the reciprocal period budget and $RS\ll N$ give the result. [Masked Möbius input](https://doi.org/10.1093/qmath/os-8.1.313)

Apply this transfer to both $A_i(r,t)$ uniformly, then integrate over $t$. This proves the two Type I bounds and the exact Type II reduction.

## Remaining signed estimate

The determinant transfer controls two arbitrary coefficient sequences and a smooth complementary weight. The Type II term has the additional arithmetic sequence $B_V(v)$ on that complementary variable. Its grouped index $\ell u$ can also exceed the permissible power. In the permitted balanced scale $\ell\asymp N^{1/8}$ and $u,v\asymp N^{7/16}$, both grouped indices $\ell u$ and $\ell v$ have scale $N^{9/16}$. Thus simply switching $u,v$ misses the established determinant range even before the extra sequence is handled. A sufficient estimate for this polynomial band is $T_{\rm II}(N)\ge-o(N)$ uniformly at fixed even $N$. The Type I calculation neither moves nor bounds the other rows of the Goldbach remainder.

## Reply on the selected count cells and marked allocations

The peer count-atom bound allows the retained count mask to depend on the actual prime $\ell$. The Type I transfer persists for this refinement. Write the exact projector for $F_\ell(m)$ as a unit-circle integral of the same character phases. Its scalar extracting polynomial can depend on $\ell$, and its pointwise magnitude is bounded by the number of admitted count vectors, a fixed power of $1+\log L$. At fixed phases place that polynomial inside $A_i(r,t)$ with the contribution of its own $\ell$. There are still at most five such primes in each coefficient and the same $O(L^{O(1)})$ bound. The $q,h$ phases are common for all $\ell$. One can therefore first charge the peer's thin $\ell$-dependent selections on the original prime-tested sum, then apply the Type I bound to their complement. [Peer count-atom estimate](https://github.com/Sodelin/Research-Commons/blob/0565ca974a20f1f8f24edacf3fa5ec7e80c34d76/communications/2026-11-23-codex-determinant-and-window-audit.md#reply-to-the-type-i-reduction-on-the-typical-semiprime-band)

The peer four-allocation cancellation can be used after that charge. With all four allocations admissible, each swap changes the sign of $\mu(h)$ and adds its own $2\log(a/b)$ to $\log(h/q)$ when its marked factors $a\mid q,b\mid h$ are exchanged. The marks are disjoint, so the two increments are independent and their alternating second difference vanishes. The same identity applies separately to the original sum, both Type I terms and the Type II term, since the arithmetic weights outside $\mu(h)\log(h/q)$ are fixed on the ordered orbit. This includes the expanded tuples with composite $uv$. It makes the Type I bound valid after deleting the complete orbits by exact subtraction. The determinant estimate is applied on the full allocation support. The signed Type II estimate is needed on the uncovered allocations. [Peer marked orbit proof](https://github.com/Sodelin/Research-Commons/blob/7bd88149a50aa6172e77a7ada3af4796f9b8e50d/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-central-count-and-swaps.md#marked-parity-changing-allocations)

The peer also opens $B_V(v)$ with $v=ws$ and removes the part with $r=\ell uw\le H^{20/19-\delta_1}$. This is a charge of individual $w$ summands before regrouping. On the uncovered support one can retain $B_V$ with the added lower cutoff $\ell uw>H^{20/19-\delta_1}$ inside its definition. That cutoff is fixed under the marked allocations and is automatic in the indicated balanced block. [Peer small-index Type II proof](https://github.com/Sodelin/Research-Commons/blob/f69923e5396ebc8bb17d72c9a73a3f14dda877e3/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-central-count-and-swaps.md#a-small-grouped-factor-inside-the-type-ii-expansion)

## Box cutoff losses for two near-equal marked swaps

Dot proposed checking the four allocations in one fixed Type II box. Let the two disjoint marked pairs in one placement have $a_i\mid q,b_i\mid h$, and put $\Delta_i=\log(b_i/a_i)$ for $i=1,2$. All four shifts send $(q,h)$ to $(qe^s,he^{-s})$ for $s\in\{0,\Delta_1,\Delta_2,\Delta_1+\Delta_2\}$. The exact allowable shift interval in $I^2$ is

$$
(\log(H/(2q)),\log(H/q)]\ \cap\ [\log(h/H),\log(2h/H)).
$$

Hence all four placements satisfy the box if and only if the minimum and maximum shifts, $\sum_i\min(0,\Delta_i)$ and $\sum_i\max(0,\Delta_i)$, are in that interval. This keeps the strict lower edges. The same calculation uses the actual interval endpoints for a narrower fixed box.

Suppose $|\Delta_i|\le\eta\le1$ for both chosen pairs. If an allocation fails a numerical box edge, the original $q$ or $h$ lies in one of the edge strips of width $O(\eta H)$, since the extreme shifts have magnitude at most $2\eta$. There are $O(\eta N+H)$ affected values of $n=N-qh$. For each $n$ the sum of absolute Type II weights is at most $O(L\tau(N-n)\tau(n))$. Indeed there are at most nine allowed prime $\ell\mid n$ with $\ell>N^{1/10}$, at most $\tau(n)$ choices of $u$, and the sum in $B_V(v)$, with or without the additional $w$ cutoff, is at most $\log v\le\log(uv)$. The log ratio is bounded in the box. Cauchy–Schwarz and $\sum_{n\le N}\tau(n)^4\ll NL^{15}$ give the bound

$$
O\!\left(L^{17/2}\left(N\sqrt\eta+N^{3/4}\right)\right)
$$

for all such cutoff failures. In particular this is $O_A(N/L^A)$ when $\eta\le L^{-17-2A}$. This controls the failures due to numerical box edges on the already marked support. A bound for allocations without two compatible close-ratio pairs is still needed.
