# Sublinear ratio strips in Goldbach Type II with a polynomial-scale sieve weight

23 November 2026. Unconditional hand proof at one fixed even target. The peer retained the endpoint roughness before Vaughan's expansion and removed logarithmic ratio strips. Here a Selberg square is exactly one on the prime-tested support. It gives two powers of $\log N$ in the absolute Type II count and allows any sublinear log-ratio width on the full prime band. [Peer retained-mask reduction](https://github.com/Sodelin/Research-Commons/blob/3c4778ccc493abb2b5f9610c8fce5ea86fd0737d/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rough-complement.md) · [Peer logarithmic windows](https://github.com/Sodelin/Research-Commons/blob/81656bc6d/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rough-log-boxes.md)

The concurrent peer two-sided fundamental-lemma proof also reaches every sublinear width by choosing the retained roughness scale for that width. The construction here uses one fixed choice of polynomial scales across all widths, retains arbitrary log savings for Type I, and gives the totient factor in the full-band estimate. [Peer two-sided sieve and period bounds](https://github.com/Sodelin/Research-Commons/blob/8964660fb05a3bf80db2793c02708497e7d071c5/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-fundamental-lemma-log-windows.md)

## Exact statement

Let $H=\sqrt N$, $L=\log N$, $m=qh$, $n=N-m$, and keep ordered $q,h\in(H/2,H]$, squarefree $m$ with $(m,N)=1$, and the pinned typical-count and mark projector $F(m)$. Keep the actual prime $N^{1/10}<\ell\le N^{1/8}$, $d=n/\ell>D_0=H^{20/19-\delta_0}$ with $0<\delta_0<1/19$ fixed, and any preceding sharp endpoint cutoff. The prime-tested sum is half the ordered sum of $F(m)\mu(h)\log(h/q)\log\ell$ on prime $d$. Swapping $q,h$ gives the original odd-$m$ weight and cancels the even part. Use Vaughan cutoffs $U=V=N^{1/5}$, so the Type I grouped index is at most $P=H^{21/20}$.

There is a nonnegative weight $W_N(n)$, specified below, with $W_N(\ell d)=1$ for every original pair of primes. Keep $n$ squarefree and $Y_0$-rough, $Y_0=\exp(L^{.005})$, and use $W_N(n)$ through the expansion. Both Type I terms are still $O_A(N/L^A)$ for every fixed $A$. The original prime-tested sum therefore equals the weighted Type II sum up to that error. Its exact terms have equation $qh+\ell uv=N$, $u>U$, $v>V$, $uv>D_0$, and weight

$$
\tfrac12 F(m)W_N(n)\mu(h)\mu(u)B_V(v)\log(h/q)\frac{\log\ell}{\log(uv)},\qquad
B_V(v)=\sum_{w\mid v,\ w>V}\Lambda(w).
$$

Let the prime $\ell$ interval have log width at most $W$. In each cell with fixed $\ell$ and dyadic endpoint band $N2^{-j-1}<n\le N2^{-j}$, impose one interval for $\log(u/v)$ of width at most $\Delta$. The location may depend on $N,\ell,j$. The absolute Type II weight on this support and on any further intersection is

$$
O_A\!\left(\frac{\varphi(N)(1+W)(1+\Delta)}{L^2}+\frac{N}{L^A}\right).
$$

In particular, across the full polynomial prime $\ell$ band, all such strips with $\Delta=o(L)$ contribute $o(N)$. This includes the whole comparable $u,v$ zone across that prime band, whose cost is $O(N/L)$ for fixed ratio width. Taking $\Delta=O(L)$ bounds the whole weighted Type II band by $O_A(\varphi(N)+N/L^A)$. Hence the original signed odd-semiprime contribution on this band is $o(N)$ along every sequence of even targets with $\varphi(N)/N\to0$. These are charges in the equivalent expansion with $W_N(n)$.

## The weight and its elementary quadratic identity

Take fixed small constants $\kappa,\delta>0$ in the order described below. Put $D=N^\kappa$, $z=N^\delta$ with $\delta<1/10$. For each prime $p\le z$, let

$$
g_p=\begin{cases}(p-1)/p^2 & p\nmid N,\\ (2p-1)/p^2 & p\mid N,\end{cases}
\qquad g_{2,p}=g_p+(1-g_p)/p.
$$

Extend $g_2$ multiplicatively to squarefree integers supported on those primes and put $h(a)=\prod_{p\mid a}g_{2,p}/(1-g_{2,p})$ on that support. The squarefree sieve indices are $a\le D$. Write $G_D=\sum_{a\le D}h(a)$ over those indices. There are real weights $\lambda_a$ supported on these indices with $\lambda_1=1$, $|\lambda_a|\le1$, and

$$
Q(\lambda)=\sum_{a,b}\lambda_a\lambda_b\,g_2([a,b])=1/G_D.
$$

For verification set $y_c=\sum_{c\mid a}\lambda_a g_2(a)$. The identity $1/g_2((a,b))=\sum_{c\mid(a,b)}1/h(c)$ gives $Q=\sum_c y_c^2/h(c)$, where $h(1)=1$. Choose $y_c=\mu(c)h(c)/G_D$. Möbius inversion gives $\lambda_1=1$ and

$$
|\lambda_a|=\frac{\prod_{p\mid a}(1+h(p))}{G_D}
      \sum_{r\le D/a,\ (r,a)=1}h(r)\le1.
$$

The last sum keeps the same prime and squarefree support. For its upper bound in the ratio, each $r$ can be multiplied by every divisor of $a$ and remain in the denominator's sum, with all these products distinct. In the full squarefree Euler product $\prod_{p\le z}(1+h(p))$, the normalized probability of a prime being present is $g_{2,p}$. Its expected log product is $\sum_{p\le z}g_{2,p}\log p\ll\log z$, since $g_{2,p}\le3/p$. Choose $\delta$ sufficiently small in terms of $\kappa$, so that by Markov at least half of the mass has product at most $D$. The local survival factor $1-g_{2,p}$ is $(1-1/p)^3$ at $p\mid N$ and $(1-1/p)^2(1+1/(p(p-1)))$ at the other primes. By Mertens and the bounded product over the primes of $N$ above $z$, this gives $1/G_D\ll_\delta\varphi(N)/(N L^2)$.

Set $W_N(n)=(\sum_{a\mid n}\lambda_a)^2$. On the original prime-tested support $\ell,d$ are both above $z$, so $W_N(n)=1$. Also $0\le W_N(n)\le\tau(n)^2$. Squarefreeness and the older roughness masks are retained when making the exact replacement of the prime test on $d$ by $\Lambda(d)/\log d$, since squarefreeness of $n$ excludes proper prime powers $d$. These masks already hold on the original prime support.

## Type I with the polynomial periods

Use the pinned Vaughan grouping $n=rs$ for either Type I term. The index $r$ is bounded by $\ell UV\le P$, the grouped coefficient is $O(L^2)$, and $s$ carries the smooth weight after integrating $d^{-t}$ for $0\le t\le10$. These steps also allow the $\ell$-dependent count selectors of the original proof. Retaining $W_N(n)$ is legitimate during the endpoint and smoothing trims: the extra weight is bounded by $\tau(n)^2$, so the fixed divisor moments still give arbitrary log savings. One may drop squarefreeness in Type I at this stage, keeping exact $Y_0$-roughness. The omitted endpoints then have a square factor $p^2$ with $p>Y_0$, and their number is $O(N/Y_0)$. Restore the exact masks in the expression for Type II. [Pinned Type I grouping and sharp cuts](https://github.com/Sodelin/Research-Commons/blob/a4d4faa26b1828d0f2cd1dfd7edb37d7b4645bbe/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md#determinant-transfer-with-the-exact-masks)

Open $W_N(rs)$ into the $a,b$ sum. For $c=[a,b]$, which is squarefree, use the exact split

$$
\mathbf1_{c\mid rs}
=\sum_{c_1 c_2=c}\mathbf1_{c_1\mid r}\mathbf1_{(c_2,r)=1}\mathbf1_{c_2\mid s}.
$$

Indeed $c_1=(c,r)$ is forced. This is valid also after dropping squarefreeness of $rs$ in Type I. The first two factors stay in the coefficient of $r$. The smooth side gets a period dividing ${\rm lcm}(c_2,b_0)$, where $b_0$ is the existing $Y_0$-roughness period from its factorial truncation. Its tail is negligible even with $W_N$: the weight and all the actual divisor-choice multiplicities are bounded by fixed powers of the endpoint divisors. The endpoint masks on $q,h$ still have $H^{o(1)}$ periods and choices.

Use the pinned joint-frequency determinant proof with first period $E=H^{o(1)}$, second period $F_0\le D^2 H^{o(1)}$, and $r\le H^{21/20}$. That proof allows $F_0\le H^\rho$, $E\le H^{5\rho}$ and at most $H^{6\rho}$ total mask cost for all sufficiently small fixed $\rho>0$ at this strict grouped exponent. Choose $\kappa<\min(\rho/8,1/100)$; then $D^2=H^{4\kappa}$ and the $a,b$ choices and their splits and all the other masks fit inside that budget. The $\lambda$ coefficients have magnitude at most one. The exact support and the smooth derivatives are as in the old proof. Thus the nonzero modes still save a fixed power. [Pinned polynomial-period budget](https://github.com/Sodelin/Research-Commons/blob/9a77141e26f67c56ec8c61102ce6516f5ed24f12/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-joint-frequency-cutoff.md)

The zero mode has reciprocal factor $1/[E,F_0]$. It uses the original signed $h$ prefix with excluded integer $NrF_0<N^2$. The condition $c_1\mid r$ counts $O(R/c_1)$ values on scale $R$ for $r$. Thus the mask sum uses $1/(c_1[E,F_0])$. A selected prime in $c_1$ pays $1/p$ there, and a prime in $c_2$ pays $1/p$ in $[E,F_0]$. Together with the other prime subset masks on $q,s$ this has only boundedly many local patterns. Its total is polylogarithmic by $\prod_{p\le N}(1+C/p)$, with the square and gcd truncations costing polylogarithmic factors. The prefix saving absorbs them. This proves the two Type I bounds with the weight intact.

## Averaging the Type II square over the two factors

The individual $B_V$ weights are nonnegative and their full sum is at most $\log v$, so the absolute weight of the retained sum is $\ll W_N(n)\log\ell$ per fixed $q,h,\ell,u,v$. This also holds on any further selected intersection. For absolute upper bounds we can enlarge the endpoint masks while keeping $M$ coprime to $N$ below. Trim $n<N/L^B$ at arbitrary log savings by the divisor moments and $W_N(n)\le\tau(n)^2$. On the dyadic band $N2^{-j-1}<n\le N2^{-j}$, both $q,h$ lie within $H2^{-j}$ of $H$. This follows from $N-qh\ge H(H-q)$ and its analogue for $h$. Use their containing rectangle of area at most $N4^{-j}$.

Put $x=\min(u,v)$, $y=\max(u,v)$. Then $2\log x=\log(n/\ell)-|\log(u/v)|$, so for each $\ell,j$ the possible $x$'s lie in a log interval of width $O(1+\Delta)$ at polynomial scale, with $x\ge N^{1/5}$. The two orientations cost at most two in the positive count. Fix $\ell,x$ and put $M=\ell x$. Then $y=(N-qh)/M$, $(M,N)=1$, and

$$
M\le\sqrt{\ell n}\le N^{9/16}.
$$

For fixed $a,b$ in the square let $c=[a,b]$. A prime $p\mid c$ that divides $x$ already divides $n$. Otherwise, since $\ell>z$, the test $p\mid n$ is a CRT condition $qh=N\bmod p$ at a prime coprime to $M$. The density is $g_p$. Enumerate those residue pairs and apply the rectangular unit-hyperbola completion modulo $M$. The main term at fixed $\ell,x$ for the count weighted by $W_N(n)$ is the rectangle area times

$$
\frac{\varphi(M)}{M^2} Z(x),\qquad
Z(x)=\sum_{a,b}\lambda_a\lambda_b\prod_{p\mid[a,b],\,p\nmid x} g_p.
$$

For a pair $a,b$, at most $D^2 N^{o(1)}$ residue pairs are used, since the new modulus divides $[a,b]\le D^2$ and the local number of residues is at most $2p-1$. There are at most $D^2$ such pairs. Thus the error at fixed $\ell,x$ is $D^4N^{o(1)}M^{1/2}(1+H/M)$. This uses the same composite-modulus completion for short rectangles as the peer proof. Summing over the $O(1+\log L)$ endpoint bands and $M\le N^{9/16}$ costs $N^{27/32+4\kappa+o(1)}$ after the log weights: each $M$ has at most $\tau(M)$ representations and the terms $M^{1/2}+H/M^{1/2}$ have sums $O(N^{27/32}+N^{25/32})$. This is a power saving. [Pinned rectangle and CRT estimate](https://github.com/Sodelin/Research-Commons/blob/909738e51f1ea4abe94c119276375481f85abc56/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-balanced-two-prime-sieve.md#count-at-a-fixed-composite-modulus)

For each $x$, $Z(x)\ge0$: it is the expectation of the same Selberg square with the primes of $x$ forced present and all other flags independent of probabilities $g_p$. Therefore the upper main term can use $\varphi(M)/M^2\le1/M$ and sum over all integer $x$ in the chosen dyadic scales, including those excluded by $(M,N)=1$. This enlargement is of the formal nonnegative main term only. For each $c=[a,b]$ the product in $Z(x)$ is

$$
\prod_{p\mid c}\big[g_p+(1-g_p)\mathbf1_{p\mid x}\big].
$$

Its expansion over divisors of $c$ has nonnegative scalar coefficients with sum one. The reciprocal sum over multiples of any $r$ in $X<x\le2X$ is $(\log 2)/r+O(1/X)$ uniformly in $r$, by the integral estimate for a harmonic interval. The main term of averaging the product therefore replaces $\mathbf1_{p\mid x}$ by $1/p$ in every factor. In the quadratic sum this gives

$$
\sum_{X<x\le2X}\frac{Z(x)}x
=(\log 2) Q(\lambda)+O(D^2/X)\ll\frac{\varphi(N)}{N L^2},
$$

since $X\gg N^{1/5}$, $\kappa<1/100$ and $\varphi(N)/N\gg 1/L$ by Mertens. This proves the two-factor saving at polynomial sifting scale. The $O(1+\Delta)$ dyadic $x$ intervals cost that factor. The actual prime interval gives $\sum_\ell\log\ell/\ell\ll1+W$ by Chebyshev. Finally $\sum_j4^{-j}\ll1$, so the displayed bound follows.

The remaining signed Type II estimate concerns broad ratio widths in this same weighted expansion on targets where $\varphi(N)$ is comparable to $N$. Powers of two already belong to that class. A fixed-target lower bound with a saving on this remainder is still required.
