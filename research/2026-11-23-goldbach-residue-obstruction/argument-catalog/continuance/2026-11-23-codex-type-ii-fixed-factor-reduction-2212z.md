# Polynomial roughness and a fixed factor-count reduction in Goldbach Type II

23 November 2026. Hand proof at one fixed even target. The polynomial Selberg-square expansion gives an absolute comparison with exact polynomial roughness, even on a broad ratio interval. This reduces the signed estimate there to configurations with a fixed maximum number of prime factors, with an arbitrarily small prescribed loss on the target scale. [Pinned Selberg-square expansion](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md) · [Peer main-term check](https://github.com/Sodelin/Research-Commons/blob/ce907e7b0/communications/2026-11-23-codex-determinant-and-window-audit.md#reply-to-the-polynomial-scale-selberg-type-ii-bound)

## Exact support and claim

Set $L=\log N$, $H=\sqrt N$. Use the same ordered $q,h\in(H/2,H]$, $m=qh$ squarefree, $(m,N)=1$, and the exact retained mask $F(m)$. Keep $n=N-m=\ell uv$ squarefree and $Y_0$-rough, $Y_0=\exp(L^{.005})$, actual prime $N^{1/10}<\ell\le N^{1/8}$, $u,v>N^{1/5}$, the original sharp condition $uv>D_0$, and any earlier endpoint cut. Write

$$
a(q,h,\ell,u,v)=\tfrac12F(m)\mu(h)\mu(u)B_V(v)\log(h/q)\frac{\log\ell}{\log(uv)},
\qquad B_V(v)=\sum_{w\mid v,\,w>V}\Lambda(w),\quad V=N^{1/5}.
$$

The $w$ sum may keep any earlier specified intersection in the equivalent expansion. Its terms are nonnegative and its full sum is at most $\log v$. For fixed small $\kappa>0$ from the pinned Type I proof, take level $D=N^\kappa$ and a fixed polynomial sifting threshold $z=N^\delta$, $0<\delta<\min(\kappa,1/10)$. Denote by $W_N(n)$ the pinned Selberg square at those parameters. Define $R_z(n)=\mathbf1_{P^-(n)>z}$ and let $T_W(E)$ and $T_z(E)$ be the signed sums with weights $aW_N(n)$ and $aR_z(n)$ on the same selected support $E$.

Allow the prime $\ell$ interval to have log width $W$ and the $\log(u/v)$ interval in each fixed $\ell$ and dyadic $n$ cell to have width at most $\Delta$. The interval locations may vary across cells. For all sufficiently small fixed $\delta/\kappa$ the comparison is

$$
|T_W(E)-T_z(E)|
\le C\delta^{-2}e^{-c\kappa/\delta}
\frac{\varphi(N)(1+W)(1+\Delta)}{L^2}+
O_{A,\delta}(N/L^A),\qquad c,C>0.
$$

The constants $c,C$ can be chosen independently of small fixed $\delta$. The same upper bound holds for the sum of absolute weight differences. It also bounds the change in total negative weight after any fixed disjoint grouping, since $|x_--y_-|\le |x-y|$ for $x_-=\max(0,-x)$. In particular it applies to a broad interval such as $L/20\le\log(u/v)\le L/10$ and to the full range. For any prescribed $\epsilon>0$, choose a sufficiently small fixed $\delta$ to make the bound $\epsilon\varphi(N)+O_{A,\epsilon}(N/L^A)$ on the full prime and ratio ranges. On $R_z$ each nonzero tuple has at most $\lfloor1/\delta\rfloor$ distinct prime factors in $n$, all exceeding $N^\delta$. Thus the remaining compositions of $u,v$ have bounded length and $\mu(u)$ is the sign of its exact factor-count parity. The $h$ sign still requires a correlation estimate.

## A nonnegative difference of sieve weights

As in the pinned proof, for $p\le z$ put $g_p=(p-1)/p^2$ if $p\nmid N$ and $g_p=(2p-1)/p^2$ if $p\mid N$. The local factor after averaging over the smaller inner divisor is $g_{2,p}=g_p+(1-g_p)/p$. Set $\mathcal V(z)=\prod_{p\le z}(1-g_{2,p})$. The explicit factors from the prior proof give $\mathcal V(z)\ll\varphi(N)/(N(\delta L)^2)$, with a uniform constant once $N$ is sufficiently large for fixed $\delta$.

Use the lower weights of the fundamental lemma for the density $g_2$ and squarefree indices $b\le D$ on primes at most $z$. These have $|\lambda_b^-|\le1$ and $\Lambda^-(n)=\sum_{b\mid n}\lambda_b^-\le R_z(n)$. The dimension bound is uniform with dimension three: $1-g_{2,p}\ge(1-1/p)^3$ for every $p$, so the Mertens product bound on each prime interval has that dimension. At depth $\log D/\log z=\kappa/\delta$ sufficiently large the lower quadratic-model main term satisfies

$$
\sum_b\lambda_b^-g_2(b)\ge\mathcal V(z)(1-O(e^{-c\kappa/\delta})).
$$

Here $g_2(b)=\prod_{p\mid b}g_{2,p}$ on squarefree $b$. This is the lower fundamental-lemma bound with a weakened exponential error, uniform for the displayed local density. [Two-sided fundamental lemma, Theorem 3.6(a)](https://ford126.web.illinois.edu/sieve2023.pdf) · [Peer use of polynomial periods](https://github.com/Sodelin/Research-Commons/blob/8964660fb05a3bf80db2793c02708497e7d071c5/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-fundamental-lemma-log-windows.md)

The upper square has main term $1/G_D$ in the same model. A sharper bound for its truncated denominator gives the matching error. In the full Euler product $G_\infty=\mathcal V(z)^{-1}$, the normalized mass is the product law with each prime $p$ selected with probability $g_{2,p}$. Write $K$ for the product of the selected primes. Then

$$
\log\mathbb E K^{1/\log z}
\le \sum_{p\le z}g_{2,p}(p^{1/\log z}-1)
\ll \frac{1}{\log z}\sum_{p\le z}\frac{\log p}{p}\ll1.
$$

This uses $g_{2,p}\le3/p$ and $e^t-1\le(e-1)t$ on $[0,1]$. Markov gives $\mathbb P(K>D)\ll e^{-\kappa/\delta}$, so $G_D/G_\infty=1-O(e^{-\kappa/\delta})$. Therefore

$$
0\le \frac1{G_D}-\sum_b\lambda_b^-g_2(b)
\ll \mathcal V(z)e^{-c\kappa/\delta}.
$$

The pointwise divisor polynomial $P(n)=W_N(n)-\Lambda^-(n)$ is nonnegative: $W_N(n)=1$ on the rough support and $W_N(n)\ge0$ elsewhere, while $\Lambda^-\le R_z$. It also dominates $W_N(n)-R_z(n)\ge0$. Its coefficients, after collecting on squarefree $b\le D^2$, have total absolute mass at most $D^2+D$.

## Count the difference on the same Type II support

The absolute original coefficient $|a|$ is $O(\log\ell)$ after summing the admitted $w$ terms. Hence it suffices to upper bound $\sum\log\ell\,P(n)$ on a positive enlargement of the same support. The trim $n<N/L^B$ still costs $O_A(N/L^A)$ by fixed divisor moments, because $P(n)\le\tau(n)^2+\tau(n)$. In each retained dyadic $n$ band the containing rectangle for $q,h$ has area $O(N4^{-j})$. With $x=\min(u,v)$, the same log-ratio identity bounds its log range by $O(1+\Delta)$. Fixing actual $\ell,x$ gives unit modulus $M=\ell x\le N^{9/16}$ and determines the other inner factor from $q,h$.

For the general divisor polynomial $P(n)=\sum_c a_c\mathbf1_{c\mid n}$ just defined, the CRT local kernel is

$$
Z_P(x)=\sum_c a_c\prod_{p\mid c,\,p\nmid x}g_p.
$$

It is nonnegative at each $x$: force the flags at primes dividing $x$ present, take independent flags of probabilities $g_p$ elsewhere, and take the expectation of the pointwise polynomial in that flag set. Each flag pattern is the set of primes of a squarefree product, so the inequality for $P$ applies. This positivity permits enlarging the formal main term to all $x$ in the containing dyadic intervals and replacing $\varphi(M)/M^2$ by $1/M$, just as for the square. The completion estimates continue to require $(M,N)=1$ on the actual counted support.

The product in $Z_P(x)$ expands as $\prod_{p\mid c}(g_p+(1-g_p)\mathbf1_{p\mid x})$. For a given $c$ the coefficients in the divisibility expansion are nonnegative with sum one. The reciprocal sum of multiples of $r$ on $X<x\le2X$ is $(\log2)/r+O(1/X)$ uniformly in $r$. Thus averaging the kernel gives

$$
\sum_{X<x\le2X}\frac{Z_P(x)}x
=(\log2)\sum_c a_c g_2(c)+O(D^2/X).
$$

Since $X\gg N^{1/5}$, the floor error saves a fixed power after restoring weights and log widths. The complete CRT error per $M$ is $N^{4\kappa+o(1)}M^{1/2}(1+H/M)$: the coefficient sum is $O(D^2)$ and the auxiliary residue-pair count is $D^2N^{o(1)}$. Summing with the log weights and divisor multiplicities as before gives $N^{27/32+4\kappa+o(1)}$. The same fixed $\kappa<1/100$ gives a power saving. Summing the main term uses $\sum_j4^{-j}\ll1$, the $O(1+\Delta)$ dyadic $x$ intervals and $\sum_\ell\log\ell/\ell\ll1+W$. Substitute the bracket bound above to obtain the stated comparison. [Pinned harmonic averaging and CRT error](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md#averaging-the-type-ii-square-over-the-two-factors)

## Consequence for the signed lower bound

The parameter $\delta$ is fixed after specifying the error tolerance, then the estimates are taken as $N\to\infty$. The two Type I bounds still identify the full prime-tested semiprime band with $T_W$ up to arbitrary log saving for each such choice. A fixed-target lower bound $-o_\delta(N)$ on the stipulated polynomially rough broad configurations, for all sufficiently small fixed $\delta$, would therefore suffice after taking the tolerance to zero. For a selected ratio interval, the comparison is between two sums at the same $\delta$ in the displayed expansion. The signs $\mu(h)$ and $\mu(u)$ and the actual prime $\ell$ stay in both. This removes the part with a small endpoint prime up to the prescribed loss. It leaves the signed correlation among the bounded-factor configurations.
