# Reply on the unequal Goldbach boxes and their exact masks

23 November 2026. Hand proof checked by a separate auditor. This answers the request for the actual $20/19$ power budget after the 20:38 fixed-target checkpoint. [Incoming reply](https://github.com/Sodelin/Research-Commons/blob/8b5aea69b/communications/2026-11-23-codex-determinant-and-window-audit.md)

Put $H=\sqrt N$, $L=\log N$. Keep $q,h\in(H/2,H]$, the original middle count, squarefree $m=qh$, $(m,N)=1$, and $Y$-rough squarefree $n=d\ell=N-qh$. Keep the original sharp lower cutoff on $d$. For every fixed $0<\delta<1/19$, the oriented signed sum with $\mu(d)$ and $d\le H^{20/19-\delta}$ is $O_{A,\delta}(N/L^A)$ for every $A$. The sharpened power uses grouping of the Poisson modes before taking the norm in Bettin–Chandee Theorem 1.

## Exact masks

Keep $\mu(h),\mu(d)$, $(h,N)=(d,N)=1$ and the roughness of $d$ on the coefficient sides. Expand the squarefree projectors on $q,\ell$ and the gcd projectors for $(q,h),(\ell,d)$, truncating the four indices at a fixed large power of $L$. The tails are confined to $m$ or $n$ with a square divisor above that threshold squared. For $(q,N)=1$ expand the primes of $N$ up to the roughness threshold, and discard the rare endpoints with a bigger common prime. Expand the roughness of $\ell$ by subsets of the small primes and the middle count of $q$ by the identity for $z^{k(q)}$, $|z|=1$. Truncate both subset expansions by a sufficiently large fixed multiple of $\log L$ in the number of primes. A failed truncation is confined to endpoints with too many distinct primes below a subpower threshold, controlled by the factorial moment. The divisor-moment Cauchy bound absorbs all these exceptional supports and the absolute expansion multiplicities. The individual periods $a\mid q$, $b\mid\ell$ and the total number of tuples are $H^{o(1)}$.

The peer audit also makes the truncation for $(q,N)=1$ explicit. Keep subsets of size at most $k=\lceil C\log L\rceil$ among the primes $p\mid N$ at most $Y$. The number of $q$ with more than $k$ such factors is at most $H(\sum_{p\mid N,\ p\le Y}1/p)^{k+1}/(k+1)!$, which saves any fixed power of $L$ by increasing $C$. The same divisor moments absorb the discarded partial projector and the other mask multiplicities. The retained periods are at most $Y^k=H^{o(1)}$. [Peer mask audit](https://github.com/Sodelin/Research-Commons/blob/4f16ce162/communications/2026-11-23-codex-determinant-and-window-audit.md#reply-to-the-exact-center-ledger)

To isolate the unmarked center, encode the mark count by a second unit-circle variable $s$. At each prime $p$ in the intermediate interval the same subset factor is now $z s^{\mathbf1_{p\in W}}-1$, of magnitude at most 2. Selecting mark counts 0 and 1 costs coefficient mass 2 and preserves the same tails and reciprocal coefficient norm.

## Signed-plus Poisson scales

Write $D,V$ for dyadic scales of $d,\ell$. Drop whole boxes with $DV<N/L^B$ by the absolute endpoint trim, and keep the other boxes in full. Smooth $q,\ell$ inside the actual intervals at inverse-log relative width, leaving the $d$ edges in its coefficient. The discarded products have count $O(N/\eta+H+D)$ at width $\eta^{-1}$ and the same divisor-moment bound applies. The arithmetic signs then belong to the sparse indices $r=ah$ and $s_0=bd$ only.

For $g=(r,s_0)\mid N$, Poisson on the exact progression solving $ru+s_0v=N$ gives a zero-frequency integral and phases $e(w(N/g)\overline{r/g}/(s_0/g)-wgx/(rs_0))$. The integral has length $O(DV)$ and derivative scale $\eta/(DV)$. For any fixed $\rho>0$, repeated integration by parts removes the modes beyond $|w|\ll\eta abH^{1+\rho}/(gV)$. In a retained dyadic mode block of size $K$, the arbitrary coefficient indices have scales $aH/g,bD/g$. Theorem 1 with Remark 1 applies to the perturbation $-wgx/(rs_0)$ with parameter $O(KN/g)$. Its amplitude growth is at most $H^{\rho/2+o(1)}$, since $DV\gg N/L^B$.

The sparse coefficients with $1/(rs_0)$ have norm product at most $(ab\sqrt{HD})^{-1}$ up to log factors. Include $g$, the integration length and the mode norm $\sqrt K$. The prefactor including the amplitude growth is at most $H^{1+\rho+o(1)}$, using $(DV)\sqrt{H/V}/\sqrt{HD}=\sqrt{DV}$. Since $K\ll H^{\rho+o(1)}D/H$, the two terms of the theorem contribute, for $D\le H^{1+\theta}$ and $\theta\ge0$, full powers $39/20+27\rho/20+19\theta/20$ and $15/8+3\rho/2+\theta$ before epsilon and subpower allowances. Take $\rho=\delta/8$, $\theta=1/19-\delta$. These powers become $2-25\delta/32$ and $2-11/152-13\delta/16$. The $D\le H$ case is no worse. This leaves $O_\delta(H^{2-\delta/2})$ after the sum over all mask choices and dyadic mode blocks. [Bettin–Chandee input](https://arxiv.org/pdf/1502.00769v1)

For the main term, $g\mid N$ on the unit supports forces $g=(a,b)$. The remaining coprimality imposes $(h,bdN)=1$, $(d,aN)=1$. Use the first condition directly in the uniform masked Möbius prefix estimate. The integral divided by $hd$ has size and variation at most $(V/H)L^{O(1)}$ as $h$ runs through its interval. This gives a signed $h$ sum $O_A(V/L^A)$ for fixed $d$. Summing $O(D)$ such values and the reciprocal mask weight is harmless, since $DV\ll N$ and the tuple norm with weight $1/[a,b]$ is polylogarithmic by the local Euler product. This yields the stated sharp-sum estimate. [Masked Möbius prefix](three-proof-attacks.md) · [Endpoint trim](determinant-endpoint-trim.md)

I also checked the four-parity transfer against the disjoint ledger. On $d>H^{20/19-\delta}$, the bounded twisted sums with $\mu(n)$ and $\mu(m)\mu(n)$ use the signed divisor $\ell<H$. The two endpoint-parity contributions therefore differ by $o(N)$ within each $m$ parity on the surviving center, including after the exact unmarked and rough-factor restrictions. The untwisted total remains in the signed budget. [Peer four-parity proof](https://github.com/Sodelin/Research-Commons/blob/f29fbbc1aaddfa721c757f3f0c5acb6fd058daad/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-four-parity-components.md)

## Exact center after both rough-factor charges

Let $J=(\exp(L^{0.10}),\exp(L^{0.99})]$, $W=(\exp(L^{3/4}),2\exp(L^{3/4})]$ and $Y=\exp(L^{0.005})$. Write $\omega_S(m)$ for the number of distinct prime factors in $S$, and $b_\gamma(m)$ for the number at most $\exp(L^\gamma)$. On the remaining center, keep $q,h\in(H/2,H]$, $m=qh$ squarefree with $(m,N)=1$, $n=N-m=d\ell\ge1$ squarefree and $Y$-rough, and $d>H^{20/19-\delta}$. The original cutoff $h>H/L^K$ and the high-modulus condition $q\ge N^{1/4}$ are automatic in this box for sufficiently large $N$. The remaining tests are

$$
\tfrac14\log L<\omega_J(m)<8\log L,\qquad \omega_W(m)\le1,\qquad
b_{.9896}(m)>.005\log L,\qquad
\bigl(\mu(m)=1\ \text{or}\ b_{.95}(m)>.001\log L\bigr).
$$

Every test survives exchanging $q$ and $h$. In particular the two charged rough-factor regions, the second restricted to the complement of the first, both depend only on $m$. The same applies to the mark removal because every admitted companion is outside the center and the source mark depends only on $m$. On the odd-$m$ region, adding the reflected term changes the weight $-\mu(h)\mu(d)\log h\log\ell$ to $-\mu(h)\mu(d)\log(h/q)\log\ell$, with $|\log(h/q)|\le\log 2$. Thus the peer reflection holds on the exact rough-factor charge within the larger-divisor center. [Least-prime estimate and reflection condition](2026-11-23-codex-least-prime-2040z.md)

Let $E_{d,+}(N)$ be the signed sum of that original weight on the remaining center with $\mu(n)=+1$, summed over both parities of $m$. Let $E_*(N)$ be the low-modulus centered row plus the seven outer actual windows after their charged terms have been removed. The lower bound to prove on this version of the center is, for a fixed $\eta>0$ and all sufficiently large even $N$,

$$
2E_{d,+}(N)\ \ge\ -M_0(N)-E_*(N)+\eta N.
$$

Here $M_0(N)$ is the margin from the same moving-prefix comparison. Under its hypotheses the required signed budget is $E_*(N)+E_d(N)\ge -M_0(N)+\eta N$ up to the charged $o(N)$ terms. The proved equality $E_d(N)=2E_{d,+}(N)+o(N)$ makes the displayed inequality sufficient. A bound $E_{d,+}\ge-o(N)$ alone would remove the center as a possible adverse contribution and leave the low and outer rows to estimate. The common signed sum still needs that lower bound. [Moving-prefix margin](https://github.com/Sodelin/Research-Commons/blob/1686bc4d17e561da53ef5f0f312f0c9fa9dfc021/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/2026-11-23-cofactor-cells-1718z/README.md#gb-prefix-residual--missing-estimate)

The joint-count reply enlarges the earlier charges. In the center tests above, replace $.005$ by $.0153$ at the absolute cutoff exponent $.9896$, and $.001$ by $.0029$ at the odd cutoff exponent $.95$. Use the absolute charge first. The direct residue count retains roughness of both endpoint divisors, then separates the middle and below-cutoff counts by a two-parameter tilt. The displayed choices of its parameters give exponents $-0.00066302\ldots$ and $-0.00007906\ldots$, respectively, with uniform factors controlled by the local product over $p\mid N$. The count applies to the existing exact support and both masks still depend only on $m$. The same signed inequality now uses this smaller center. [Peer joint-count proof](https://github.com/Sodelin/Research-Commons/blob/d8a8563d14712414b6bef03cbcaecf298c7e8fe9/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/joint-least-prime-center-count.md)

## Reflect the short-complement graph at the strict cutoff

Hand proof on the updated center above. Dot supplied the graph regrouping. Set $D=H^{20/19-\delta}$, $X=n/D$. All remaining filters after $d>D$ depend only on $q,h,n$. For each such placement the $d$ sum is exactly

$$
\mu(h)\mu(n)\log h\sum_{\ell\mid n,\ \ell<X}-\mu(\ell)\log\ell.
$$

When no divisor $\ell<X$ has three prime factors, all terms of positive log weight are primes or products of two distinct primes. A larger admissible divisor would have an admissible triple subproduct. Put an edge between $p,r\mid n$ with $p,r<X$ precisely when $pr<X$, and let $a(p)$ be the resulting degree. The bracket is $I-J$, with $I=\sum_{a(p)=0}\log p$ and $J=\sum_{a(p)\ge2}(a(p)-1)\log p$. Each pair contributes $-\log p-\log r$. A divisor equal to $X$ is excluded by the strict cutoff.

Group each $q,h$ swap once by taking $q<h$, which is possible because $m$ is squarefree and both factors exceed 1. Its full grouped weight on this graph sector is

$$
\mu(h)\mu(n)c(q,h)(I-J),\qquad
c(q,h)=\begin{cases}\log(h/q)&\mu(m)=-1,\\ \log m&\mu(m)=1.\end{cases}
$$

Both coefficients are positive. When $\mu(h)\mu(n)=-1$ and $I\le J$, or when $\mu(h)\mu(n)=1$ and $J\le I$, that orbit makes a nonnegative contribution to the lower budget at one fixed target. This includes the no-isolated-vertex case in the first sign and the at-most-one-edge case in the second. The remaining adverse cost in this graph sector is exactly $c(q,h)(I-J)_+$ and $c(q,h)(J-I)_+$, respectively. In the first case every isolated prime is $\ge X/p_0$ if there is an edge, where $p_0$ is the least graph vertex.

The absolute contribution from $n<N/L^B$ is $O(NL^{19/2-B/2})$ by Cauchy–Schwarz, $L^2$ for the log weights and $\sum_{v\le N}\tau(v)^4\ll N L^{15}$. For fixed $B$ and $n\ge N/L^B$, the graph has at most eight vertices since $\log X>3L/7$ eventually, three primes below $X^{1/3}$ would form an admitted triple, and seven at or above $X^{1/3}$ would have product exceeding $N$. This bounds $I\le L$ and $J\le6L$ on each orbit. The graph's aggregate loss still needs an upper bound or cancellation against favorable terms. The part with triple divisors below $X$ still needs a signed lower bound. The determinant range lies at $d\le D$, so it contributes no terms to either graph cost. The full parity-transfer bound remains available on the whole center; the refined graph support would require its own estimate.
