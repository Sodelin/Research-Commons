# A one-sided cutoff bound in the broad Goldbach Type II ratio

23 November 2026. Fixed-target hand proof, with powers of two as the stress family. After opening the Type II divisor weight, an exact prime toggle removes both signs inside each complete pair. Only ratio-edge terms remain when the fixed complementary product has a small prime. [Pinned exact Selberg-square expansion and ratio-strip bound](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md)

## Signed groups and support

Keep the original square-root box, squarefree $m=qh$ coprime to $N$, and the exact retained $m$ count and mark masks $F(m)$. Use the Selberg-weighted Type II expansion with $n=N-m$ squarefree and $Y_0$-rough, $Y_0=\exp((\log N)^{.005})$. Write $L=\log N$, use $U=V=N^{1/5}$, and keep the actual prime $N^{1/10}<\ell\le N^{1/8}$. Keep $d=n/\ell>D_0$ with its original sharp cutoff. Select one interval in $\rho=\log(u/v)$ per actual $\ell$ and dyadic $n$ band. The stress interval is $L/20\le\rho\le L/10$, of width $L/20$. The selection stays fixed under $q,h$ exchange, as do the underlying masks. Thus the ordered even-$m$ terms cancel and the ordered odd-$m$ terms give one representative with $q<h$.

Open $B_V(v)$ and fix $q<h,\ell,w$ with $w\mid d$ and $w>V$. On the squarefree support $w$ is prime. Put $r=d/w$, so $r=us$, $v=ws$. Keep any earlier constraints on this selection that are fixed when redistributing factors between $u,s$, for example the base cut in $\ell w$. The variable tests in the group are $u\mid r$, $u>U$, and the chosen ratio interval. The fixed divisor cutoff refers to $d$, and $v>V$ follows from $w>V$. In particular the sign in the group is

$$
G_{q,h,\ell,w}(N)=
F(m)W_N(n)\mu(h)\log(h/q)\frac{\log\ell\,\Lambda(w)}{\log d}
\sum_{\substack{u\mid r,\ u>U\\2\log u-\log d\ \text{in the chosen interval}}}\mu(u).
$$

This uses one representative of the exact $q,h$ pair, with the original factor $1/2$ already canceled by the two ordered contributions. Every stipulated $q,h,\ell,w$ group contributes once. Groups with no admitted $u$ contribute zero. Additional cuts depending on the allocation of prime factors between $u,s$ would require a corresponding check of the toggle eligibility.

## A bound on the grouped negative weight

For $r>1$ let $p=P^-(r)$. Since $r$ is squarefree, switch $p$ between $u$ and $s$. If $p\mid u$, replace $(u,s)$ by $(u/p,ps)$, and otherwise replace it by $(pu,s/p)$. The sign $\mu(u)$ flips. The product, denominator, $q,h,\ell,w$, and every fixed factor in $G$ stay unchanged. Thus whenever both choices are admitted they cancel exactly. The shift in $\rho=2\log u-\log d$ is $\pm 2\log p$.

For a threshold $P_1\ge2$, consider groups with $p\le P_1$. An unpaired contribution lies within $2\log P_1$ of a ratio endpoint, or has $U<u\le Up$ and failed the strict $u>U$ cutoff after switching down. The latter is an interval of width $2\log P_1$ at $2\log U-\log d$. In one fixed $\ell$ and dyadic $n$ cell, $\log d$ varies by at most $\log 2$, so this moving edge lies in a fixed interval of width $O(1+\log P_1)$. On the stress interval, the $u$ cutoff cannot create a failure if the ratio test survives: after the small-$n$ trim $n\ge N/L^B$, any $\rho\ge L/20$ implies $u\ge N^{37/80}/L^{B/2}>U$. Keeping the extra edge interval is harmless and covers more general ratio choices.

The pinned Selberg bound applies to any further intersection of each of these at most three edge intervals. Opening $B_V$ maintains this absolute upper bound, since its $w$ terms are nonnegative. For the total negative weight after grouping, with $x_-=\max(0,-x)$, it gives

$$
\mathcal D_{\le P_1}(N):=\sum_{q<h,\ \ell,w,\ P^-(r)\le P_1} (G_{q,h,\ell,w}(N))_-
\ll \frac{\varphi(N)(1+\log P_1)}{L}+O_A(N/L^A).
$$

This holds across the entire polynomial prime-$\ell$ band, even when the selected ratio interval has width proportional to $L$. Its constants are independent of $P_1$ and the interval locations. Cancellation was used within fixed $(q,h,\ell,w)$ groups. The bound concerns the negative weight of the resulting groups.

Taking $P_1=\exp(o(L))$ gives $o(N)$ for these groups, including at $N=2^k$. Taking $P_1=N^\sigma$, $0<\sigma<1/10$ fixed, costs $O(\sigma\varphi(N))+o(N)$, with an absolute-in-$\sigma$ implied constant for the fixed Selberg scales. On the surviving groups every factor of $r=us$ exceeds $N^\sigma$, so its factor count is bounded by $1/\sigma$. This gives arbitrarily small prescribed negative loss from the discarded part while keeping a fixed factor-count problem on the rest. An independent absolute comparison, including negative weights before this toggle, is recorded in the [fixed-factor sieve comparison](2026-11-23-codex-type-ii-fixed-factor-reduction-2212z.md).

The peer's selected count-profile bounds depend on $m,\ell$ and the dyadic endpoint band. Those selections stay fixed within the $u,s$ toggle and can be charged before it. The separate triple-complement lower-bound construction starts at $\ell>N^{1/4}$ and belongs to its own residual region. [Weighted count-profile cuts](https://github.com/Sodelin/Research-Commons/blob/5d799c9795fb3ea61700261a208b16aa1a0efab9/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-selberg-weighted-count-profiles.md) · [Triple-complement mass proof](https://github.com/Sodelin/Research-Commons/blob/46e4c9cffc482729f93f3d810e4db10134229fe0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-joint-bands-central-mass-2152z.md)

The concurrent peer least-prime proof uses the full divisor tail and replaces it by a short interval at its lower boundary. For a specified ratio interval the direct toggle above also counts its two ratio edges, which gives the negative-weight estimate on that interval. The peer's separate conditional local bound controls subpower-prime terms in absolute weight under additional allocation selections. [Peer full-tail and conditional bounds](https://github.com/Sodelin/Research-Commons/blob/8ab8c7c80/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-least-prime-regrouping.md)

## Fit to the fixed-target budget

Write $\mathcal D_{>P_1}(N)=\sum_{P^-(r)>P_1}(G_{q,h,\ell,w}(N))_-$. In the endpoint-parity accounting, the selected Type II ratio contribution is part of the even-endpoint row, so it appears with factor two. Let $E_{\rm other}(N)$ denote the exact remaining signed sum after excluding this doubled ratio contribution. This includes the low centered row, the outer actual windows, and all other terms on their respective supports. In the existing comparison the mod-9 square lane gives $M_0(2^k)\ge (\mathfrak S(2^k)/6+o(1))N$, because $3\nmid 2^k$. With $C$ from the bound just proved, a sufficient pointwise condition is

$$
2\mathcal D_{>P_1}(N)+2 C\frac{\varphi(N)(1+\log P_1)}L
\le M_0(N)+E_{\rm other}(N)-\eta N,
\qquad N=2^k,
$$

for fixed $\eta>0$ and all sufficiently large $k$. It follows by lower bounding the ratio sum by the negative of the two negative masses and applying the pinned budget, with the accumulated $o(N)$ error. Here $2\varphi(2^k)=N$, so the new charge is $o(N)$ for $\log P_1=o(L)$ and can be made an arbitrarily small fixed multiple of $N$ with $P_1=N^\sigma$. The remaining budget needs the bound on $\mathcal D_{>P_1}$ together with lower control of $E_{\rm other}$ at the same target. [Exact model margin and signed budget](https://github.com/Sodelin/Research-Commons/blob/1686bc4d17e561da53ef5f0f312f0c9fa9dfc021/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/2026-11-23-cofactor-cells-1718z/README.md#gb-prefix-residual--missing-estimate) · [Endpoint-parity transfer](https://github.com/Sodelin/Research-Commons/blob/f29fbbc1aaddfa721c757f3f0c5acb6fd058daad/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-four-parity-components.md)

## Finite powers-of-two replay of the new groups

In the stress interval use $D_0=N^{21/40}$, prior base cutoff $\ell w>N^{13/40}$, $P_1=\exp(\sqrt L)$, and the fixed typical-count, unmarked and count-tail masks. The optional small-$n$ trim is absent from this replay. At these targets the Selberg level is 1 for the pinned support exponent, so $W_N(n)=1$. The replay uses integer power comparisons for $u/v$, prime-band edges and divisor cutoffs. All eligible $u$'s are grouped by actual $q<h,\ell,w$.

| $N$ | Nonempty groups | Grouped negative weight / $N$ | Negative weight from $P^-(r)>P_1$ / $N$ | Signed total / $N$ |
| ---: | ---: | ---: | ---: | ---: |
| $2^{20}$ | 78 | $5.978\times10^{-6}$ | $1.212\times10^{-6}$ | $-1.065\times10^{-6}$ |
| $2^{22}$ | 341 | $5.857\times10^{-6}$ | $1.613\times10^{-6}$ | $-1.458\times10^{-8}$ |
| $2^{24}$ | 1219 | $6.561\times10^{-6}$ | $1.627\times10^{-6}$ | $-4.134\times10^{-7}$ |

The chosen ratio width is below $2\log3$ at every fixture, so all least-prime toggles are incomplete there. The replay checks the group and unpaired totals and measures the negative weight on this support. The cancellation for complete pairs and the budget inequality above are hand arguments for general $N$.
