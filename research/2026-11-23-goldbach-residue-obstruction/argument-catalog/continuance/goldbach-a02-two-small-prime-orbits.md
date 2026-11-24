# Exact small-prime allocation cancellation in the unmatched Goldbach outer row

**Unconditional hand proof at fixed \(N=2^k\).** Put \(L=\log N\), \(H=\sqrt N\), \(Q=N^{1/4}\), and \(\alpha=H/L^{K_0}\). The row here is the raw unmatched part of \(A_{02}\), with \(Q\le q\le\alpha\), \(h>H\), \(m=qh<N\) squarefree, \((q,N)=1\), and exact weight
\[
 -\Lambda(n)\mu(h)\log h,\qquad n=N-m.
\]
Keep the original cutoffs and any additional \(m\)-only masks, including a fixed \(\mu(m)\) parity. Any proper prime-power terms in \(n\) have total absolute cost \(N^{1/2+o(1)}\) by the divisor bound, so the prime estimates below may use actual \(n\) prime and hence \(m\) odd. [Pinned raw outer rows and exact moving cutoff](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0).

Let \(0<\sigma<1\), \((1+\sigma)/2<\theta<1\), \(Z_{\rm low}=\exp(L^\sigma)\), and \(Z_{\rm high}=\exp(L^\theta)\). For any fixed integer \(j\ge1\), the complete signed contribution of this unmatched row on
\[
 \#\{p\mid m:p\le Z_{\rm high}\}=j,\qquad
 P^-(m)\le Z_{\rm low}
 \tag{1}
\]
is \(o(N)\) at each fixed target. In particular it is \(o(N)\) when exactly one or two primes are at most \(Z_{\rm high}\) and at least one is at most \(Z_{\rm low}\). In the two-prime case the second prime may lie anywhere up to \(Z_{\rm high}\). This slices the original raw row by \(m\) and keeps all its admitted placements on each selected endpoint.

## Exact allocation groups

Fix a squarefree odd \(m\), two distinct marked primes \(p<r\) of \(m\), and \(a\mid m/(pr)\). Put \(b=m/(apr)\). The four underlying allocations are
\[
 (q,h)=(a v,\ bpr/v),\qquad v=1,p,r,pr.
\]
All arithmetic weights except \(\mu(h)\log h\) are fixed. The sign outside that factor is the original one. The log is affine in the two independent prime allocations, and \(\mu(h)=\mu(b)\mu(v)\). Thus the four weights sum to zero whenever all four allocations satisfy the original interval tests. A partially admitted group can contribute only when an admitted \(q\) belongs to at least one of
\[
 [Q,Qpr),\qquad(\alpha/(pr),\alpha],\qquad[m/(Hpr),m/H).
\]
Indeed the smallest \(a\) may fail the lower cut, or the largest \(a pr\) may fail the upper \(q\) cut or the strict \(h>H\) cut. The four allocations share both products, their signs on \(n\), and all \(m\)-only masks. No primality test is moved to a different target.

For the asymptotic charge, take the original fixed \(K_0>3\), and fix \(B_0\in(3,K_0)\). Remove \(m<N/L^{B_0}\) in absolute weight \(O(N/L^{B_0-3})\), using the fixed product \(m\), \(\Lambda(n)\log h\ll L^2\), and \(\sum_{m\le x}\tau(m)\ll x\log(2x)\). Now \(h=m/q\ge H L^{K_0-B_0}>H\) for all allocations in \(Q\le q\le\alpha\). Thus the third possible edge disappears under this trim. Since \(\log(\alpha/Q)\asymp L\), a marked orbit with \(\log(pr)\le 2L^\theta=o(L)\) can meet at most one of these edges.

For one marked prime \(p\) the two allocations are \(q=a,h=bp\) and \(q=ap,h=b\). If both are admitted, their total weight apart from \(\Lambda(n)\) is \(\mu(b)\log p\). If only one is admitted, its magnitude is at most \(L\), and the underlying \(a\) belongs to an interval of log width \(\log p\) at \(Q\) or \(\alpha\).

For two marks \(p<r\), order the divisors \(v\) as \(1,p,r,pr\). At each outer \(q\)-edge, the four choices form a prefix or suffix. The ranges of \(a\) with one or three admitted choices have total log width at most \(2\log p\) at each edge and weight at most \(L\) apart from \(\Lambda(n)\). In the three-term case this follows by subtracting the missing term from the exact zero. The middle range has log width \(\log(r/p)\) and retains two adjacent choices differing by \(p\), with combined magnitude \(\log p\). Specifically at the lower edge the log-widths of \([Q/(pr),Q/r),[Q/r,Q/p),[Q/p,Q)\) are \(\log p,\log(r/p),\log p\). The upper edge uses the same pattern with thresholds \(\alpha/(pr),\alpha/r,\alpha/p,\alpha\). Integers at endpoints follow the exact non-strict tests \(Q\le q\le\alpha\). In the middle two-choice ranges the exact signs depend on \(\mu(b)\); the argument below takes the absolute weight after grouping.

## A product sieve for the remaining boundary placements

For now take \(j=1\) or \(2\) and write \(v_0=p\) or \(pr\) for the product of the small marks, so \(m=v_0ab\). By (1), both \(a,b\) have no prime at most \(Z_{\rm high}\). In a dyadic range \(A<a\le2A\) that can meet an admitted term, one has \(A\gg N^{1/4}/Z_{\rm high}^{2}=N^{1/4-o(1)}\) and \(b\le N/(v_0A)\). At fixed \(v_0,A\), count the two rough factors \(a,b\) and \(n=N-v_0ab\) prime in this rectangle. Discard \(n\le N^\xi\), for a sufficiently small fixed \(\xi>0\), at cost \(N^{\xi+o(1)}\) by the same divisor bound.

At an odd sieve prime \(s\nmid v_0\), the bad conditions for \(s\le Z_{\rm high}\) are \(s\mid a\), \(s\mid b\), or \(s\mid N-v_0ab\). The third is disjoint from the first two since \(N\) is a power of two, and the bad density is \((3s-2)/s^2\). For \(Z_{\rm high}<s\le N^\xi\) keep only the prime test on \(n\), of bad density \((s-1)/s^2\). Omit 2 and the marked primes. The Euler survival product is \(O(1/(L(\log Z_{\rm high})^2))\), by Mertens and the local comparisons to \((1-1/s)^3\) and \((1-1/s)\), respectively. The at most two omitted odd primes cost a bounded factor. For the optimal Selberg square at level \(D=N^{1/50}\), the denominator retains a fixed fraction of its Euler product by Markov's inequality on the log product: its expected log is \(O(\xi L)\), so take \(\xi\) small relative to \(1/50\). On the actual support no sieve prime is present in the bad sets, so this square equals one. [Pinned diagonal Selberg identity](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md#the-weight-and-its-elementary-quadratic-identity).

For each opened square pair, the modulus \(c\le D^2\) has at most \(c\,3^{\omega(c)}\) allowed bad residue pairs. On each pair the rectangle lattice error is \(O((A+N/(v_0A))/c+1)\). Multiplying the residue count and summing the \(D^2\) square pairs costs \(N^{.79+o(1)}\) in total after the subpower enumeration of the marks, logarithmic weights and dyadic cells. Indeed \(A\le H\), \(N/(v_0A)\le N^{.75+o(1)}\), and the square-pair count is \(N^{.04}\). The positive main bound at fixed \(v_0,A\) is \(O(N/(v_0 L(\log Z_{\rm high})^2))\).

For one mark, the complete groups have log weight \(\log p\) over \(O(L)\) dyadic bands, while the edge groups have log weight at most \(L\) over \(O(1+\log p)\) bands. Use \(\Lambda(n)\le L\). Summing the two parts with \(\sum_{p\le Z_{\rm low}}(1+\log p)/p\ll1+\log Z_{\rm low}\) yields
\[
 O\!\left(N\frac{L(1+\log Z_{\rm low})}{(\log Z_{\rm high})^2}\right)
 =O(N L^{1+\sigma-2\theta}).
\]
For the two-mark full-weight edge parts, \(p\le Z_{\rm low}\), \(r\le Z_{\rm high}\). Thus \(\sum_{p<r}(1+\log p)/(pr)\ll(1+\log Z_{\rm low})(1+\log L)\) by separate weighted and unweighted prime bounds. The cost is \(O(N L^{1+\sigma-2\theta}(1+\log L))\). The middle parts have log weight \(\log p\) over \(O(1+\log r)\) bands. Their cost is \(O(N\log Z_{\rm low}/\log Z_{\rm high})=O(N L^{\sigma-\theta})\). Both exponents are negative by the chosen \(\sigma,\theta\).

For fixed \(j>2\), choose the two smallest among the \(j\) marks and fix the assignments of the other \(j-2\) prime factors to \(q,h\). The same cancellation applies after rescaling the two \(q\) thresholds by the fixed marked product on \(q\). Both free factors remain \(Z_{\rm high}\)-rough. The number of assignments is bounded in terms of \(j\), the marked product is subpower, and the extra reciprocal prime sums cost at most \(O((1+\log L)^{j-2})\). The same negative logarithmic powers still give \(o(N)\). This proves the claimed signed charge on (1).

The same method also allows an unrestricted positive number of primes below \(Z_{\rm low}\) when there is a gap above them. Assume \(0<\sigma<1/3\) and \((1+3\sigma)/2<\theta<1\). The unmatched signed row is \(o(N)\) on \(P^-(m)\le Z_{\rm low}\) and no prime factor in \((Z_{\rm low},Z_{\rm high}]\). To see this, fix \(\sigma<\rho<1\) and discard endpoints whose product of primes at most \(Z_{\rm low}\) exceeds \(\exp(L^\rho)\). Their number is \(O(N e^{-L^{\rho-\sigma}})\): the mean exponential moment of the logarithm of this product, divided by \(\log Z_{\rm low}\), is at most
\[
 \prod_{p\le Z_{\rm low}}\left(1+\frac{p^{1/\log Z_{\rm low}}-1}{p}\right)=O(1)
\]
by the positive divisor expansion and the weighted prime bound. Cauchy–Schwarz with \(\sum_{m\le N}\tau(m)^2\ll NL^3\) makes the discarded weight negligible. On the remaining endpoints the marked product and its number of exact assignments are subpower. The local sieve omission cost for all marked primes is at most \((1+\log L)^3\), by splitting their reciprocal sum at \(L^2\). For at least two primes, choose the two least and hold the other assignments fixed. Their total reciprocal cost, with their assignment multiplicities, is bounded by \(\prod_{p\le Z_{\rm low}}(1+2/p)\ll(\log Z_{\rm low})^2\). The full-weight edges therefore have main bound \(O(N L^{1+3\sigma-2\theta}(1+\log L)^3)\), using the two-mark inner weighted sum up to \(Z_{\rm low}\). The middle edges cost \(O(N L^{4\sigma-2\theta}(1+\log L)^3)\). Both are \(o(N)\), and the one-mark case was already covered. The rectangle power error is unchanged.

## An absolute near-\(H\) charge without factor selection

The same raw unmatched row with \(H<h\le H L^{K_0-1-\varepsilon}\), for fixed \(\varepsilon>0\), has absolute weight \(O_\varepsilon(N/L^\varepsilon+N^{1/2+o(1)})\). Discard even \(h\) and prime powers in \(n\) at the stated power cost. At fixed odd \(h\), the actual prime \(n=N-qh\) is in the reduced class \(N\bmod h\) in an interval of length at most \(\alpha h\); its logarithm is at most \(L\). Interval Brun–Titchmarsh with the larger interval of length \(\alpha h\) gives prime weight \(O(\alpha h/\varphi(h))\), since \(\log\alpha\asymp L\). Multiplying the remaining \(\log h\) and summing \(h/\varphi(h)\) up to \(H L^{K_0-1-\varepsilon}\), using its bounded mean, gives \(O(N/L^\varepsilon)\). [Montgomery–Vaughan interval Brun–Titchmarsh](https://doi.org/10.1112/S0025579300004708).

These bounds leave the signed unmatched row on rough \(m\) and on endpoints without the separated fixed small-prime profile in (1).
