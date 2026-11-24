# Exact outer pairing and rough paired estimates at powers of two

Let \(N=2^k\), \(L=log N\), \(H=\sqrt N\), \(Q=N^{1/4}\), and \(\alpha=H/L^{K_0}\), with fixed \(K_0>3\) as in the moving cutoff. For all sufficiently large \(N\), \(Q<\alpha<H/2\). The original raw rows have \(q\ge Q\), \(q\) odd, \(h>\alpha\), \(qh<N\), bin cutoffs \(H/2,H\) in both variables, and weight \(-\Lambda(N-qh)\mu(q)\mu(qh)\log h\). Exclude the central cell \(A_{11}\) throughout. Off the original squarefree support the summand vanishes. If \(N-qh=2^j\) with \(j\ge2\), then \(4\mid qh\), so it also vanishes. The remaining \(N-qh=2\) costs \(N^{o(1)}\) by the divisor bound. At every odd prime-power endpoint both \(q,h\) are odd. [Pinned pointwise ledger](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0)

## Exact decomposition and the two unmatched small-product cells

Apart from the even endpoint just isolated, the entire seven-row sum is the combination of the following disjoint supports.

- For \(Q\le q\le\alpha<h\), keep the original orientation and weight. Its transpose is absent because its new cofactor would be \(h'=q\le\alpha\). These are the unmatched parts of \(A_{00},A_{01},A_{02}\).
- On \(q<h\) with both variables greater than \(\alpha\), keep the original full paired weight
\[
 -\Lambda(N-qh)\bigl(\mu(h)\log h+\mu(q)\log q\bigr).
\tag{1}
\]
Exclude those pairs with both factors in \((H/2,H]\). This pairs \(A_{00}\) with itself, \(A_{01}\) with \(A_{10}\), \(A_{02}\) with \(A_{20}\), and \(A_{12}\) with \(A_{21}\). The diagonal would make \(qh\) nonsquarefree, and \(A_{22}\) is empty. Equality at the moving threshold stays on the unmatched side, as required by the original strict cutoff on \(h\).

The unmatched parts of \(A_{00},A_{01}\) have \(h\le H\) and hence \(m=qh\le \alpha H=N/L^{K_0}\). More generally any selected raw terms with \(m\le X\) have absolute weight at most
\[
 L^2\sum_{m\le X}\tau(m)\ll L^2 X(1+\log X).
\]
All of these two unmatched cells therefore cost \(O(N/L^{K_0-3})=o(N)\). The earlier capped unmatched \(A_{02}\) terms are separate from these two cells and from every paired estimate below.

## Rough paired rows

For (1) on \(\mu(qh)=-1\), the magnitude is \(\Lambda(N-qh)\log(h/q)\), where \(h/q\le N/\alpha^2=L^{2K_0}\). On \(\mu(qh)=+1\), use the magnitude \(\Lambda(N-qh)\log(qh)\). Thus, for \(3\le Y\le N\), the following pointwise bounds hold as \(N\to\infty\), with fixed \(K_0\):
\[
\begin{array}{ll}
\mu(qh)=-1,\ \max(P^-(q),P^-(h))>Y:
 &O\!\left(\dfrac{N(1+\log L)^2}{\log Y}\right)+o(N),\\[4pt]
\min(P^-(q),P^-(h))>Y,\ \log Y/\log L\to\infty:
 &O\!\left(\dfrac{N L(1+\log L)}{(\log Y)^2}\right)+o(N).
\end{array}
\tag{2}
\]
Both bounds are on the sum of absolute paired weights with the stated masks. In particular \(Y=\exp((\log L)^3)\) suffices for the first to be \(o(N)\), and \(Y=\exp(L^{3/4})\) suffices for the second, which allows both parities.

Fix the other factor \(a\) when the variable \(t\) is \(Y\)-rough, so \(q,h\) have become \(a,t\) in either order. Their original bounds imply \(a\in(\alpha,N/\alpha)\) and \(at<N\). Discard proper prime powers and \(N-at\le N^{.26}\) at total cost \(N^{1/2+o(1)}\), using the number of endpoints and the divisor bound. For fixed \(a\), use an upper Selberg square on odd \(t\), of level \(D_a=\lfloor N^{.499}/\sqrt a\rfloor\), for the two forms \(t,N-at\). Only the first form is sifted through \(Y\). More precisely take primes up to \(W=D_a^c\) for the second form, with sufficiently small fixed \(c>0\), and primes up to \(W_1=\min(Y,W)\) for the first. All retained inputs pass these tests, since \(D_a<N^{.26}\) and \(P^-(t)>Y\).

For odd \(p\nmid a\), the forbidden density is \(2/p\) up to \(W_1\) and \(1/p\) above \(W_1\) through \(W\). If \(p\mid a\) the second form has no forbidden residue, because \(N\) is a power of two, so the density decreases to \(1/p\) or 0, respectively. With \(\kappa(a)=\prod_{p\mid a}(p-1)/(p-2)\), this loss reduces the diagonal Euler product by at most \(\kappa(a)\). The unrestricted Euler mass is \(\gg (\log W)(\log W_1)/\kappa(a)\) by Mertens, and the normalized mean of the logarithm of its index is at most \(2\sum_{p\le W}\log p/p=O(c\log D_a)\). With \(c\) small, Markov leaves at least half the mass at indices at most \(D_a\). Since \(\log D_a\asymp L\) uniformly, the diagonal mass is \(\gg L\log Y/\kappa(a)\). The usual upper Selberg square with \(|\lambda_b|\le1\) and the Chinese remainder theorem therefore give the count
\[
O\!\left(\frac{N\kappa(a)}{a L\log Y}\right)+D_a^2N^{o(1)}.
\tag{3}
\]
The factor \(N/a\) is an upper bound for the exact variable interval and may enlarge it for this positive count. The error follows by counting at most \(2^{\omega([b_1,b_2])}\) residue classes per pair of sieve indices. Even after multiplying by \(L^2\), the sum of errors over \(a\) is \(o(N)\), since \(D_a^2\le N^{.998}/a\). [Pinned diagonal argument](https://github.com/Sodelin/Research-Commons/commit/b8d0afa3e5fab3380f662ce172eacad56ea05316)

In any multiplicative interval \((A,B)\) with \(A\ge1\), one has \(\sum_{A<a<B}\kappa(a)/a\ll1+\log(B/A)\) for odd \(a\). Expand \(\kappa(a)=\sum_{d\mid a}c(d)\), with \(c\) supported on squarefree odd indices and \(c(p)=1/(p-2)\). Its weighted sum \(\sum c(d)/d\) converges absolutely. In the inner harmonic interval, when \(d\le A\), its multiplicative ratio is \(B/A\). If \(d>A\), its upper endpoint is at most \(B/A\). This proves the bound. For the first line of (2), apply it on \((\alpha,N/\alpha)\), giving \(O(1+\log L)\), and weigh (3) by \(O(L(1+\log L))\).

For the second line, the fixed \(a\) is also \(Y\)-rough and \(\kappa(a)=1+o(1)\) uniformly, since \(a\le N\) and \(\sum_{p\mid a}1/p\le L/(Y\log Y)\). A dimension-one upper square for \(Y\)-rough integers in each dyadic interval \((x,2x]\), using level \(N^{1/20}\) and primes up to the smaller of \(Y\) and a small fixed power of that level, bounds their count by \(O(x/\log Y)+N^{1/10+o(1)}\). The same Euler mass and Markov calculation gives this dimension-one diagonal, and there is one forbidden residue per odd prime. Summing reciprocal weight over the \(O(1+\log L)\) dyadic intervals covering \((\alpha,N/\alpha)\), with \(x\gg N^{1/2}/L^{K_0}\), yields \(O((1+\log L)/\log Y)\) up to a negligible error. Multiplying (3) by \(L^2\) proves the second line of (2).

For a fixed \(C\ge1\), on the bounded box \(q,h\le CH\) the odd-parity estimate with at least one rough factor improves to \(O_C(N/\log Y)+o(N)\). At fixed \(a\), open the same square on each dyadic \(t\)-interval below \(CH\), retaining its actual interval length in the main term. Bound \(\log(\max(a,t)/\min(a,t))\) by \(\log(CH/a)+\log(CH/t)\). The sum of the weighted lengths of those intervals is \(O_C(H(1+\log(CH/a)))\), since the dyadic widths decay geometrically. The floors lose at most powers of \(1+\log L\), still negligible with the original \(D_a\). Summing over \(a\) uses \(\sum_{a\le CH}\kappa(a)(1+\log(CH/a))\ll_C H\), by the same convergent divisor expansion and \(\sum_{b\le X}(1+\log(X/b))\ll X\). In this bounded box, the both-rough estimate similarly improves to \(O_C(NL/(\log Y)^2)+o(N)\) under the same condition on \(Y\), by applying the one-dimensional upper sieve for \(a\) on the whole interval of length \(CH\). For \(C=2\), the box includes all outer paired cells except the long-variable portion of \(A_{02}+A_{20}\) above \(2H\).

## Endpoint groups with a prime exceeding \(H\)

If squarefree \(m=qh=av\) has a prime \(v>H\), that prime is unique. In the paired region the short variable is a divisor \(d\mid a\) with \(d>\alpha\), and the long one is \(v(a/d)\). Thus \(\alpha<a<H\), and the pair can only be in \(A_{02}+A_{20}\) or \(A_{12}+A_{21}\). The strict cutoff is now \(e=a/d<R=a/\alpha\). For \(\mu(a)=+1\), hence \(\mu(m)=-1\), the sum of all absolute paired contributions with this large prime is
\[
 O\!\left(\frac{N(1+\log L)^3}{L}\right)+o(N)=o(N).
\tag{4}
\]
Indeed the paired log ratio is \(O(1+\log L)\). Fix \(a\) and sieve \(v,N-av\) as in (3), now using primality of \(v\) through the full auxiliary level, giving \(O(N\kappa(a)/(aL^2))+D_a^2N^{o(1)}\). When summing over \(a\), the number of short divisors is at most \(\sum_{e\mid a,\ e<L^{K_0}}1\). For each such \(e\), write \(a=eb\) and use \(\kappa(eb)\le\kappa(e)\kappa(b)\). The reciprocal sum over \(b\) in \((\alpha/e,H/e)\) is \(O(1+\log L)\) by the interval bound above, and \(\sum_{e<L^{K_0}}\kappa(e)/e=O(1+\log L)\). Weighing the count by \(O(L(1+\log L))\) proves (4). Divisor multiplicity in the sieve errors costs only \(N^{o(1)}\).

If \(\mu(a)=-1\), the paired group instead equals exactly
\[
\Lambda(N-av)\log(av)\sum_{\substack{e\mid a\\e<R}}\mu(e).
\]
Let \(r\) be the product of all primes of \(a\) strictly below \(R\). If \(r<R\), the sum comprises every divisor of \(r\), and the group is favorable for \(r=1\) and zero otherwise. The other \(\mu(a)=-1\) endpoint groups are not bounded here unless they also meet one of the rough paired criteria above.

## Complete allocations of small primes within the paired outer region

For another exact cancellation, write odd squarefree \(m=suv\), where \(s\) is the product of the prime factors of \(m\) at most a chosen \(Y\) and \(u,v\) are unordered coprime factors of the remaining rough part. Require \(u,v>\alpha\) and require that every \((ub,v(s/b))\) for \(b\mid s\) is outside the central square. The latter holds, for example, if \(m\le N/4\), if \(\max(u,v)>H\), or if \(s\min(u,v)\le H/2\). Every assignment then belongs to (1) in its unique unordered orientation. At fixed \(m,u,v\), the sum of (1) over all \(b\mid s\) is zero for \(\omega(s)\ge2\), since both the unweighted and log-weighted divisor Möbius sums vanish. If \(s=p\) is a prime, the whole group is \((\mu(u)+\mu(v))\Lambda(N-m)\log p\). For \(\mu(m)=+1\), \(\mu(u)=-\mu(v)\) in this last case, so all these complete groups with \(s>1\) vanish exactly. The group condition on the central square is needed to avoid mixing an outer estimate with an already charged central support.

The immediate ledger reduction is two entire unmatched outer cells at \(o(N)\), the paired slices in (2) and (4), and the listed exact nonnegative or zero groups. These can be used on their union without summing the same raw weight twice. The unmatched \(A_{02}\) still keeps its previous charge on its own masks, and generic paired rows of either parity still need a signed estimate. These are hand proofs at fixed targets, with no Lean verification or average over \(N\).
