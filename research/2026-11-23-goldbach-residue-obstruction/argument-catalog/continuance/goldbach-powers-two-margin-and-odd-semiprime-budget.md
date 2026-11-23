# A pointwise powers-of-two comparison and the full odd semiprime charge

This is a hand audit of the corrected moving-prefix comparison and a direct auxiliary upper-sieve bound on the original prime-tested odd-semiprime support. Fix \(N=2^k\), \(H=\sqrt N\), \(L=\log N\) and strict \(d>P=H^{21/20}\) in the determinant center. In the previously rebalanced band keep \(U=N^{1/100}\), \(V=N^{1/5}\), \(D_s=N^{23/500}\), \(z=N^{17/5000}\), and \(\ell w>N^{13/40}\). The auxiliary sieve below upper-bounds the original prime-tested sum. Its conclusion transfers to the net sum of all ratio ranges in the fixed rebalanced expansion by the pinned exact equality. [Rebalanced equality](https://github.com/Sodelin/Research-Commons/commit/3894f49a36cb7cc752bdf1002b8f465253d3fafe)

## Pointwise comparison and rows

Write \(m=N-n\), \(\alpha_0=H/L^{K_0}\) with \(K_0\) sufficiently large and fixed, and \(Q_0=N^{1/4}\). Define the signed low-modulus remainder
\[
 E_{\rm lo}(N)=\sum_{\substack{q<Q_0\\(q,N)=1}}
 \mu(q)\sum_{n<N-\alpha_0 q}\Lambda(n)\mu(N-n)
 \log\frac{q}{N-n}\left(\mathbf1_{q\mid N-n}-\frac1{\varphi(q)}\right).
\]
The \(q=1\) term cancels. The \(q=3\) term alone has weight
\((\mathbf1_{3\mid m}-1/2)\Lambda(n)\mu(m)\log(m/3)\)
on the original strict interval. This is a shifted Möbius correlation at the fixed target. [Moving cut and diagonal class](https://zenodo.org/records/21939906) · [Exact \(q=3\) crosswalk](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/rough-pair-row-crosswalk.md)

Let \(I_0=(0,H/2]\), \(I_1=(H/2,H]\), \(I_2=(H,\infty)\). For \(i,j\in\{0,1,2\}\), define the raw ordered actual contribution
\[
 A_{ij}(N)=-
 \sum_{\substack{q\in I_i,\ h\in I_j,\ q\ge Q_0,\ h>\alpha_0\\
                  qh<N,\ \mu^2(qh)=1,\ (q,N)=1}}
       \Lambda(N-qh)\mu(h)\log h .
\]
There are exactly seven noncentral cells, indexed by
\(\mathcal O=\{(0,0),(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)\}\). The \((2,2)\) cell is empty. This partition uses raw actual cells and therefore requires no credit from earlier charges whose source and companion straddle a cell. The exact moving-prefix comparison gives
\[
 \sum_{n<N}\Lambda(n)\Lambda(N-n)
   = M_0(N)+E_{\rm lo}(N)+\sum_{(i,j)\in\mathcal O}A_{ij}(N)
       + A_{11}(N)+o(N),
 \qquad
 M_0(N)=\mathfrak S(N)\left(N-\sum_{n<N}\Lambda(n)\mu(N-n)\right).
 \tag{1}
\]
Here is the audit of the ordinary and model terms.

* Huang–Li's underlying squarefree short-divisor expansion has \([b^2,d]\) with \(d\le\alpha_0\). Truncate \(b\) at \(B=L^C\). Using \((b,d)=g\), \(b=ga\), \(d=gc\), the reciprocal tail is \(O(L\sum_{ga>B}1/(g^2a^2))=O(L(1+\log B)/B)\). After the two logs and the elementary progression count, the tail is \(o(N)\) with \(C\) fixed large. Nonreduced classes have only powers of primes dividing \(N\) with logarithmic total and divisor-bound multiplicities. For the reduced error, the multiplicity at \(z=s^2r\), where \(s,r\) are coprime and squarefree, is at most \(2^{\omega(s)}\), hence \(\sum_z m(z)^2/z\ll L\). The crude progression error is \(O(NL/z)\) on this range. Cauchy–Schwarz and ordinary Bombieri–Vinogradov give an \(o(N)\) error since \(\alpha_0B^2\le H/L^{K_{\rm BV}}\) for sufficient \(K_0\). The Euler product in the proof of Huang–Li Lemma 3 reduces to its Lemma 2 at \(R=\alpha_0\), which has \(\log R\asymp L\). Thus the ordinary short contribution is \(\mathfrak S(N)N+o(N)\). [Huang–Li, Lemmas 1–3 and §3.1](https://arxiv.org/pdf/2005.03811v2)
* In the long model combine both logarithms before reversing the finite sums. At \(R=m/\alpha_0\) its kernel is \( -\sum_{q<R,(q,N)=1}\mu(q)\log(R/q)/\varphi(q)-(\log\alpha_0)\sum_{q<R,(q,N)=1}\mu(q)/\varphi(q)\). For \(m\ge N^{3/4}\), Huang–Li Lemma 1 gives \(-\mathfrak S(N)+o(1)\) uniformly, including at integer strict endpoints. The remaining \(m\) have crude total \(O(N^{3/4} L^3)\) by the reciprocal-totient sum. Thus the model equals \(-\mathfrak S(N)\sum\Lambda(n)\mu(m)+o(N)\). The portion of this model with \(q\ge Q_0\) is itself \(o(N)\): on reversal, the Goldston–Yıldırım reciprocal prefix in the same lemma bounds every partial sum on \([Q_0,R)\) by \(O(\exp(-c\sqrt L))\), and \(\log(q/m)\) has size and variation \(O(L)\). This is why only \(q<Q_0\) remains centered in (1). The argument is pointwise and has no Vaughan or Selberg parameters. [Moya §6 and strict cutoff](https://zenodo.org/records/21939906)

In \(A_{11}\), \(q\ne h\) by squarefreeness and \(n\ge\lfloor H\rfloor\). Restrict \(n\) to the squarefree \(Y\)-rough set \(Y=\exp(L^{.005})\) at cost \(O_\epsilon(N^{1/2+\epsilon})\) by prime-power counting. Then \(\Lambda(n)=\sum_{d\ell=n}\mu(d)\log\ell\). The pinned determinant proof with the product-count phases set to one gives \(o(N)\) on \(d\le P\). Completing the divisor bracket on \(n\) with a prime factor at most \(Z_1=\exp(L\sqrt{\log\log L}/\log L)\) and repeating the short estimate charges this composite part on \(d>P\). For the endpoint-parity twist on the retained rough support, \(\mu(n)\mu(d)=\mu(\ell)\) puts the signed variable at \(\ell<N/P<H\) and moves the log onto that coefficient. The count condition “no prime in \((Y,Z_1]\)” is included by the same finite count phases. Hence
\[
 A_{11}(N)=2\left(S_{\rm odd,sp}(N)+S_{\rm even,sp}(N)
               +C_{\ge4}(N)\right)+o(N).
 \tag{2}
\]
The two \(S\)'s are original semiprime sums with \(\mu(qh)=-1,+1\), respectively, and \(C_{\ge4}\) is the original signed sum on squarefree \(n\) of even factor count at least four. All three retain \(P^-(n)>Z_1\), \(d>P\) and their raw central support. Original count and mark removals can be inserted separately in their recorded disjoint order. They are unnecessary for the upper bound below. [Pinned complete divisor and parity argument with the count mask](https://github.com/Sodelin/Research-Commons/commit/5ea16bc7f76f066d04b5077764ec67c57cf715ab) · [Actual semiprime coefficient and cutoff](https://github.com/Sodelin/Research-Commons/commit/ef82e66f32ed05a21477543b6aa57c1b2bb6739a)

## A direct charge on the original odd semiprime row

Let \(\mathcal E\subseteq[0,19/40]\) be a fixed finite union of intervals in the variable \(x=(\log\ell)/L\). Restrict \(S_{\rm odd,sp}\) to this set and to any additional swap-invariant original mask. The strict \(d>P>H\) means the nonzero term has \(d\) the larger prime and \(\ell\) the smaller prime, with \(\ell<N/P=N^{19/40}\). Pair \(q,h\) and keep \(q<h\). The exact signed weight is \(\mu(h)\log(h/q)\log\ell\). The semiprime unit condition implies \(q,h\) are both odd at powers of two. Then the sum of the absolute paired weights, with its external factor two, is at most
\[
 N\left[J\Pi\int_{\mathcal E}\frac{dx}{c(x)}+o(1)\right],
 \qquad c(x)=\frac13-\frac1{1000}-\frac x2,
 \quad J=\frac38-\frac{\log2}2,\quad
 \Pi=\prod_{p>2}\left(1+\frac1{p(p-1)}\right).
 \tag{3}
\]

Fix \(\ell\) and take an auxiliary upper Selberg square in the variable \(d=(N-qh)/\ell\) at level \(D_\ell=N^{c(x)}\), supported on odd primes other than \(\ell\). It has coefficients \(|\lambda_a|\le1\) and \(\lambda_1=1\), by the pinned diagonal optimum; it equals one at a prime \(d>P>D_\ell\). The count may enlarge the region and drop the other masks after the exact paired absolute weight. Approximate \((\log(h/q))_+\) by a nonnegative upper grid on \((H/2,H]^2\), mesh \(H/L\). Its normalized integral is \(J+o(1)\). For each term of the opened square, with \(b=[a_1,a_2]\), the congruence is \(qh=N\bmod \ell b\). Put \(M=\ell b\), an odd composite unit modulus. Count directly at this modulus on each grid rectangle while keeping \(q,h\) odd. Substituting the odd progressions transforms it into a translated unit hyperbola modulo \(M\). The count has main term equal to one fourth of the rectangle area times \(\varphi(M)/M^2\), with error \(M^{1/2+o(1)}(1+H/M)\). This follows by separating full periods and completing the two partial intervals using the composite-modulus Kloosterman bound. For example the gcd factors are summed using divisors of \(M\) and the interval Fourier estimate \(\sum_{j\ne 0,\ r\mid j}|\widehat{\mathbf1}_I(j)|\ll (M/r)\log(2M)\); the full-period against a partial-period unit count has remainder \(O(\tau(M))\) per full period. [Pinned rectangular completion](https://github.com/Sodelin/Research-Commons/commit/909738e51f1ea4abe94c119276375481f85abc56) · [Estermann composite Kloosterman bound cited there](https://doi.org/10.1112/S0025579300002187)

Using \(\sum_{a_1,a_2\le D}[a_1,a_2]^{-1/2}\ll D\) (write \(a_1=gu,a_2=gv\) with \((u,v)=1\)) gives the total error at this \(\ell\), including the grid and logarithms, as
\[
 N^{o(1)}\big(\ell^{1/2} D_\ell^3+H\ell^{-1/2}D_\ell\big).
\]
The two displayed terms are respectively \(N^{1-3/1000}/\ell\) and \(N^{5/6-1/1000}/\ell\). Summing over \(\ell\) costs only a reciprocal harmonic factor and is power-saving.

The local dimension-one density is \(g(p)=(p-1)/p^2\) at the odd primes being sifted. The optimal reciprocal quadratic norm equals \(G_\ell^{-1}\), with \(G_\ell=\sum_{a\le D_\ell,(a,2\ell)=1,\ a\ {\rm sf}} \prod_{p\mid a}g(p)/(1-g(p))\). Uniformly,
\[
 G_\ell=(1+o(1))\frac{\log D_\ell}{2\Pi}.
\]
Indeed the odd-prime Euler constant is \(\frac12\prod_{p>2}(1-1/p)/(1-g(p))=1/(2\Pi)\). Convolution against \(1/n\) gives the asymptotic with bounded additive error, since the remaining local coefficients have absolutely convergent logarithmic moment. Omitting \(\ell>Z_1\) changes the constant by \(1+O(1/\ell)\) uniformly. The factor \(1/2\) in \(G_\ell\) reflects omission of 2 from the sieve. The actual odd progression density \(1/4\) stays in the rectangle count. Thus the doubled main bound, after reinstating \(\log\ell\), is
\[
 N(J\Pi+o(1))\sum_\ell\frac{\log\ell}{\ell\log D_\ell}.
\]
The prime number theorem in its harmonic form makes this reciprocal sum tend to \(\int_{\mathcal E}dx/c(x)\). It still gives the upper integral starting at zero when the actual lower cutoff on \(\ell\) moves with \(N\), by including all smaller primes in this positive upper sum. [Pinned one-dimensional Selberg diagonal and local factors](https://github.com/Sodelin/Research-Commons/commit/b8d0afa3e5fab3380f662ce172eacad56ea05316)

For the exact constant check put \(A=997/3000\). The three integrals for the full range, the band \((1/10,1/8]\), and its complement are \(2\log r\), with
\[
 r=\frac{1994}{569},\qquad \frac{1694}{1619},\qquad \frac{1614143}{481943},
\]
respectively. Since \(J<57/2000\) and \(\Pi<34/25\), let \(v=(r-1)/(r+1)\) and use
\[
 2\log r\le 4\left(v+\frac{v^3}{3}+\frac{v^5}{5(1-v^2)}\right).
\]
The corresponding rational upper bounds for the coefficients in (3) are \(0.097467303\), \(0.003510410\), and \(0.093902394\) when rounded upward. For sufficiently large powers of two, the doubled charges are therefore strictly below \(0.098N,\ 0.004N,\ 0.094N\), respectively. The off-band charge applies solely to the complement of the displayed prime-\(\ell\) interval. The full charge includes any atypical remainder inside that interval.

## Implications for the requested fixed budget

In the exact rebalanced prime-tested band use \(\delta_0=1/380\) in the original notation \(D_0=H^{20/19-\delta_0}\), so \(D_0=P\). The original band endpoints \(\ell>N^{1/10}\), \(d>P\) automatically satisfy \(P^-(n)>Z_1\) for large \(N\). The arithmetic surrogate inside the rebalanced Type II expansion retains its pinned \(Y\)-roughness. The prime-tested equality does not require an extra \(Z_1\) mask on that surrogate. The full rebalanced signed band, combining all its ratio rows at its own fixed weights, has absolute value after doubling below \(0.004N+o(N)\) by (3) and the exact equivalence. At the global scale the whole original odd-semiprime charge \(0.098N\) already includes this band. Using that charge, a sufficient same-target lower bound is
\[
 E_{\rm lo}(N)+\sum_{(i,j)\in\mathcal O}A_{ij}(N)
       +2S_{\rm even,sp}(N)+2C_{\ge4}(N)
 \ \ge\ -M_0(N)+(0.098+\eta)N
 \tag{4}
\]
for some fixed \(\eta>0\) on all sufficiently large powers of two. The remaining rows in (4) retain their original arithmetic weights. They are not estimated by the positive Type II strip cap. In particular even-\(qh\) reflection retains a logarithm of size \(L\), so (3)'s bounded log-ratio weight is unavailable there. The four-or-more-prime term comprises its graph and triple sectors, the seven outer entries are the actual cells in (1), and the low entry stays centered. Each still needs a compatible signed bound, individually or jointly. The hand proof and exact rational constant checks do not give a numerical evaluation at any finite \(N\) or a Lean verification.

## A short-cofactor part of the raw outer rows

One can remove the subrange \(\alpha_0<h\le H/L^{B_0}\) of each raw \(A_{i0}\) with error \(O_A(N/L^A)\) if \(K_0>B_0\) are chosen sufficiently large for the desired saving. In particular \(q>H L^{B_0}\) forces such a cofactor and costs \(O_A(N/L^A)\) in \(A_{20}\). This uses ordinary Bombieri–Vinogradov and retains the fixed window tests on \(q\); it has no dependence on the rebalanced Selberg square. A hand derivation follows for the raw cells in (1).

For fixed squarefree odd \(h\), expand \(\mu^2(q)\) and the coprimality with \(h\) as
\(\sum_{b^2\mid q}\mu(b)\sum_{c\mid(q,h)}\mu(c)\), with \(b,c\) odd. Absorb oddness of \(q\) by excluding the even inputs \(n\) from the prime-weighted sum at a negligible logarithmic cost from powers of two and divisor multiplicities. Truncate both indices at \(B=L^T\), \(T\) sufficiently large. The absolute actual tail divided by \(NL^3\) is bounded by a constant times \(\sum_{b,c}1/(c[b^2,c])\) over \(b>B\) or \(c>B\): for each surviving congruence the possible \(q\)'s are positive multiples of \([b^2,c]\) up to \(N/h\), and \(\sum_{h\le H,c\mid h}1/h\ll L/c\). On writing \(b=ga,c=ge\) with \(g=(b,c)\), the reciprocal is \(1/(g^3a^2e^2)\), so the tail is \(O(B^{-1})\). The truncated modulus in the \(n\) progression is \(j=h[b^2,c]\le H L^{3T-B_0}\), and its interval comes from the exact \(q\)-window with the original \(q\ge Q_0,\,qh<N\). For each prime, multiplicities of the exponents \(1,2,3\) in \(j\) are at most \(1,2,2\), respectively, from the possible squarefree local data of \(h,b,c\) with \(c\mid h\). Hence the squared multiplicity divided by \(j\) sums to \(O(L)\). Cauchy–Schwarz with the trivial error \(O(NL/j)\) and ordinary maximal-prefix Bombieri–Vinogradov gives the asserted log savings as \(B_0\) is increased in terms of \(T,A\).

In the model the truncation in \(b,c\) can again be dropped with arbitrary log savings. Indeed \(\sum_{h\le H,c\mid h}1/\varphi(h[b^2,c])\ll L/(\varphi(c)\varphi([b^2,c]))\), using \(\varphi(xy)\ge\varphi(x)\varphi(y)\). The sum of these latter reciprocal terms over \(b,c\) is absolutely convergent even with a small fixed positive moment in \(\max(b,c)\), by the same \(g,a,e\) separation. At a prime \(p\mid h\), inside its baseline local \(1/\varphi(p)\), the choices \((p\mid b,p\mid c)\) give \(1-1/p-1/p^2+1/p^2=1-1/p\). Thus the resulting model factor for \(h\) is
\[
 \frac1h\prod_{\substack{p>2\\p\nmid h}}\left(1-\frac1{p(p-1)}\right).
\]
The model interval length as a function of \(h\) is bounded by \(N\) with variation \(O(N)\), by taking the difference of two clipped \(q\)-window endpoints times \(h\). The remaining Möbius coefficient is \(\mu(h)\) on odd \(h\), multiplied by \(\prod_{p\mid h}(1-1/[p(p-1)])^{-1}\). Its convolution with the inverse of \(\mu\) has absolute reciprocal norm at exponent \(1/2\), since the corrective coefficient on every positive power of an odd prime is \(O(p^{-2})\), and the factors at 2 are a geometric series. Splitting the convolution at \(\sqrt h\) and using the classical Möbius prefix log saving gives arbitrary logarithmic savings uniformly for prefixes at \(h\ge \alpha_0\). Partial summation against the interval length times \((\log h)/h\) proves the bound. The signed interiors of the seven raw \(A_{ij}\) outside these short-cofactor charges remain in (4).


By the separate all-square-lanes estimate, \(M_0(2^k)\ge 0.330N\) for sufficiently large \(k\). Thus (4) follows from the concrete joint lower allowance \(-\bigl(0.232-\eta\bigr)N\) on the remaining rows, after the short-cofactor charges. This uses the same original-model decomposition and the exact rebalanced band equality. [Pinned margin evaluation](https://github.com/Sodelin/Research-Commons/commit/d9ac2acb4650d202d5cd84c3604a62655a6c037d)
