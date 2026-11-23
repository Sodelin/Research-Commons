# Exact cancellations and a sieve charge in the four-prime Goldbach center

**Unconditional hand proof at each fixed power of two.** Keep the full admitted-divisor bracket of the original square-root center, its unmodified \(m=qh\) masks and both block parities. Write \(N=2^k\), \(H=\sqrt N\), \(L=\log N\), \(P=H^{21/20}\), \(n=N-qh\), and \(X=n/P\). Both products are squarefree, \((m,N)=1\), and the retained \(n\) has \(P^-(n)>Z_1=\exp(L\sqrt{\log\log L}/\log L)\). The strict admission test is \(\ell<X\), equivalently \(d=n/\ell>P\). Define
\[
 B(n)=-\sum_{\substack{\ell\mid n\\\ell<X}}\mu(\ell)\log\ell .
\]
On an even-factor endpoint, the paired contribution at \(H/2<q<h\le H\) is \(\mu(h)c_\epsilon(q,h)B(n)\), where \(c_{-1}=\log(h/q)\), \(c_{+1}=\log(qh)\) and \(\epsilon=\mu(m)\). These are the original signs. [Pinned powers-of-two ledger and retained center](https://github.com/Sodelin/Research-Commons/blob/36624845444790787f442157309e7f9ba6644ad0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-powers-two-margin-and-odd-semiprime-budget.md) · [Pinned full-bracket grouping](https://github.com/Sodelin/Research-Commons/blob/bfd3f2d1281fe76fa8541279a7aef3e4949e051e/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/2026-11-23-codex-triple-complement-balance-2225z/README.md).

## Exact graph on four-prime endpoints

First trim \(n<N/L^B\) at arbitrary logarithmic saving, with large fixed \(B\), using Cauchy–Schwarz and the fixed divisor moments for \(\tau(n)\tau(N-n)\). At any endpoint with at least four prime factors, if its largest prime exceeds \(P\), every admitted divisor is a divisor of the product of the remaining primes, and every such divisor is admitted. This follows from \(P>H\ge X\) and \(n/P^+(n)<X\). There are at least two remaining primes, so the complete Möbius logarithmic sum is zero and \(B(n)=0\). Also, if at least two endpoint primes are \(\ge X\), their complementary product is at most \(P^2/n<X\) on the trimmed range. Three primes \(\ge X\) would give \(n\ge X^3>N\) for large \(N\). With two such primes and at least four endpoint factors, the admitted divisors again form a complete group with at least two primes and \(B(n)=0\).

There is another exact completion whenever the largest prime \(R\) is not an admitted vertex, \(R\ge X\). Put \(M=n/R\) and \(T=P/R\). All admitted divisors lie in \(M\), and replacing \(\ell\) by \(M/a\) gives
\[
 B(n)=-\mu(M)\sum_{\substack{a\mid M\\a>T}}\mu(a)\log(M/a)
      =\mu(M)\sum_{\substack{a\mid M\\a\le T}}\mu(a)\log(M/a).
\]
The second equality completes the divisor sum on \(M\), which has at least three distinct primes. On even \(\Omega(n)\) its prefactor is \(-1\). If \(T\ge1\), put \(S=\prod_{p\mid M,\ p\le T}p\). When \(S\le T\), the last sum contains all divisors of \(S\). It equals \(-\log M\) after the prefactor if \(S=1\), equals \(-\log S\) if \(S\) is prime, and vanishes if \(S\) has two or more prime factors. The vanishing case can hold with just one nonvertex and six or more endpoint primes. It requires the full admitted bracket.

Now write \(n=p_1p_2p_3p_4\) with increasing primes. The remaining case has \(p_4\le P\), hence any admitted divisor has at most two prime factors, since an admitted triple would have complementary singleton \(>P\). The admitted vertices are the primes \(p_i<X\), and an edge joins \(p_i,p_j\) exactly when \(p_i p_j<X\). Two disjoint edges would give \(n<X^2<n\). Thus after complete-group removal there are three or four vertices, and every nonempty edge family is a star or a triangle. A nontrivial star can be based at \(p_1\): an edge among two larger primes forces the two corresponding edges to \(p_1\), making a triangle. A triangle uses the three least primes by the same monotonicity.

If there are three vertices, put \(M=n/p_4\) and \(t=P/p_4\). An edge between two of the three vertices is admitted exactly when the opposite vertex exceeds \(t\), by \(n/(\ell)>P\). At least one vertex exceeds \(t\): otherwise \(M\le t^3\le(P^2/n)^3\le N^{3/20}L^{3B}\), whereas \(M\ge N^{19/40}/L^B\). The three possible bracket values, indexed by the number of vertices greater than \(t\), are
\[
\begin{array}{c|ccc}
\#\{p_i>t:i\le3\}&1&2&3\\ \hline
B(n)&\log p_3&-\log p_1&-\log M .
\end{array}
\]
This follows by starting with the singleton sum \(\log M\) and subtracting the log of each admitted pair.

If there are four vertices, a star with zero, one, two or three edges gives respectively \(\log n,\ \log(p_3p_4),\ \log(p_4/p_1),\ -2\log p_1\). The triangle gives \(\log(p_4^2/n)<0\), since \(p_4<X\) and \(X^2<n\). These formulas include threshold equalities through the original strict tests. They isolate the signs at fixed \(n\) without presuming any cancellation across distinct additive complements.

## An absolute charge on a separated-large-prime factorization of \(q,h\)

Fix \(0<\sigma,\tau<1\) with \(\sigma+\tau<1\). Restrict paired placements to those with \(q=a\pi,\ h=b\varrho\), where \(\pi,\varrho\) are actual primes and \(a\le\exp(L^\sigma), b\le\exp(L^\tau)\). On the original \(\Omega(n)=4\) row, its full absolute paired weight, in either \(\mu(m)\) parity and with all original \(m\) masks, is
\[
 O\bigl(N L^{\sigma+\tau-1+o(1)}\bigr)=o(N).
 \tag{1}
\]
More generally (1) holds on any even-\(\Omega(n)\ge4\) row where the product \(A\) of the prime factors of \(n\) at most \(N^\eta\) satisfies \(A\le H\), for any fixed \(\eta>0\). The empty product \(A=1\) is allowed. For \(\Omega(n)=4\), after removing \(p_4>P\), one has \(p_3^3\ge n/p_4\ge N^{19/40}/L^B\). Taking \(\eta=1/10\), at most two primes of \(n\) enter \(A\), and \(A\le p_1p_2\le\sqrt n\le H\). Thus the general charge proves the four-prime statement.

To prove (1) fix \(a,b,A\). They are pairwise coprime as required by the original squarefree and unit conditions, in particular \((ab,A)=1\). The exact equation implies the unit rectangle congruence \(\pi\varrho=N\overline{ab}\bmod A\). Its rectangle area is \(O(N/(ab))\) and its two side lengths are at most \(H\). We upper-sieve the three tests that \(\pi,\varrho\) are prime and \(n/A\) is \(N^\eta\)-rough. At an odd sieve prime \(s\nmid abA\), the three bad conditions are \(\pi=0\), \(\varrho=0\), or \(ab\pi\varrho=N\bmod s\). The first two have union density \((2s-1)/s^2\), and the third has density \((s-1)/s^2\) and is disjoint from that union, since \(N\) is a power of two. The bad density is therefore \((3s-2)/s^2\), with survival \((1-1/s)(1-2/s)\).

Use the elementary optimal Selberg square with level \(D=N^{1/32}\), prime support \(s\le N^\xi\) for a sufficiently small fixed \(0<\xi<\eta\), omitting all primes of \(2abA\). The actual \(\pi,\varrho\) exceed the sieve primes for large \(N\); the third test has no such prime by the definition of \(A\). Thus the square equals one on the actual support. Its diagonal main term is at most \(O(L^{-3}(1+\log L)^3)\). In detail, the full product of survival factors up to \(N^\xi\) is \(O(L^{-3})\) by Mertens. Omitting primes dividing \(2abA\) costs at most \(O((1+\log L)^3)\), by separating at \(L^2\) and using \(\#\{p:p\mid2abA\}=O(L)\). The optimum denominator truncated at \(D\) contains a fixed fraction of its full Euler product: under its normalized independent law the mean log product is at most \(\sum_{s\le N^\xi}(3/s)\log s=O(\xi L)\), so take \(\xi\) sufficiently small relative to \(1/32\) and use Markov. The coefficients of the optimal square have absolute value at most one. [Pinned quadratic identity and denominator bound](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md#the-weight-and-its-elementary-quadratic-identity).

After opening the square at a squarefree modulus \(c=[d_1,d_2]\le D^2\), the bad residue pairs number at most \(c\,3^{\omega(c)}\). For each use the pinned unit hyperbola rectangle bound modulo \(A\) in the two translated progressions. The added period is coprime to \(A\). There are at most \(D^2\) square coefficient pairs. Thus the error at fixed \(a,b,A\) is \(O(D^4N^{o(1)}(A^{1/2}+H/A^{1/2}))\); this also covers \(A=1\) by the elementary interval rounding error. Summing over \(a,b\) of subpower size and \(A\le H\), with the eventual logarithmic weights, costs \(N^{7/8+o(1)}\), a power saving. The positive main term is bounded by
\[
 O\!\left(\frac{N(1+\log L)^3}{ab A L^3}\right),
\]
using \(\varphi(A)/A\le1\). The other exact support may be relaxed in this upper count. [Pinned unit-hyperbola rectangle bound](https://github.com/Sodelin/Research-Commons/blob/909738e51f1ea4abe94c119276375481f85abc56/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-balanced-two-prime-sieve.md#count-at-a-fixed-composite-modulus).

For the weights, \(|B(n)|\le L\tau(n)\), \(|c_\epsilon(q,h)|\le L\), and \(P^-(n)>Z_1\) implies \(\tau(n)\le2^{L/\log Z_1}=L^{o(1)}\). The reciprocal sums of \(a,b\) cost \(O(L^{\sigma+\tau})\). The reciprocal sum of all possible \(A\), whose primes are in \((Z_1,N^\eta]\), is at most \(\prod_{Z_1<s\le N^\eta}(1+1/s)\ll L/\log Z_1\), also \(L^{o(1)}\). Combine these bounds with the main term and the power error to prove (1). The external factor two in the powers-of-two ledger only doubles the same \(o(N)\) charge. The general even-endpoint bracket still includes placements outside the stated large-prime cofactor selection.

## A thin strip below the largest-prime cutoff

Without the \(q,h\) cofactor selection, let \(\Omega(n)=4\) and \((1-\eta)P\le p_4\le P\), \(0<\eta\le1/2\). For every fixed \(A_0>0\), its absolute paired charge, in either \(\mu(m)\) parity, is
\[
 O_{A_0}\!\left(N(\eta+L^{-A_0})L(1+\log\log L)^3
                    +N^{309/400+o(1)}\right).
 \tag{2}
\]
In fact the main term has the stronger bound \(O_{A_0}(N\eta(1+\log\log L)^2+N L^{1-A_0}(1+\log\log L)^3)\), with the same power error. Thus, for example, the strip of relative width \((1+\log\log L)^{-3}\) is \(o(N)\).

Put \(M=p_1p_2p_3=n/p_4\le 2N^{19/40}\) and \(X=M p_4/P\). The three small primes are vertices since each is at most \(M/Z_1^2<X\), while \(p_4\ge X\) because \(M<P\). Every pair of those three primes is admitted, since the opposite prime exceeds \(P/p_4\le2\). There is no admitted triple under \(p_4\le P\), so the exact full bracket here is \(B(n)=-\log M\).

At fixed \(M\), the product \(qh=N-Mp_4\) lies in an interval of length \(\eta M P\). Cover its part of the square-root block by intersecting grid rectangles of mesh \(H/K\), \(K=\lceil L^{A_0}\rceil\). Their union lies in the same product interval thickened by \(O(N/K)\), since the product varies by \(O(N/K)\) on each cell. At each \(q\ge H/2\), the allowed \(h\)-length is \(O((\eta M P+N/K)/H)\), so the total rectangle area is \(O(\eta M P+N/K)\). There are at most \(K^2\) rectangles.

Count the unit congruence \(qh=N\bmod M\) and apply the pinned auxiliary one-dimensional Selberg square of level \(D=N^{1/50}\) to \(p_4=(N-qh)/M\), omitting primes dividing \(M\). This prime exceeds the sieve level. Since \(M\) has just three prime factors, all \(>Z_1\), the omitted factors have uniformly bounded, in fact \(1+o(1)\), effect on the reciprocal sieve norm \(O(1/L)\). Opening at \(c=[a,b]\) gives the combined unit hyperbola modulo \(Mc_{\rm odd}\); if \(c\) is even use the three admissible parity pairs separately. Its error is \(N^{o(1)}((Mc)^{1/2}+H/(Mc)^{1/2})\). Summing over the square indices uses \(\sum_{a,b\le D}[a,b]^{1/2}\le D^3\) and \(\sum_{a,b\le D}[a,b]^{-1/2}\le D^{1+o(1)}\) by grouping their lcm. Over \(M\le 2N^{19/40}\), the first error has exponent \(57/80+3/50=309/400\), the second \(59/80+1/50=303/400\). The polylogarithmic grid, divisor multiplicities and absolute log weights fit in \(N^{o(1)}\). This uses the same combined-modulus count as the pinned narrow semiprime proof. [Pinned combined modulus and square-level calculation](https://github.com/Sodelin/Research-Commons/blob/c464e64722382a25eddbff67af0c017a8684eda9/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-rebalanced-type-ii-complement-rows.md#a-direct-upper-count-on-the-narrow-prime-tested-band).

For the main term, each \(M\) costs \(O(\eta P/L+N/(K M L))\) before weights. Its possible reciprocal mass is bounded by \((\sum_{Z_1<p\le N}1/p)^3\ll(1+\log\log L)^3\) by Mertens. Also for \(Y=2N^{19/40}\) the number of such \(M\le Y\) is \(O(Y(1+\log\log L)^2/L)\). To see this, fix the two least primes \(p_1,p_2\). Since \(p_1p_2\le M^{2/3}\), the upper bound \(Y/(p_1p_2)\) on the third prime is at least \(Y^{1/3}\). Chebyshev thus gives \(O(Y/(p_1p_2L))\) possible third primes. Sum the two prime harmonic factors. Multiplying both main terms by the exact paired weight bound \(L^2\) proves the stronger form of (2). The strict cutoff at \(p_4=P\) is retained, and the behavior above \(P\) is the separate complete-group zero.

The same moving strip can be charged for every even \(\Omega(n)\ge4\). For \((1-\eta)P\le p_{\max}\le P\) put \(M=n/p_{\max}\le Y\). Since \(M<P\), the largest prime cannot divide an admitted \(\ell\). Every proper divisor of \(M\) is at most \(M/Z_1<X\), whereas \(M\) itself fails the strict test. The complete logarithmic sum on \(M\) vanishes, and \(\mu(M)=-1\), so the exact bracket is again \(-\log M\). The same CRT and area calculation applies. Omitting all primes of \(M\) from the auxiliary square changes its main factor by \(1+o(1)\) uniformly, because \(P^-(M)>Z_1\) and \(\sum_{p\mid M}1/p\le L/(Z_1\log Z_1)=o(1)\). The elementary one-dimensional sieve gives \(\#\{M\le Y:P^-(M)>Z_1\}\ll Y/\log Z_1\). For instance, use the optimal square in the integer divisibility model \(g(p)=1/p\) up to \(Z_1\) with level \(N^{1/20}\). Markov captures a fixed fraction of the full denominator, since its mean log product is \(O(\log Z_1)=o(L)\), and opening the square has only \(O(N^{1/10})\) floor error. The reciprocal \(M\) mass is at most \(\prod_{Z_1<p\le N}(1+1/p)\ll L/\log Z_1\). With grid \(K=\lceil L^{A_0+1}\rceil\), the all-parity absolute charge for this general even endpoint strip is therefore
\[
 O_{A_0}\!\left(N(\eta+L^{-A_0})\frac L{\log Z_1}
                       +N^{309/400+o(1)}\right).
\]
It is \(o(N)\) for \(\eta=(\log L)^{-2}\). This keeps the complete admitted-divisor bracket.
