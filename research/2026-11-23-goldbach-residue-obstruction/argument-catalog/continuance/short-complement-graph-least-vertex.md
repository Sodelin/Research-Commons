# The short-complement graph with a subpolynomial least vertex

This gives an \(o(N)\) bound on an additional part of the exact graph in the peer even-endpoint center. It allows composite endpoints with more than two prime factors and allows individual graph vertices of polynomial size. The bound is a hand estimate at each fixed even \(N\). [Peer graph and its signed regrouping](https://github.com/Sodelin/Research-Commons/blob/b29f3312e/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#reflect-the-short-complement-graph-at-the-strict-cutoff).

Keep the same strict larger-divisor cutoff \(d>P\), with \(H=\sqrt N,\ P=H^a\), \(1<a<20/19\) fixed, and write \(X=n/P,\ n=N-qh\). Retain the original center masks, including \(n\) squarefree and \(Y\)-rough and the \(q,h\) swap symmetry. Discard \(n<N/L^B\) at arbitrary log savings by the pinned endpoint trim, with \(L=\log N\) and a sufficiently large fixed \(B\). Work on the graph with vertices \(p\mid n,\ p<X\) and edges \(pr<X\). Assume no product of three distinct primes dividing \(n\) is \(<X\).

For this graph, the sum \(\sum_{\ell\mid n,\,\ell<X}-\mu(\ell)\log\ell=I-J\), where \(I\) is the sum of \(\log p\) on isolated vertices and \(J\) is the sum of \((\deg(p)-1)\log p\) on vertices of degree at least two. Every admitted \(\ell>1\) is a prime or a product of two distinct primes. If the graph is empty the weight is zero. Otherwise let \(p_0\) denote its least vertex. The result is:

**On odd \(qh\), the entire reflected graph with \(p_0\le\exp(L^\sigma)\), \(0<\sigma<1\) fixed, has absolute orbit weight**
\[
 \ll N L^{\sigma-1}(1+\log L)^3+N^{.9+o(1)}+O_A(N/L^A)=o(N).
\]
In particular either adverse graph sign on this support is negligible. This applies inside the even-\(n\) row with no change to its signed budget.

## Polynomial sieve available on this graph

Choose a sufficiently small fixed \(c>0\) with \(3c<1-a/2\), and set \(z=N^c\). The endpoint trim implies \(X\ge N^{1-a/2}/L^B>z^3\) for large \(N\). Hence no-triple forces at most two primes \(\le z\) in \(n\), and therefore in any \(d=n/\ell\) on this graph. The previous polynomial sieve with at most two exceptions applies. Its consequence for any permitted set \(\mathcal L\subseteq[2,H]\) is that the number of placements weighted by \(\log\ell\) is bounded by
\[
 \ll \frac{N(1+\log L)^2}{L}
            \sum_{\ell\in\mathcal L}\frac{\log\ell}{\ell}
     +N^{.9+o(1)} .
\]
Here one writes \(d=Ab\) with \(A\) the product of its at most two primes \(\le z\), fixes \(A,\ell\), and sieves \(b\) modulo \(A\ell\). Choosing \(c\) small in the lattice error justifies the stated power error. The weight \(\log\ell\) here has no Möbius sign and never requires a parity assumption. [Polynomial sieve with exceptions](https://github.com/Sodelin/Research-Commons/blob/be190409fedb5f8c5de58bc2958d618dd1eb2821/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/polynomial-rough-large-divisor.md).

## Reduction of the graph weight to a short logarithmic band

Let \(V=\exp(L^\sigma)\). Every isolated prime other than \(p_0\) satisfies \(p_0 p\ge X\). Every edge \(pr<X\) with neither endpoint equal to \(p_0\) satisfies \(p_0pr\ge X\), by the no-triple condition. These isolated primes and edge products thus all lie in the single fixed band
\[
 \frac{N}{P L^B V}\le\ell<\frac NP .
\]
This band has log width at most \(B\log L+L^\sigma\) and upper endpoint \(<H\).

For \(p\ne p_0\), its degree minus one, if positive, is at most its number of edges not incident to \(p_0\). Summing the incidence weights charges at most \(\log(pr)\) to each such edge. The part at \(p_0\) costs at most \(O(\log p_0)\): there are only boundedly many vertices after the endpoint trim. Indeed at most two vertices are below \(X^{1/3}\), while the product bound \(n\le N\) bounds how many primes can be at least \(X^{1/3}\), since \(\log X\gg L\). Therefore
\[
 I+J\ll\log p_0+
 \sum_{\substack{p\ {\rm isolated}\\p\ne p_0}}\log p
 +\sum_{\substack{pr\ {\rm edge}\\p,r\ne p_0}}\log(pr).
\]
The first term is charged by \(\ell=p_0\), which is admitted with \(d>P\). In the other terms the charged \(\ell\)'s are admitted primes or semiprimes in the band. On odd \(qh\) the peer reflection leaves \(|\log(h/q)|\le\log2\), so it is enough to upper bound the displayed nonnegative charges. This argument deliberately bounds the absolute **grouped** weight, after reflection.

The reciprocal log sum on primes up to \(V\) is \(O(L^\sigma)\). For primes in any band \([A_0,B_0]\), it is \(O(1+\log(B_0/A_0))\), by Chebyshev on dyadic intervals. For squarefree semiprimes in that band, order \(p<r\), use \(\log(pr)\le2\log r\), and apply the same prime bound to the interval for \(r\) with \(p\) fixed. Summing \(1/p\) costs \(O(1+\log L)\). Hence the total reciprocal log sum for the three charges is \(O(L^\sigma(1+\log L))\). The polynomial sieve proves the result.

**Additional all-parity slices.** The no-triple graph condition gives at most two prime factors in each \(\ell>1\) and at most two exceptions to polynomial roughness in \(d\). Thus the middle-count tail estimate in the previous note applies to every graph vertex and edge product, even at polynomial scales. With the original parameters, \(k(qh)\le.26\log L\) and \(k(qh)\ge4\log L\) each give \(o(N)\) in the absolute original weight, with either \(qh\) parity. These extend the corresponding semiprime-endpoint estimates to the full no-triple graph. Outside those tails, the odd-\(qh\) bound above still removes the subpolynomial-least-vertex case. Graphs with all vertices polynomial in size, even \(qh\) in the central count region, and endpoints admitting triple complements remain open in general.


## A wider least-vertex range

The same conclusion holds for \(p_0\le V=N^{o(1)}\) whenever \(\log V=o(L/(1+\log L))\). The improvement comes from keeping \(p_0\) in the counting and charging the two small primes jointly.

For the charge \(\ell=p_0\), only one other prime \(\le z\) can remain in \(d\), so the polynomial-sieve main term is \(O(N\log(2V)(1+\log L)/L)\). For the other charges, fix \(p_0\). The band has log width at most \(W(p_0)=B\log L+\log p_0\). The charged \(\ell\) is not divisible by \(p_0\), so \(p_0\) belongs to \(A\) in the polynomial sieve. The band lies above \(z^2\) for sufficiently small fixed \(c\), since \(V=N^{o(1)}\). Thus a prime or semiprime \(\ell\) in the band has a prime \(r>z\). Use the marked \(r\) to pay for \(\log\ell\) and sum \(\log r/r\) in its band, at cost \(O(1+W(p_0))\). If \(\ell\) has another prime factor above \(z\), its unmarked reciprocal cost is \(O_c(1)\) by Mertens between \(z\) and \(N\). Across \(A/p_0\) and \(\ell\), at most one further prime \(\le z\) is available, at cost \(O(1+\log L)\). Hence the main term for fixed \(p_0\) is bounded by \(N(1+W(p_0))(1+\log L)/(p_0 L)\). Summing over \(p_0\le V\) gives
\[
 O\!\left(\frac N L\left[\log(2V)(1+\log L)+(1+\log L)^3\right]\right).
\]
The power-error bound is unchanged: every counted \(A,\ell\) determines at most two possibilities for the marked \(p_0\) dividing \(A\). This proves the wider range, including \(V=\exp(L/(\log L)^{1+\epsilon})\) for each fixed \(\epsilon>0\).
