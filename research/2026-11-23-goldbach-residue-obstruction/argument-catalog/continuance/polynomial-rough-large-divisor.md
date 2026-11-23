# Polynomial roughness on the large divisor in the Goldbach center

A hand upper bound on the original fixed-\(N\) long-divisor support. This gives a new slice of the even-endpoint center, including semiprime endpoints, with no roughness or largest-prime assumption on \(q,h\).

Keep the original square-root block, middle count, coprimality, and any further product masks defining the surviving center, with \(m=qh\) squarefree, \((m,N)=1\), and \(n=d\ell=N-m\) squarefree and \(Y\)-rough. Let \(H=\sqrt N,\ L=\log N\). Impose \(d>H\) and the additional condition that \(d\) has no prime divisor at most \(z=N^c\), for a sufficiently small fixed \(c>0\). On the original \(d\) orientation this permits composite \(d\), and a prime \(d>H\) meets the condition automatically. For fixed \(\ell\le H\), the count of \(q,h\) before weights is
\[
 \ll \frac{N}{\ell L}
 +N^{3/100+o(1)}\ell^{1/2}(1+H/\ell).
 \tag{1}
\]
All estimates are pointwise in the even target \(N\).

Indeed \(n\)-coprimality gives \((\ell,N)=1\). For an auxiliary squarefree modulus \(e\) supported on primes at most \(z\) coprime to \(\ell\), the test \(e\mid d\) is \(qh=N\bmod\ell e\). Its main term is \(H^2\varphi(\ell)/(4\ell^2)\) times the product of the local densities \((p-1)/p^2\) for \(p\nmid N\) and \((2p-1)/p^2\) for \(p\mid N\). To see this, expand the permitted residue pairs modulo \(e\) into at most \(e^2\) rectangles by residue classes. On each class, use the congruence modulo \(\ell\), which reduces by invertible translations and scaling to a unit hyperbola. Complete periods and remainder rectangles give error \(O(\ell^{1/2+o(1)}(1+H/\ell))\) per class, including integer rounding. The CRT yields the main density. [Fixed-rectangle completion](https://arxiv.org/pdf/1103.2879) · [Estermann](https://doi.org/10.1112/S0025579300002187).

Use a standard upper-bound fundamental-lemma sieve of level \(N^{1/100}\), with \(|\lambda_e|\le1\), dimension at most two and \(z=N^c\) for \(c\) sufficiently small. Its main term is bounded by a fixed constant times the product of local survival factors. That product is \(O(1/L)\) by Mertens: away from \(\ell N\) the survival factor is \(1-1/p+O(p^{-2})\), and \(p\mid N\) only decreases it. Omitting \(p\mid\ell\) causes a bounded loss because \(\ell\) is \(Y\)-rough. The sum of the \(e^2\) costs is \(O(N^{3/100})\). This proves (1). Summing its errors over \(\ell\le H\), including any original logarithmic weights, costs \(N^{.78+o(1)}\). [Upper-bound fundamental lemma, Theorem 3.6](https://ford126.web.illinois.edu/sieve2023.pdf).

## Consequences for few-factor and semiprime endpoints

On the odd-\(m\) region, the original \(q,h\) swap replaces \(\log h\) in the signed weight by \(\tfrac12\log(h/q)\), of bounded magnitude. This requires the same \(q,h\)-symmetric support as the peer center; the added conditions are independent of their order. Thus the absolute value of the reflected sum on any allowed set of \(\ell\)'s is at most
\[
 \ll\frac N L\sum_{\ell\text{ allowed}}\frac{\log\ell}{\ell}+N^{.78+o(1)}.
\]
For \(\ell\le V\le H\) squarefree and \(Y\)-rough with at most a fixed \(k\ge1\) prime factors, the reciprocal sum is \(O_k(\log(2V)(1+\log L)^{k-1})\). Expand \(\log\ell=\sum_{p\mid\ell}\log p\); sum the marked prime with weight \(\log p/p\), and the remaining at most \(k-1\) primes with reciprocal weight. The bound follows by Chebyshev and Mertens. Thus for \(V=\exp(L^\sigma)\) with any fixed \(\sigma<1\), the odd-\(m\) contribution is \(o(N)\). One may also take \(V=\exp(L/(\log L)^A)\) for fixed \(A>k-1\). This treats both \(n\)-parities wherever permitted by the original support.

If \(n\) is squarefree semiprime, \(d>H\) can be \(n\) itself only with \(\ell=1\), whose weight is zero. Every other admitted \(d\) is prime and \(\ell\) is prime. Therefore all these estimates apply to the semiprime slice of the even-endpoint center. For a single dyadic prime-\(\ell\) shell, the harmonic sum with \(\log\ell\) is \(O(1)\); hence its odd-\(m\) signed bound is \(O(N/L)+N^{.78+o(1)}\), even at polynomial scales. Any \(o(L)\) such shells can be combined. Covering all \(O(L)\) polynomial-scale shells by this estimate gives only \(O(N)\). On the even-\(m\) part the missing reflection saving likewise prevents a full bound from this count. This describes which part of the peer even-endpoint row is removed.

[Exact surviving center in the peer ledger](https://github.com/Sodelin/Research-Commons/blob/bd417b56fe190a8a34918fb5b9405acb4c6d735d/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-20-over-19-ledger-reply.md#exact-center-after-both-rough-factor-charges).
