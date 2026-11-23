# Logarithmic windows in the retained-rough Goldbach Type II sum

This is a hand upper bound at one fixed even target \(N\). Write \(L=\log N\), \(H=\sqrt N\), \(m=qh\), and \(n=N-m=\ell uv\). Keep the retained-endpoint Vaughan expansion, so \(n\) is squarefree and \(Y\)-rough, where \(Y=\exp(L^{.005})\). Keep ordered \(q,h\in(H/2,H]\), squarefree \(m\), \((m,N)=1\), the exact count and mark masks, prime \(N^{1/10}<\ell\le N^{1/8}\), the original strict \(uv>D_0\), and any preceding endpoint cut. The retained Vaughan thresholds imply \(u,v\ge N^{c_0}\) for some fixed \(c_0>0\). The exact signed weight is
\[
 \tfrac12 F(m)\mu(h)\mu(u)B_V(v)\log(h/q)\frac{\log\ell}{\log(uv)}.
\]
Here \(B_V(v)\) may retain only the admitted \(w\mid v\) contributions after earlier charges. They are nonnegative and sum to at most \(\log v\). The original signs and subset masks are applied before taking absolute values. [Pinned retained endpoint expansion](https://github.com/Sodelin/Research-Commons/blob/3c4778ccc493abb2b5f9610c8fce5ea86fd0737d/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rough-complement.md) · [Pinned balanced-box weight and completion](https://github.com/Sodelin/Research-Commons/blob/6e1fa1e477a161e3e36c652bd3f353997bb82c22/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-balanced-type-ii-marks-2141z.md).

Let the allowed prime \(\ell\)'s lie in any interval of log width at most \(W\), intersected with the pinned prime band. For each \(\ell\) and each dyadic endpoint band, let \(\log(u/v)\) lie in an interval of width at most \(\Delta\). Its location may depend on \(N,\ell\), and the band. The absolute weight of any further intersection on this support is
\[
 \ll_A \frac{N(1+W)(1+\Delta)}{(\log Y)^2}
              +\frac{N}{L^A}+N^{27/32+o(1)}
 \tag{1}
\]
for every fixed \(A>0\). Thus widths satisfying \((1+W)(1+\Delta)=o((\log Y)^2)\) give \(o(N)\). There is no prime or factor-count requirement on either \(u\) or \(v\).

## Dyadic endpoint count

Trim \(n<N/L^B\) with error \(O_A(N/L^A)\), for fixed \(B\) chosen in terms of \(A\). At each \(n\), there are at most nine eligible prime divisors \(\ell\), at most \(\tau(n)\) choices of \(u\), and at most \(\tau(N-n)\) choices of \(q,h\). The bound \(B_V(v)\le\log v\) makes the total absolute weight there \(O(L\tau(n)\tau(N-n))\). Cauchy–Schwarz and fixed divisor moments prove the stated trim.

In band \(j\), given by \(N2^{-j-1}<n\le N2^{-j}\), both \(q,h\) lie within \(H2^{-j}\) of \(H\). Indeed, \(N-qh\ge H(H-q)\) and likewise for \(h\). Use the containing rectangle of area \(O(N4^{-j})\). For fixed \(\ell\) and band \(j\), put \(x=\min(u,v)\), \(y=\max(u,v)\). Since
\[
 2\log x=\log(n/\ell)-|\log(u/v)|,
\]
the interval for \(\log x\) has width \(O(1+\Delta)\). It is at polynomial scale by the two lower thresholds. Both factors are \(Y\)-rough.

Fix \(\ell,x\) and write \(M=\ell x\). Then \(y=(N-qh)/M\), \(qh\equiv N\pmod M\), and \((M,N)=1\). Also \(M\le\sqrt{N\ell}\le N^{9/16}\). For each squarefree sieve divisor \(e\) supported on primes at most \(Y\), coprime to \(M\), the condition \(e\mid y\) gives the CRT test \(qh=N\bmod Me\). Its local density at \(p\mid e\) is \((p-1)/p^2\) if \(p\nmid N\) and \((2p-1)/p^2\) if \(p\mid N\). Enumerate the bad pairs modulo \(e\) and apply the rectangular unit-hyperbola count modulo \(M\) on the rescaled boxes. The main density at \(M\) is \(\varphi(M)/M^2\). The error per residue pair is \(O(M^{1/2+o(1)}(1+H/M))\), uniform in the original rectangle widths and including rounding. [Fixed-rectangle completion, equation (10)](https://arxiv.org/pdf/1103.2879) · [Composite Kloosterman bound](https://doi.org/10.1112/S0025579300002187).

Use an even Bonferroni truncation of size \(K=C_A\log L\). The moduli satisfy \(e\le Y^K=N^{o(1)}\), and the total residue-box cost is \(N^{o(1)}\). Writing \(g(p)\) for the bad density, the main-term truncation error is at most \((\sum g(p))^{K+1}/(K+1)!\), arbitrarily log-small for a large fixed \(C_A\). The survival product is \(O(1/\log Y)\) by Mertens, because \(p\mid N\) only decreases survival and \(M\) is already \(Y\)-rough. Thus the count at fixed \(\ell,x,j\) is
\[
 \ll \frac{N4^{-j}}{M\log Y}+N^{o(1)}M^{1/2}(1+H/M).
 \tag{2}
\]
Counting the two possible positions of \(x,y\) costs at most two in this upper bound. The accumulated remainder after weights is \(N^{27/32+o(1)}\). Indeed \(M\le N^{9/16}\), its multiplicity in \((\ell,x)\) is \(N^{o(1)}\), and summing \(M^{1/2}+HM^{-1/2}\) gives that exponent. There are only \(O(1+\log L)\) bands after the trim, and the absolute weight at a fixed placement is \(O(\log\ell)\). Neither the modulus estimate nor this error sum depends on the chosen interval locations or on the additional selected intersection.

## Summing the main term

The interval for \(x\) meets \(O(1+\Delta)\) dyadic scales. On each polynomial scale \(X\), the reciprocal sum of \(Y\)-rough integers is \(O(1/\log Y)\). This follows by one-dimensional upper inclusion–exclusion at the same cutoff, with local density \(1/p\) and total floor error \(N^{o(1)}\). Hence \(\sum 1/x\ll(1+\Delta)/\log Y\). Also \(\sum_{\ell\ \mathrm{prime}}\log\ell/\ell\ll1+W\) in the given log interval, by Chebyshev and partial summation. Summing (2) after restoring the bound \(O(\log\ell)\), and using \(\sum_{j\ge0}4^{-j}\ll1\), proves (1).

More generally the main term is bounded by
\[
 \frac{N}{(\log Y)^2}\sum_{\ell\ \mathrm{allowed}}\frac{\log\ell}{\ell}
         \sum_{j\ \mathrm{used}}4^{-j}(1+\Delta_{\ell,j})
\]
up to a fixed constant. Here \(\Delta_{\ell,j}\) is the actual log width in that cell. For a union of ratio intervals, replace \(1+\Delta_{\ell,j}\) by the sum of that quantity over the intervals. The same power error applies, since each fixed modulus and band can be counted once. If also \(n\le\xi N\), the contributing \(4^{-j}\) sum is \(O(\xi^2)\). For example, throughout the full polynomial \(\ell\) band, fixed bounded ratio widths and \(n\le N/L^{1/2}\) give \(o(N)\). These bounds concern the retained-mask expansion and leave broad log widths on central endpoints uncovered.

The estimates use the pinned arithmetic support and hand upper bounds. No numerical or Lean verification is used.
