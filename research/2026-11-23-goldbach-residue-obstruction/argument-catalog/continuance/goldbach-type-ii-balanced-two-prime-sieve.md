# A balanced two-prime slice of the fixed-target Goldbach Type II sum

Use the opened Vaughan expansion on its original ordered support. Put \(L=\log N\), \(H=\sqrt N\), \(m=qh\), and \(n=N-m\), with \(q,h\in(H/2,H]\), squarefree \(m\), \((m,N)=1\), and the exact typical count and mark projector \(F(m)\). Keep the original strict condition \(d=uws>D_0\), the prime \(N^{1/10}<\ell\le N^{1/8}\), the retained thresholds on \(u,w\), and any original lower endpoint cutoff. The equation and signed weight are
\[
 qh+\ell uws=N,\qquad
 \tfrac12 F(m)\mu(h)\mu(u)\Lambda(w)\log(h/q)
                      \frac{\log\ell}{\log(uws)}.
\]
Keep the already retained prime \(w\) and \((\ell w,us)=1\). The following upper bound is valid after intersecting with the preceding small-base and marked-orbit exclusions. [Pinned Type II support](https://github.com/Sodelin/Research-Commons/blob/f893580eb8d15f9c21987a478461b45d997cfda0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md) · [Pinned small-base and prime-power removal](https://github.com/Sodelin/Research-Commons/blob/581f30cc217415f438594c02cfc4f894837fe981/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-small-prime-base.md).

Require in addition that \(u\) is prime and \(C^{-1}\le u/w\le C\) for a fixed \(C\ge1\). Let \(\mathcal S\) be any allowed set of positive integers \(s\le N^\sigma\), where \(0\le\sigma<5/24\) is fixed. The absolute weight on this slice is
\[
 O_A\!\left(\frac{N(1+\log L)}L\sum_{s\in\mathcal S}\frac1s+\frac N{L^A}\right)
 \tag{1}
\]
for every fixed \(A>0\), uniformly at each even \(N\). Constants may depend on the fixed cutoffs and \(C,\sigma\).

## Count at a fixed composite modulus

Trim \(n<N/L^B\) with error \(O_A(N/L^A)\) by the pinned divisor-moment bound, choosing fixed \(B\) in terms of \(A\). For fixed \(\ell,s\), comparability gives
\[
 C^{-1/2}\sqrt{\frac{N}{\ell s L^B}}\le u,w\le C^{1/2}\sqrt{\frac{N}{\ell s}}.
\]
Thus both primes are at polynomial scale. Fix \(\ell,u,s\) and set \(M=\ell us\). The equation gives \(qh\equiv N\pmod M\), with \((M,N)=1\), and
\[
 M\ll_C N^a,\qquad a=9/16+\sigma/2<2/3.
\]
Count \(w=(N-qh)/M\) with no prime factor at most \(z=N^c\) for sufficiently small fixed \(c>0\), omitting \(p\mid M\) from the sieve. Every admitted prime \(w\) passes these tests.

For a squarefree sieve divisor \(e\), the bad local densities at \(p\mid e\) are \(g(p)=(p-1)/p^2\) for \(p\nmid N\) and \(g(p)=(2p-1)/p^2\) for \(p\mid N\). These count \(qh\equiv N\pmod p\). The CRT count thus has main term \(X_M\prod_{p\mid e}g(p)\), where \(X_M=H^2\varphi(M)/(4M^2)\). There are at most \(2^{\omega(e)}e\) bad residue pairs modulo \(e\). On each, the rescaled rectangle reduces to a unit modular hyperbola modulo \(M\). The rectangular Weil completion, with complete periods separated, gives per residue pair an error \(O_\epsilon(M^{1/2+\epsilon}(1+H/M))\), including integer rounding. [Fixed-rectangle completion, equation (10)](https://arxiv.org/pdf/1103.2879) · [Composite-modulus Kloosterman bound](https://doi.org/10.1112/S0025579300002187).

Take Selberg level \(D_s=N^\eta\), with \(\eta>0\) fixed in terms of \(\sigma\), and individual weight support through \(D_s^{1/2}\). The sieve remainder is bounded by the sum of the CRT errors with coefficients \(3^{\omega(e)}\) for \(e\le D_s\). Its reciprocal main denominator is \(O(\prod_{p\le z,p\nmid M}(1-g(p)))\). Indeed, in the full normalized Euler product for the denominator, include \(p\) with probability \(g(p)\). The expected log divisor is \(\sum g(p)\log p=O(\log z)\). Choosing \(c\) small in terms of \(\eta\) puts at least half this mass below \(D_s^{1/2}\) by Markov's inequality. [Selberg upper sieve, Theorem 4.1](https://ford126.web.illinois.edu/sieve2023.pdf).

Uniformly in \(M\), Mertens gives
\[
 \prod_{p\le z,p\nmid M}(1-g(p))
 \ll \frac1{\log z}\prod_{p\le z,p\mid M}(1-1/p)^{-1}.
\]
The omitted-prime reciprocal factor cancels against \(\varphi(M)/M\) in \(X_M\), leaving a bounded factor even if \(M\) contains many small primes. Also \(\sum_{e\le D_s}6^{\omega(e)}e\ll D_s^2(1+\log D_s)^5\). The resulting number of pairs \(q,h\) at fixed \(\ell,u,s\) is
\[
 \ll \frac{N}{ML}+N^{2\eta+o(1)}M^{1/2}(1+H/M).
\tag{2}
\]
There are at most \(d_3(M)=N^{o(1)}\) triples \((\ell,u,s)\) with the same \(M\). The weight's magnitude is \(O(\log\ell)\), since \(\Lambda(w)\le\log(uws)\) and \(|\log(h/q)|\le\log2\). After restoring it, the total remainder in (2) is
\[
 O\!\left(N^{\max(3a/2,\,1/2+a/2)+2\eta+o(1)}\right)
 =O\!\left(N^{27/32+3\sigma/4+2\eta+o(1)}\right).
\]
Choose \(2\eta<1-27/32-3\sigma/4\) to get a fixed power saving for every stated \(\sigma\).

## Summing the main term

For fixed \(\ell,s\), the prime \(u\) ranges over the displayed polynomial interval of ratio \(O_C(L^{B/2})\). Partial summation of Chebyshev's bound gives a reciprocal sum \(O((1+\log L)/L)\) there. Using also \(\sum_{\ell\text{ in the prime band}}\log\ell/\ell\ll L\), the main contribution of (2) is at most \(N(1+\log L)L^{-1}\sum_{s\in\mathcal S}1/s\), proving (1).

For example, (1) is \(o(N)\) if \(s\le\exp(L^\rho)\) for fixed \(0<\rho<1\). It is also \(o(N)\) at the full stated polynomial scale if \(s\) has at most a fixed \(k\) prime factors, whose reciprocal mass is \(O_k((1+\log L)^k)\), or if all prime factors of \(s\) exceed \(N^\xi\) for fixed \(\xi>0\), whose reciprocal mass is \(O_\xi(1)\).

The primality of \(u\) can be relaxed to at most a fixed \(j\) distinct prime factors, with \((1+\log L)^j\) replacing \(1+\log L\) in (1). The nonzero \(\mu(u)\) weight makes \(u\) squarefree. Mark its largest prime, which is at polynomial scale. For each product of the other at most \(j-1\) primes, the marked prime stays in an interval of the same polylogarithmic ratio. Its reciprocal sum is \(O((1+\log L)/L)\), and the unmarked reciprocal sum costs \(O_j((1+\log L)^{j-1})\). The fixed-modulus count is unchanged.


A growing low factor count also gives a saving. For fixed \(0<\alpha<1\), allow \(\omega(u)\le\alpha\log L\) and put \(f(\alpha)=\alpha(1+\log(1/\alpha))<1\). The largest prime of such a squarefree \(u\) is \(\ge\exp(cL/\log L)\) for a fixed \(c>0\), by the polynomial lower bound on \(u\). In each polylogarithmic ratio interval the reciprocal sum of possible largest primes is then \(O_\alpha((1+\log L)^2/L)\) by dyadic Chebyshev bounds. For the unmarked part \(a\) of \(u\), Mertens and the factorial expansion give
\[
 \sum_{\substack{a\le N,\ \mu^2(a)=1\\ \omega(a)\le \alpha\log L}}\frac1a
 \le \sum_{j\le \alpha\log L}\frac{(\sum_{p\le N}1/p)^j}{j!}
 \ll_\alpha L^{f(\alpha)}.
\]
The last estimate follows from \(j!\ge(j/e)^j\) and the geometric domination by the last term for fixed \(\alpha<1\). Thus the general absolute bound on this slice is
\[
 O_A\!\left(N(1+\log L)^2 L^{f(\alpha)-1}
           \sum_{s\in\mathcal S}\frac1s+\frac{N}{L^A}\right).
\]
For instance \(s\le\exp(L^\rho)\) is admissible for a saving when \(0<\rho<1-f(\alpha)\), and polynomial \(s\) of bounded factor count also gives a saving throughout \(0\le\sigma<5/24\).

These are absolute estimates on the stated balanced Type II slice. They leave the unrestricted signed Type II sum open.
