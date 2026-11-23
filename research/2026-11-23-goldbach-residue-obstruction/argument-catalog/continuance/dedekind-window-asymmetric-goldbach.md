# Dedekind windows and an asymmetric Goldbach divisor range

Two hand deductions. The first reduces off-line Artin control to one Dedekind window per Galois closure. The second bounds an exact asymmetric Goldbach sector by a sieve and a middle-count restriction.

## One Dedekind window for a finite Galois extension

Let \(M/k\) be finite Galois with group \(G\). Put \(d_M=[M:\mathbb Q]\), \(D_M=|\operatorname{disc} M|\), and \(\gamma_M=\operatorname{FP}_{s=1}(\zeta'_M/\zeta_M)\). Define
\[
G_M(x)=\sum_{\mathrm N\mathfrak a\le x}\Lambda_M(\mathfrak a)(x/\mathrm N\mathfrak a-1)
-x\log x+(1+\gamma_M)x.
\]
Suppose that for every \(\epsilon>0\) sufficiently small there is \(C_{M,\epsilon}>0\) and there are arbitrarily large \(Y\) with \(G_M(x)\le C_{M,\epsilon}x^{1/2+\epsilon}\) throughout \([Y,Y^{3/2}]\). The finite positive family lemma of the preceding note applies to \(\zeta_M\) alone, with its simple pole and logarithmic-derivative coefficients bounded by \(d_M\Lambda(n)\). Letting \(\epsilon\downarrow0\) and using the Dedekind functional equation gives RH for \(\zeta_M\). This is a conditional hand application of the pinned generic theorem. The estimate is new input for general nonabelian \(M\). [Pinned generic theorem](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84).

For \(z\) in the open strip let \(a_\chi=\operatorname{ord}_z L(s,\chi,M/k)\) for \(\chi\in\operatorname{Irr}G\), using negative orders at poles. Brauer gives meromorphy. The virtual character \(\Theta=\sum_\chi a_\chi\chi\) restricts to a genuine character of every cyclic \(H\le G\). Indeed, the multiplicity of \(\omega\in\widehat H\) in the restriction is the order at \(z\) of the corresponding Hecke factor for \(M/M^H\), by Frobenius reciprocity and Artin formalism. That order is nonnegative. Therefore \(|\Theta(g)|\le\Theta(1)\) for each \(g\) by taking \(H=\langle g\rangle\), and the regular-representation identity gives \(\Theta(1)=\operatorname{ord}_z\zeta_M\). Character orthogonality yields
\[
\sum_\chi |a_\chi|^2\le(\operatorname{ord}_z\zeta_M)^2 .
\]
In particular the window excludes both zeros and poles for all the Artin factors off the critical line in the open strip. A simple zero of \(\zeta_M\) forces precisely one order \(+1\) at a linear character since \(\Theta(1)=1\). This argument leaves the pole question at multiple zeros on the line open. Conversely, absence of all off-line Artin divisors in the open strip implies Dedekind RH by the regular-representation factorization. [Brauer](https://doi.org/10.2307/1969183) · [Heilbronn](https://doi.org/10.4153/CJM-1973-090-3) · [Stark, Theorem 3](https://doi.org/10.1007/BF01405166).

There is also a uniform conditional prime-power bound with only \(d_M,D_M\) in the error. Let \(\psi_\chi(x)\) use the full coefficients of \(-L'/L\) including ramified prime ideals. Under RH for \(\zeta_M\),
\[
|\psi_\chi(x)-\mathbf1_{\chi=1}x|\le\sqrt x
\left[\left(\frac{\log x}{2\pi}+2\right)\log D_M+
\left(\frac{\log^2x}{8\pi}+2\right)d_M\right].
\]
Indeed, Grenié–Molteni's weighted class count includes the average over inertia, and so \(\psi_\chi(x)=\sum_C\chi(C)\psi(C;x)\). Multiply their Theorem 1.1 by the class proportions, use \(\sum_C |C|\chi(C)/|G|=\mathbf1_{\chi=1}\), and apply Cauchy–Schwarz to \(\sum_C|C||\chi(C)|/|G|\le1\). The cyclic Hecke factors used in that proof inherit RH from \(\zeta_M\) by their product factorization. These marginal counts have no same-target Goldbach correlation. [Grenié–Molteni, Theorem 1.1 and §2](https://sites.unimi.it/molteni/research/papers-pdf/44-molteni-An_explicit_Chebotarev_density_theorem_under_GRH.pdf).

## Exact Goldbach sector with large \(d\) and small \(\ell\)

On the original square-root block, retain \(H=\sqrt N,\ L=\log N\), the exact middle-count mask, \((qh,N)=1\), squarefree \(qh\), and \(n=d\ell=N-qh\) with no prime factor \(\le Y=\lfloor\exp(L^{\delta/2})\rfloor\). Here \(\delta=1-\beta\) and the middle interval is \((\exp(L^\gamma),\exp(L^\beta)]\). The exact summand is \(-\mu(h)\mu(d)\log h\log\ell\). Restrict to \(d\ge H,\ \ell\le V=\exp(L^\sigma)\), with fixed \(\delta/2<\sigma<1\), and to \(q,h\) each having a largest prime \(\ge N^\varepsilon\), fixed \(0<\varepsilon<1/2\). These conditions leave \(d\) free to be composite. Further restrict the middle count \(k(qh)\) to \(k(qh)\le\alpha\log L\) when \(\alpha<m=2(\beta-\gamma)\), or \(k(qh)\ge\alpha\log L\) when \(\alpha>m\), intersecting either condition with the original mask. Put \(I(\alpha)=\alpha\log(\alpha/m)-\alpha+m\).

The absolute weight over this sector is
\[
O\left(N(1+\log L)L^{1-I(\alpha)+2\sigma-\delta}\right).
\]
On the additional odd sector \(\mu(qh)=-1\), its signed contribution satisfies
\[
O\left(N(1+\log L)L^{-I(\alpha)+2\sigma-\delta}\right).
\]
All constants may depend on the fixed parameters. For \((\beta,\gamma)=(.99,.10)\), the lower-tail choice \((\alpha,\sigma)=(.26,.01)\) saves a power of \(L\) in the first bound. In the second bound \((\alpha,\sigma)=(.35,.40)\) saves a power as well. These exponents were evaluated numerically only to illustrate the proven inequalities. [Original exact signed expansion and two-form sieve context](https://github.com/Sodelin/Research-Commons/blob/4ad4701470274b6793bbcd352b1c9493733e7727/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/third-pass-two-boundaries.md).

Write \(q=ar,\ h=bs\) with \(r,s\) the largest primes. Fix \(a,b,r,\ell\). The support forces \((qb,\ell)=1\) and \((N,qb\ell)=1\). Solve \(s=s_0+\ell t\), \(d=(N-qbs_0)/\ell-qb t\) over an interval of length \(O(X)\), \(X=H/(b\ell)\ge N^{\varepsilon-o(1)}\) on nonempty rows. We count \(s\) prime and \(d\) rough. Sift \(s\) up to \(z=N^\nu\), where \(\nu>0\) is sufficiently small in terms of \(\varepsilon\), and \(d\) up to \(Y<z\). For odd \(p\nmid Nqb\ell\), the two roots are distinct when \(p\le Y\) by the determinant \(N\). For \(Y<p\le z\) there is one root. For primes dividing \(Nqb\ell\), the root losses in the product cost at most \(g(N)g(q)g(b)g(\ell)\), where \(g(v)=\prod_{p\mid v,\ p>2}(p-1)/(p-2)\). For \(p\mid\ell\) above \(Y\), the \(s\)-form is constant and nonzero, so \(p/(p-1)\le(p-1)/(p-2)\) suffices. Prime \(2\) can be omitted.

For clarity, apply the upper Brun sieve to the congruence exclusions with local densities \(\nu_p/p\le2/p\), excluding \(2\). The remainder per squarefree sieve modulus \(e\) is at most \(\prod_{p\mid e}\nu_p\) by the CRT and counting a residue class in an interval. Thus the upper sieve gives \(O(X\prod_{p\le z,p>2}(1-\nu_p/p)+z^{c_2})\) with an absolute \(c_2\). By choosing \(\nu\) small, the error is absorbed in \(X/(L\log Y)\). Mertens bounds the product by \(O(g(N)g(a)g(b)g(\ell)/(L\log Y))\), since \(r\ge N^\varepsilon\) and \(g(r)=O(1)\). Chebyshev bounds the number of \(r\)'s by \(O(H/(aL))\). [Upper Brun sieve, Theorem 8.5.2 as quoted on p. 50](https://pub.math.leidenuniv.nl/~evertsejh/Fundamental%20Lemma.pdf).

The absolute weight per placement is \(\le L\log\ell\). Because \(\ell\) is rough,
\[
\sum_{\ell\le V,\ \ell\ {\rm rough}}\frac{g(\ell)\log\ell}{\ell}
\le \log V\prod_{Y<p\le V}\big(1+g(p)/(p-1)\big)
\ll(\log V)^2/\log Y .
\]
For the cofactor sums, choose \(t_0=\alpha/m\). On either specified tail its indicator is bounded by \(t_0^{k(a)+k(b)-\alpha\log L}\), because \(r,s>Z\), and the original squarefree support makes the counts additive. Dropping the cross-coprimality restriction after the bound, the two squarefree cofactor Euler products with weights \(g(a)/a,g(b)/b\) contribute \(O(L^{2-m+mt_0})\). Indeed, the contributions of primes inside and outside the middle interval to the combined logarithm are \(mt_0\log L+O(1)\) and \((2-m)\log L+O(1)\). The factor \(t_0^{-\alpha\log L}\) makes the final cofactor bound \(O(L^{2-I(\alpha)})\). Multiplication gives the first inequality using \(g(N)\ll1+\log L\). For odd \(qh\), the same sector is invariant under \(q\leftrightarrow h\), and squarefreeness gives \(\mu(q)=-\mu(h)\). Its average signed summand is \(-\tfrac12\mu(h)\mu(d)\log(h/q)\log\ell\). The ratio is bounded by \(2\) on the original block, saving a factor \(L\) for the second inequality. No averaging over \(N\), Artin GRH, or prime assumption on \(d\) enters this argument.

A separate corollary drops the middle-count tail condition if \(q,h\) are both \(\exp(L^\gamma)\)-rough and \(qh\) is odd in Möbius parity. The cofactor products are then bounded by \(O(L^{2(1-\gamma)})\) from Mertens. The same sieve and single reflection give a signed bound \(O(N(1+\log L)L^{2\sigma-2\gamma-\delta})\), so any fixed \(\delta/2<\sigma<\gamma+\delta/2\) gives \(o(N)\) throughout the original middle-count mask.

### Where this meets the earlier bounded ranges

The asymmetric estimate applies in the orientation \(d\ge H\), \(Y<\ell\le \exp(L^\sigma)\). The endpoint \(\ell=1\) has zero weight, and \(1<\ell\le Y\) is excluded by roughness. The earlier double-reflection estimate needs both \(d,\ell\ge H/F\), with \(F=\exp((\log Y)^\eta)\) for fixed \(\eta<1\). Since \(\exp(L^\sigma)=N^{o(1)}\) and \(H/F=N^{1/2-o(1)}\), these two proved ranges are disjoint for large \(N\). On the common arithmetic support this leaves the interval \(\exp(L^\sigma)<\ell<H/F\) outside these two estimates, as well as any asymmetric tuples that fail the sieve's cofactor or parity restrictions. This comparison is with the published double-reflection bound. A separate determinant estimate would need to be compared using its own cutoff and support. [Pinned double-reflection bound and its improvement](https://github.com/Sodelin/Research-Commons/blob/9ef17a4f38a850126bcf0f47157041f3fdbe0ef8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/riemann-goldbach-proof-memo.md#L37-L59).
