# Follow-up proof note — Landau windows and the Goldbach cutoff

## Finite positive families

Let finitely many \(L_j\) be meromorphic on \(\Re s>0\), with no poles there except a possible pole of order \(r_j\ge0\) at \(1\), and no zeros on \(\Re s\ge1\). Assume \(-L'_j/L_j(s)=\sum_n\Lambda_j(n)n^{-s}\) on \(\Re s>1\), with \(|\Lambda_j(n)|\ll_j\Lambda(n)\). Define
\[
c_j=\lim_{s\to1}\big(L'_j/L_j(s)+r_j/(s-1)\big),\qquad
G_j(y)=\sum_{n\le y}\Lambda_j(n)(y/n-1)-r_j y\log y+(r_j+c_j)y .
\]
For fixed positive \(a_j\), put \(G(y)=\sum_j a_j\Re G_j(y)\). If \(G(y)\le Cy^\theta\) throughout arbitrarily late windows \([Y,Y^{1+\kappa}]\), for \(C,\kappa>0\) and \(0<\theta<1\), all family members are zero-free in \(\theta<\Re s<1\).

The Laplace transform of \(G_j(e^u)\) for \(\Re s>2\) is
\[
\Phi_j(s)=-\frac{L'_j(s)}{s(s-1)L_j(s)}-\frac{r_j}{(s-1)^2}+\frac{r_j+c_j}{s-1}.
\]
Both poles at \(1\) cancel. Taking the real part pairs \(\Phi_j(s)\) with \(\overline{\Phi_j(\bar s)}\). At a strip zero \(z\) of a family member or its conjugate the resulting residue is \(-\sum_j a_j(m_j(z)+m_j(\bar z))/(2z(z-1))\), with \(m_j\) the zero multiplicity extended by zero. The sum of multiplicities is positive. Thus the poles are isolated, have nonzero residues, and the residue at a real pole is positive. The coefficient bound gives continuity and \(O(e^{2u})\) growth for \(u\ge0\). On the log window \([U,(1+\kappa)U]\), the majorant \(Ce^{\theta u}\) has normalized integral \(C\kappa U\le e^{\eta U}\) for every \(\eta>0\) on sufficiently late windows. This verifies the generic Lean theorem's inputs by hand. [Pinned generic theorem](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84) · [Pole and window inputs](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean#L15-L29).

A finite-order Hecke character's functional equation with its dual, together with conjugation, gives \(z\mapsto1-\bar z\) in the open strip. Thus windows for \(\theta\downarrow1/2\) give the critical line using the real part of a single character's sum. For a concrete non-self-dual test, twist the standard \(S_3\) representation of the original memo by a Dirichlet character \(\nu\bmod7\) of order three. Its cyclic cubic field is disjoint from the \(S_3\) closure since \(S_3\) has no quotient \(C_3\). The compositum has group \(S_3\times C_3\), with the second factor acting by \(\nu\) on the twist and \(\bar\nu\) on the dual. The Hecke character over \(K=\mathbb Q(\sqrt{-23})\) is \(\chi(\nu\circ\mathrm N_{K/\mathbb Q})\). The Artin conductor is \(23\cdot7^2=1127\), since the twist is unramified at \(23\) and acts by a nontrivial tame scalar on a two-dimensional unramified representation at \(7\). The new window estimate for this twist is open in this argument. [Artin induction](https://doi.org/10.1007/BF02941010) · [Hecke analytic theory](https://www.math.ias.edu/~goresky/pdf/3-01Tate.pdf).

**Converse for the original \(S_3\) factor.** Assume Artin GRH only for the converse. With checked RH and \(\zeta_E=\zeta L_\rho\), Grenié–Molteni give \(A_\rho(t)=\psi_E(t)-\psi_{\mathbb Q}(t)\ll \sqrt{t}[(1+\log t)\log Q+(1+\log t)^2]\) for \(t\ge100\), \(Q=|D_E|\), with an absolute constant for cubics. Partial summation gives the first term of \(G_\rho(y)\) as \(y\int_1^y A_\rho(t)t^{-2}dt\). Dominated convergence in \(-L_\rho'/L_\rho(s)=s\int_1^\infty A_\rho(t)t^{-s-1}dt\) at \(s=1\) gives \(G_\rho(y)=-y\int_y^\infty A_\rho(t)t^{-2}dt\). Thus the same estimate, with \(t\) replaced by \(y\), bounds \(|G_\rho(y)|\) for \(y\ge100\). This proves the converse to the original window criterion with conductor dependence, assuming checked RH. [Grenié–Molteni, Corollary 1.2](https://doi.org/10.1090/mcom3031).

## A larger negligible divisor slice at each even \(N\)

Write \(L=\log N,\ H=\sqrt N,\ Z=\exp(L^\beta),\ \delta=1-\beta,\ 0<\beta<1\). Retain the pinned cutoff \(D=\lfloor\exp((\delta/64)L^\delta\log L)\rfloor\) and exact support. For a sufficiently large fixed \(C_\delta\), put
\[
D_*=\left\lfloor \exp\left(\frac{\delta}{2}L^\delta\log L+\frac12 L^\delta\log\log L-C_\delta L^\delta\right)\right\rfloor .
\]
Under Dirichlet GRH and Baker–Harman, the exact signed contribution of \(D<d\le D_*\) on \(qh+d\ell=N\) is \(O_{\delta,A}(N/L^A)\) for all fixed \(A\), with all original signs and parities. The estimate also holds on the \(Y\)-rough endpoints, for \(Y=\lfloor\exp(L^{\delta/2})\rfloor\). The leading coefficient of \(L^\delta\log L\) in the cutoff exponent increases by a factor of \(32\). [Pinned cutoff](https://github.com/Sodelin/Research-Commons/blob/4ad4701470274b6793bbcd352b1c9493733e7727/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/third-pass-two-boundaries.md) · [Baker–Harman](https://doi.org/10.1112/jlms/s2-43.2.193).

For fixed \(q,z\), \(|z|=1\), write \(f(h)=\mu(h)1_{(h,q)=1}z^{k(h)}=(\mu*g)(h)\) with \(k\) the intermediate prime count. Then \(g(p^j)=1-a_p\) for \(j\ge1\) with \(a_p=-f(p)\), and only \(p\le Z\) or \(p\mid q\) can have \(a_p\ne1\). Set \(\lambda=(\delta\log L+\log\log L)/\log Z\) and \(A_0=\lambda\log Z\). The geometric series at each prime, Chebyshev's bound, and partial summation give
\[
\log\sum_e|g(e)|e^{-1+\lambda}
\ll \sum_{p\le Z}p^{-1+\lambda}+LZ^{-1+\lambda}
\ll 1+\log\log Z+e^{A_0}/A_0+LZ^{-1+\lambda}
=O_\delta(L^\delta).
\]
In the partial summation integral \(\int_{\log 2}^{\log Z} e^{\lambda v}dv/v\), split at \(\lambda v=1\). Then split the convolution at \(X=H\exp(-8L^\delta\log L)\). With fixed exponent \(7/8\) Baker–Harman bounds the part \(e\le X\) by \(H^{7/8}X^{1/8}\sum_e|g(e)|e^{-1+\lambda}\). For \(e>X\) trivial counting gives \(HX^{-\lambda}\sum_e|g(e)|e^{-1+\lambda}\). Since \(8\lambda L^\delta\log L=o(L^\delta)\), the combined bound, uniformly in prefix and additive frequency, is
\[
H\exp\!\left(-\frac{\delta}{2}L^\delta\log L-\frac12L^\delta\log\log L+O_\delta(L^\delta)\right).
\]
The exact count mask is extracted on the unit circle with \(O(L)\) coefficients at most. At each \(q,d\), \((q,N)=1\) makes the divisibility condition either empty or one progression in \(h\), with additive Fourier coefficient absolute sum one. Partial summation costs \(O(L^2)\) for the log weights. Sum over at most \(HD_*\) pairs to prove the claim.

For rough endpoints, inclusion–exclusion at \(k=\lceil C_A\log L\rceil\) uses at most \(Y^k=\exp(o(L^\delta))\) moduli, which fits the cutoff margin. Combined divisibility tests are again empty or a single progression. The truncation error is bounded by the pinned divisor-moment argument, whose fixed-endpoint weight bound is independent of the divisor cutoff. This gain is a hand deduction using Dirichlet GRH alone. [Pinned rough-endpoint reduction](https://github.com/Sodelin/Research-Commons/blob/4ad4701470274b6793bbcd352b1c9493733e7727/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/rough-residual-and-norm-limit.md).
