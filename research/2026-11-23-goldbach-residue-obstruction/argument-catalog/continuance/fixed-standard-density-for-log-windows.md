# Fixed standard \(L\)-function density and logarithmic windows

Let \(\pi\) be a fixed unitary cuspidal representation of \(\operatorname{GL}_n(\mathbb A_F)\). In degree one, exclude pure imaginary norm powers. Write \(D=n[F:\mathbb Q]\), and let \(N_\pi(b,T)\) count completed zeros with real part at least \(b\) and absolute ordinate at most \(T\), with multiplicity. If
\[
 \max(1/2,1-1/D)<b<1,
\]
then some \(c_{b,D}>0\) gives
\[
 N_\pi(b,T)\ll_{\pi,b} T^{1-c_{b,D}}.
\tag{1}
\]
This suffices for \(\sum_{\Re\rho>b}(1+|\Im\rho|)^{-1}<\infty\). For a fixed dual-closed finite family, apply (1) factorwise. If the family has a zero to the right of \(\max_j\max(1/2,1-1/D_j)\), the reciprocal-sparsity criterion then detects an off-line zero on every late logarithmic interval of some sufficiently large fixed length. In particular all fixed cuspidal \(\operatorname{GL}_2/\mathbb Q\) families satisfy the reciprocal-sparsity premise at every real part strictly above \(1/2\), including at non-tempered archimedean parameters. [Pinned positive-filter criterion](https://github.com/Sodelin/Research-Commons/commit/ac31949e4a564781a10255f564f56a5d4b6b6f06)

## Rankin–Selberg coefficient means

Write the standard and reciprocal Dirichlet coefficients over ideals as \(a(\mathfrak n)\) and \(m(\mathfrak n)\). At an unramified prime with parameters \(\alpha\), their coefficients at the \(k\)-th power are \(s_{(k)}(\alpha)\) and \((-1)^k s_{(1^k)}(\alpha)\). The first is the complete homogeneous symmetric polynomial, and the second is the signed elementary symmetric polynomial. Since \(\pi\) is unitary, the self Rankin–Selberg coefficient there is \(\sum_{\lambda\vdash k}|s_\lambda(\alpha)|^2\) by the Cauchy identity. It dominates the square of each of the two coefficients. Multiplication over good primes and absolute convergence of the self Rankin–Selberg series in \(\Re s>1\) show that the two squared-coefficient series restricted to good primes also converge there. [Thorner–Zaman, §2.2 and equations (3.1)–(3.2)](https://arxiv.org/pdf/1906.07717v6)

At the finitely many ramified primes, \(|\alpha_i(\mathfrak p)|\le (N\mathfrak p)^{\vartheta_n}\) with \(\vartheta_n<1/2\), including zero parameters used to pad the degree. The local \(a(\mathfrak p^k)\) is \(O_n((k+1)^{n-1}(N\mathfrak p)^{k\vartheta_n})\), while \(m(\mathfrak p^k)=0\) for \(k>n\). Thus the squared ramified factors also converge on \(\Re s>1\), so
\[
 \sum_{N\mathfrak n\le X}(|a(\mathfrak n)|^2+|m(\mathfrak n)|^2)
 \ll_{\pi,\varepsilon} X^{1+\varepsilon}.
\]
The number of ideals of norm \(j\) is bounded by \(d_{[F:\mathbb Q]}(j)\), by comparing the local products \(\prod_{\mathfrak p\mid p}(1-X^{f(\mathfrak p/p)})^{-1}\) coefficientwise with \((1-X)^{-[F:\mathbb Q]}\). Cauchy–Schwarz therefore gives the same bound, after adjusting \(\varepsilon\), for the rational-norm grouped coefficients \(a_j,m_j\). It also gives the bound for their absolute convolution \(d_j=\sum_{k\mid j}|a_{j/k}m_k|\), because
\[
 \sum_{j\le X}d_j^2
 \ll_\varepsilon X^\varepsilon\sum_{k\le X}|m_k|^2
                  \sum_{\ell\le X/k}|a_\ell|^2
 \ll_{\pi,\varepsilon}X^{1+3\varepsilon}.
\tag{2}
\]
In the last step use the preceding square-mean bound with exponent \(1+\varepsilon\) for \(a_\ell\) and \(1+\varepsilon/2\) for \(m_k\), which gives convergence of \(\sum|m_k|^2/k^{1+\varepsilon}\). The small change in the final exponent is harmless. [Müller–Speh, Proposition 3.3](https://doi.org/10.1007/s00039-004-0452-0) · [Thorner–Zaman, equation (2.4)](https://arxiv.org/pdf/1906.07717v6)

## Analytic truncation

Write the completed function as \(G_\pi(s)L(s,\pi)\), including the conductor in \(G_\pi(s)\) and expressing all gamma factors as \(\Gamma_{\mathbb R}\) factors using \(\Gamma_{\mathbb C}(s)=\Gamma_{\mathbb R}(s)\Gamma_{\mathbb R}(s+1)\). The completion is entire of order one, and its functional equation pairs \(\pi\) with \(\widetilde\pi\). Fix \(\sigma_0\) strictly between the threshold in (1) and \(b\), and fix \(0<r<\min(b-\sigma_0,(\sigma_0-1/2)/4,1/8)\). Work with \(\sigma_0\le\sigma\le1+r\) and \(t\asymp T\). The Gaussian approximate functional equation is
\[
 L(s,\pi)
 =\sum_j a_jj^{-s}V_{\pi,s}(j)
  +\epsilon_\pi \frac{G_{\widetilde\pi}(1-s)}{G_\pi(s)}
   \sum_j \overline{a_j}\, j^{s-1}V_{\widetilde\pi,1-s}(j),\quad
 V_{\omega,w}(y)=\frac{1}{2\pi i}\int_{(3)}
       \frac{G_\omega(w+z)}{G_\omega(w)} e^{z^2} y^{-z}\frac{dz}{z}.
\]
Shift the integral for the completed \(L\)-function from \(3\) to \(-3\), crossing only \(z=0\), then use the functional equation and absolute convergence on the reflected positive line. Stirling gives \(|G_{\widetilde\pi}(1-s)/G_\pi(s)|\ll_\pi T^{D(1/2-\sigma)}\). [Godement–Jacquet](https://doi.org/10.1007/BFb0070263) · [Standard and self Rankin–Selberg analytic inputs, Thorner–Zaman, §2](https://arxiv.org/pdf/1906.07717v6)

Set \(K=T^{D/2}\). For \(y\le K\), moving the first weight to \(\Re z=-a\), with \(0<a<\sigma_0-\vartheta_n\), gives \(V_{\pi,s}(y)=1+O((y/K)^a)\), and its derivative after multiplication by \(y\) is \(O((y/K)^a)\). All numerator gamma arguments have positive real part in this shift, and only the explicit \(1/z\) pole is crossed. For \(y>K\), shifting either weight to any sufficiently large fixed \(A>3\) gives \(O((y/K)^{-A})\) for both the weight and the logarithmic \(y\)-derivative.

For the dual weight with \(y\le K\), shift to \(\Re z=2r\) within \(|\Im z|\le T/4\). If \(|t|\ge T/2\), the numerator gamma poles all have imaginary part of absolute size at least \(T/2-O_\pi(1)\), even when the original gamma shifts have negative real parts. There are no poles in this rectangle. The truncated shifted line is \(O((K/y)^{2r})\) for the weight and its logarithmic derivative by Stirling, since the absolute imaginary parts of all gamma arguments are \(\asymp_\pi T\) there. The two horizontal edges and the unused tails of the original line contribute \(O_{\pi,A}(\exp(-cT^2))\) for \(y\ge1\), up to fixed powers of \(T\) which can be absorbed, because \(e^{z^2}\) dominates the gamma quotient and \(y^{-\Re z}\le1\). Thus the dual dyadic weight and its total variation are \(O((K/Y)^{2r})\) for \(Y\le K\), without temperedness.

## Mollification and zeros

For a dyadic block of length \(Y\), Montgomery–Vaughan and a dyadic decomposition of arbitrary partial sums bound the squared \(L^2\) norm of the maximum partial sum of \(\sum c_jj^{-it}\) by
\[
 O\!\left((T+Y)\log^2(2Y)\sum |c_j|^2\right)
\]
on an interval of length \(O(T)\). Partial summation multiplies the bound for the \(L^2\) norm by the supremum plus total variation of a weight on that block. This works for weights depending on \(t\) since the variation bounds above are uniform pointwise in \(t\). [Montgomery–Vaughan, Corollary 2](https://doi.org/10.1112/jlms/s2-8.1.73)

Let \(P=T^\nu\) with \(\nu>0\) sufficiently small, and \(A_P(s)=\sum_{j\le P}a_jj^{-s}\). Replacing the first weight by \(1\) for \(j\le P\) costs \(O(K^{-a}P^{1+a-\sigma_0+\varepsilon})\) pointwise by (2) and Cauchy–Schwarz. Its squared mean has a power saving when \(\nu\) is sufficiently small. For \(j>P\), the first squared mean, after summing the dyadic \(L^2\) norms, is at most
\[
 O_{\pi,\varepsilon}\!\left(
       T^{1+\varepsilon}P^{1-2\sigma_0}
       +T^{D(1-\sigma_0)+\varepsilon}\right).
\]
Indeed the dyadic squared bound for \(Y\le K\) is \((T+Y)Y^{1-2\sigma_0+\varepsilon}\), and for \(Y>K\) the weight also gives arbitrary power decay. The \(T\) part is largest near \(P\), and the \(Y\) part near \(K\). For the dual sum before multiplication by the gamma ratio, the corresponding bound is
\[
 O_{\pi,\varepsilon}\!\left(T^\varepsilon(T+K)K^{2\sigma-1}\right),
\]
since \(2\sigma-1-4r>0\). The singleton \(j=1\) contributes \(O(TK^{4r})\) and obeys the same bound. The square of the gamma ratio turns this into
\[
 O_{\pi,\varepsilon}\!\left(
       T^{1+D(1/2-\sigma)+\varepsilon}
       +T^{D(1-\sigma)+\varepsilon}\right).
\]
All contributions save a power since \(\sigma_0>\max(1/2,1-1/D)\). Consequently \(\int |L(s,\pi)-A_P(s)|^2dt\ll_\pi T^{1-c_0}\) uniformly on the strip for some \(c_0>0\). The argument works on \(T/2\le |t|\le3T\).

Let \(M_X(s)=\sum_{j\le X}m_jj^{-s}\) with \(X=T^\eta\) and \(0<\eta\) sufficiently small. Its pointwise cost is at most \(O(X^2)\) by (2). The coefficients of \(A_PM_X-1\) vanish through \(X\) when \(X\le P\), and its support ends before \(T\). Equation (2) and Montgomery–Vaughan therefore bound its squared mean by \(O(T X^{1-2\sigma_0+\varepsilon})\). This gives \(\int |L(s,\pi)M_X(s)-1|^2dt\ll_\pi T^{1-c_1}\) uniformly on the strip for some \(c_1>0\).

At each zero with \(\beta\ge b\) and \(T\le|\gamma|\le2T\), the mollified deviation has value \(-1\). Its squared modulus has disk integral at least \(\pi r^2\) by subharmonicity. The disks lie within the bounded strip used above, and their multiplicity of overlap is \(O_\pi(\log T)\) by the local completed-zero count. Integrating in \(\sigma\) and summing the disk lower bounds gives \(O_{\pi,b}(T^{1-c_1}\log T)\) on the height block. This applies for either sign of \(t\), and dyadic summation proves (1). [Iwaniec–Kowalski, Proposition 5.7](https://doi.org/10.1090/coll/053)

This proof is in the height aspect of fixed representations. It is a hand proof of a density bound and its fixed-length detection consequence. No new arithmetic upper window, conductor uniformity, or zero verification is claimed.
