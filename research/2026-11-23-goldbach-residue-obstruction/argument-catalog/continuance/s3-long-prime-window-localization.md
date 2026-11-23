# Long-prime localization of the original conductor-23 upper window

Take the standard \(S_3\) representation \(\rho\) of the splitting field of \(T^3-T-1\), induced from the order-three ideal class character \(\chi\) of \(K=\mathbb Q(\sqrt{-23})\). Write \(L(s)=L(s,\rho)=\sum_n a(n)n^{-s}\), and let \(\mu_L\) be the reciprocal coefficients. Use the same \(K_B\) and exact negative sign of the original arithmetic-reference window \(C_{0,B}\). The prime-only Vaughan formula gives, for fixed \(B>0\), \(x\ge Y\), \(U=Y^{o(1)}\), and \(Q\asymp\sqrt Y\),
\[
 C_{0,B}(x)=
 -\frac14\sum_{Q<p\le e^B x/(U+1)}a(p)\log p\,W_{x,U}(p)
 +O_{\rho,B,\epsilon}(x^{1/2+\epsilon}),
 \quad
 W_{x,U}(t)=\sum_{h>U}\beta_U(h)K_B(ht/x),
 \quad
 \beta_U=\mu_{L,>U}*a .
\tag{1}
\]
The cutoff \(Q\) can also be raised to \(Y^{1/2+o(1)}\). [Original kernel and normalization](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md)

The convolution in (1) can be replaced by the unweighted prime trace up to \(p=x^{3/5}/U\), with an unconditional square-root error. A different comparison depending only on the actual rightmost zero supremum lets the upper-window criterion use just \(p>x^\alpha\) for any fixed \(1/2<\alpha<1\). Its remaining \(h\)-range is \(U<h\le e^Bx^{1-\alpha}\).

## A pointwise lattice estimate at the original kernel

Let \(S(y)=\sum_n a(n)K_B(n/y)\), with \(K_B(0)=1-e^{-B}\). Then
\[
 S(y)\ll_{\rho,B} y^{-1/4}\qquad(y>0).
\tag{2}
\]
To prove this, choose for each ideal class \(c\) of \(K\) an integral ideal \(\mathfrak b_c\) in class \(c^{-1}\). Integral ideals in class \(c\) correspond to nonzero elements \(\alpha\in\mathfrak b_c\) modulo units, by \(\alpha\mapsto (\alpha)\mathfrak b_c^{-1}\). Their norms are \( |\alpha|^2/N\mathfrak b_c\). Thus with \(w=\#\mathcal O_K^\times\), \(\mathcal L_c=\mathfrak b_c/\sqrt{N\mathfrak b_c}\subset\mathbb C\), and \(F_y(z)=K_B(|z|^2/y)\), one has
\[
 S(y)=\frac1w\sum_c\chi(c)\sum_{z\in\mathcal L_c} F_y(z).
\tag{3}
\]
The inserted zero points cancel by \(\sum_c\chi(c)=0\). All lattices have the same covolume \(\sqrt{23}/2\).

For \(\xi\ne0\), set \(d=2\pi|\xi|\). The Fourier transform of \(F_y\) on \(\mathbb R^2\) is
\[
 \widehat F_y(\xi)=\pi\int_0^\infty K_B(t/y)J_0(d\sqrt t)\,dt.
\]
In the first integration by parts use
\((\sqrt t J_1(d\sqrt t))'=(d/2)J_0(d\sqrt t)\), with zero boundary terms at \(0\) and \(\infty\). For the second use \(J_1(d\sqrt t)=-(2\sqrt t/d)(J_0(d\sqrt t))'\). On the support of the derivative of \(K_B(t/y)\), namely \(y<t<e^By\), the resulting coefficient \(t(K_B(t/y))'\) is \(-y/t\). Its total variation including endpoints is bounded independently of \(y\). The bound \(|J_0(v)|\ll v^{-1/2}\) for \(v>0\) yields
\[
 |\widehat F_y(\xi)|\ll y^{-1/4}|\xi|^{-5/2}.
\]
This decays summably on every two-dimensional dual lattice. Poisson summation follows by smoothing \(F_y\) with compact approximate identities and dominated convergence on the dual lattice and compact primary support. The zero frequencies are equal across classes and cancel. This proves (2). [Bessel identities and bounds, DLMF §§10.6 and 10.17](https://dlmf.nist.gov/10)

Since \(\beta_U=\mathbf1_{\{1\}}-\mu_{L,\le U}*a\), the exact weight and its approximation are
\[
 W_{x,U}(t)=K_B(t/x)-\sum_{m\le U}\mu_L(m)\,S(x/(mt))
 =K_B(t/x)+O_{\rho,B}\!\left((t/x)^{1/4}U^{5/4}\log(2U)\right).
\tag{4}
\]
Use \(|\mu_L(m)|\le\tau(m)\). Chebyshev and \(|a(p)|\le2\) show that for \(Q<P\le x^{3/5}/U\) the part of the prime sum in (1) with \(p\le P\), before its factor \(-1/4\), equals
\[
 (1-e^{-B})\sum_{Q<p\le P}a(p)\log p
 +O_{\rho,B}\!\left(x^{-1/4}(PU)^{5/4}\log(2U)\right).
\tag{5}
\]
The error is \(O_\epsilon(x^{1/2+\epsilon})\) on this support. This is unconditional. The prime trace prefix displayed in (5) still contributes at its own scale.

## Reduction to arbitrarily long primes for the zero criterion

Let \(\beta_*=\sup_{\rho_0}\Re\rho_0\) over critical-strip zeros of \(L(s)\), with \(\beta_*\ge1/2\) by symmetry. For the coefficient sequence in (1),
\[
 A(t)=\sum_{p\le t}a(p)\log p
 \ll_{\rho,\epsilon}t^{\beta_*+\epsilon}\qquad(t\ge2).
\tag{6}
\]
For \(\beta_*<1\), use truncated Perron for \(-L'/L\) at \(z=\lfloor t\rfloor+1/2\), height \(z^2\) and initial line \(1+1/\log z\). Its error is \(O_\rho(z^{-1}(1+\log z)^C)\). At \(n\asymp z\) use \(|\Lambda_L(n)|\le 2\log n\) and \(|n-z|\ge1/2\). Away from this range use absolute Euler convergence on the initial line. On every fixed line \(\sigma>\beta_*\), sufficiently close to \(\beta_*\) and less than \(1\), the local completed-zero expansion bounds the logarithmic derivative by \(O_{\rho,\sigma}(\log(3+|\Im s|))\), uniformly from this line to the initial line. Moving the contour there introduces no residues, and the shifted vertical integral is \(O_{\rho,\sigma}(z^\sigma\log^2(3+z))\). Higher prime powers cost \(O(\sqrt t)\). If \(\beta_*=1\), use Chebyshev. [Local logarithmic derivative, Iwaniec–Kowalski, Proposition 5.7](https://doi.org/10.1090/coll/053)

For the required variation in (4), each lattice \(\mathcal L_c\) has
\[
 \#\{z\in\mathcal L_c:0<|z|\le\sqrt y\}
 =\frac{\pi y}{\operatorname{covol}(\mathcal L_c)}+O_\rho(1+\sqrt y).
\]
Indeed, fixed fundamental cells covering boundary points of the disk lie in an annulus of fixed width. Summing across classes as in (3) shows \(\sum_{n\le y}a(n)=O_\rho(\sqrt y)\) for \(y\ge1\). Partial summation and the exact derivative of the kernel now give
\[
 |S(y)|\ll_{\rho,B}\sqrt y,\qquad
 \left|yS'(y)\right|
 =\left|\sum_{y<n<e^By}a(n)\frac{y}{n}\right|
 \ll_{\rho,B}\sqrt y .
\tag{7}
\]
The derivative is taken almost everywhere, since the locally finite kernel sum is continuous and piecewise \(C^1\). The inequalities also hold in \(0<y<1\) using zero support below \(e^{-B}\) and boundedness on the remaining compact interval.

By (4) and (7), the supremum plus total variation of \(W_{x,U}(t)\) on any interval in \([T,2T]\) is
\[
 O_{\rho,B}\!\left(1+\sqrt{x/T}\sqrt U\log(2U)\right).
\]
Partial summation with (6), then dyadic summation over \(Q<p\le P\le x\), yields
\[
 \left|\sum_{Q<p\le P}a(p)\log p\,W_{x,U}(p)\right|
 \ll_{\rho,B,\epsilon}
 x^{1/2+\epsilon} P^{\beta_*-1/2}\qquad(x\ge Y,\ U=Y^{o(1)}),
\tag{8}
\]
where the threshold for \(Y\) depends on the chosen \(U\). This compares signed weights while preserving their arithmetic values in the terms that survive.

Choose \(P=x^\alpha\) with \(1/2<\alpha<1\) fixed. One can instead keep \(P=Y^\alpha\) constant throughout a window starting at \(Y\), with the corresponding \(h\)-support. The difference of the two observables \(C_{0,B}\) and
\[
 R_\alpha(x)=-\frac14\sum_{x^\alpha<p\le e^Bx/(U+1)}
      a(p)\log p\sum_{U<h\le e^Bx/p}\beta_U(h)K_B(hp/x)
\tag{9}
\]
is \(O_{\rho,B,\epsilon}(x^{c_\alpha+\epsilon})\), where \(c_\alpha=1/2+\alpha(\beta_*-1/2)\). Under RH for \(L\) this is square-root size with an arbitrary epsilon. If \(\beta_*>1/2\), then \(c_\alpha<\beta_*\). The absolute difference of the weighted positive integrals is \(O(X^{c_\alpha-1/2+\epsilon}\log X)\) for a window ending at \(X\). This is smaller by a fixed power than the positive integrals for \(C_{0,B}\) on the windows where the original rightmost-zero rate holds. The inequality \(|v_+-w_+|\le|v-w|\) transfers that rate and the square-root subpower criterion to (9). For example the proportional log windows follow from the generic Landau criterion. The transform is \(H_B(s)L'(s)/(4L(s))\) up to the entire initial-interval term, \(H_B\) is nonzero in the critical strip, and every real strip-zero residue is positive. The same argument works on shorter windows whenever the original rightmost-zero rate is available there. [Pinned rightmost-rate argument](https://github.com/Sodelin/Research-Commons/blob/25fb33dfbbc5cabe79f039f741636e69ead590f5/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/window-rightmost-zero-rate.md)

## Polylogarithmic complementary factors when the top line is attained

Keep \(U\) fixed. In (6) one can use the bound
\[
 A(t)\ll_{\rho} t^{\beta_*}\log^3(3+t).
\tag{10}
\]
If \(\beta_*<1\), take the line \(\sigma=\beta_*+1/\log z\) in the same Perron argument, for \(z\) sufficiently large that \(\sigma<1\). Every zero in the local logarithmic-derivative formula is separated horizontally by \(1/\log z\) or more, uniformly throughout this shifted contour. The local count is \(O_\rho(\log(3+|\Im s|))\), so the uniform derivative bound on the contour is \(O_\rho(\log z\log(3+|\Im s|))\). The vertical integral costs \(\log^3(3+z)\) at height \(z^2\), while \(z^\sigma=e z^{\beta_*}\). The horizontal and truncation errors are smaller. Chebyshev suffices if \(\beta_*=1\).

One can replace the exponent \(1/2\) in (7) by \(1/3\). For a fixed planar lattice and disk radius \(R\ge1\), majorize and minorize the disk indicator by the indicators of the disks of radius \(R\pm d\), convolved with a nonnegative smooth unit-mass mollifier supported in the disk of radius \(d=R^{-1/3}\). The zero Fourier modes give area error \(O(Rd)\). The nonzero Fourier transform of either disk has size \(O(R^{1/2}|\xi|^{-3/2})\) by the \(J_1\) formula, and the mollifier inserts \(O_N((1+d|\xi|)^{-N})\) for each \(N\). Summing over the fixed dual lattice costs \(O(R^{1/2}d^{-1/2})\) by the lattice bound \(O((1+r)^2)\) on points in a disk of radius \(r\). Thus the count has discrepancy \(O(R^{2/3})\), with the bounded range of \(R\) covered separately. Equation (3) again cancels the area main terms. For \(y=R^2\), this gives the asserted \(O(y^{1/3})\) bounds on \(S\) and its log derivative. [Disk Fourier transform and Bessel bound, DLMF §§10.6 and 10.17](https://dlmf.nist.gov/10)

The dyadic variation argument with (10) now bounds the removed prime sector by
\[
 O_{\rho,B,U}\!\left(x^{1/3}P^{\beta_*-1/3}\log^3(3+x)\right)
 \qquad (Q<P\le x).
\tag{11}
\]
Since \(\beta_*\ge1/2\), the dyadic sum is geometric with a ratio bounded away from one. Set \(P=x/(\log x)^{20}\). Then (11) is \(O_{\rho,B,U}(x^{\beta_*}(\log x)^{-1/3})\). The surviving range is
\[
 \frac{x}{(\log x)^{20}}<p\le e^Bx/(U+1),\qquad U<h\le e^B(\log x)^{20}.
\]
If \(\beta_*>1/2\) is attained, the original positive-part window integral on every sufficiently long fixed log interval ending at \(X\) is \(\gg X^{\beta_*-1/2}\). The length and lower-bound constant can depend on \(L\) and \(B\). Estimate (11) and the root-scale error of (1) contribute \(o(X^{\beta_*-1/2})\) on these fixed log intervals, so the same lower bound holds for the surviving prime range. Under RH, (11) is within the square-root subpower budget regardless of attainment. This polylogarithmic restriction therefore transfers the fixed-log-window criterion under the attained-top hypothesis. [Pinned attained-line lower bound](https://github.com/Sodelin/Research-Commons/blob/e00069c40dd17f50a10f57bb76d7300c8f0e3cdf/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/rightmost-zero-short-log-windows.md)

These are hand proofs. The surviving prime sum's square-root upper-window bound remains open. There are no new numerical checks or Lean verifications.

The centered split-prime comparison also holds at the polylogarithmic cutoff above under verified Dirichlet GRH. Its partial-summation argument clips the weight at any prime threshold while retaining the matching integral reference. [Pinned centered comparison](https://github.com/Sodelin/Research-Commons/commit/1dcdd242401023541592d0126a999ae6cb43c8c5)
