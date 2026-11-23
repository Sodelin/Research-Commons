# A square-root Type I bound for the degree-two dilation window

This hand argument applies to the conductor-23 standard \(S_3\) Artin factor and to a fixed tempered cuspidal standard \(L\)-function on \(\mathrm{GL}_2/\mathbb Q\), including Ramanujan's \(\Delta\). It uses no zero hypothesis. Work without damping, so the target exponent is exactly \(1/2\).

Let \(L(s)=\sum_n a(n)n^{-s}\) be such a degree-two factor with its unitary normalization. Write \(L(s)^{-1}=\sum_m\mu_L(m)m^{-s}\) in \(\Re s>1\). At each prime the inverse is a polynomial of degree at most two with unit-disc Euler roots, including at ramification. Thus \(|\mu_L(m)|\le\tau(m)\), and
\[
\Lambda_L(k)=\sum_{mn=k}\mu_L(m)a(n)\log n.
\]
For fixed \(B>0\), set
\[
K_B(t)=e^{-B}(e^B/t-1)_+-(1/t-1)_+.
\]
It equals \(1-e^{-B}\) on \(0<t\le1\), \(t^{-1}-e^{-B}\) on \(1<t\le e^B\), and zero above \(e^B\). The exact arithmetic-reference subtraction in the undamped degree-two window gives
\[
C_{0,B}(x)=-\frac14\sum_{m,n\ge1}\mu_L(m)a(n)\log n\,K_B(mn/x).
\tag{1}
\]
For a dual-closed family, the right side is summed over its members and \(1/4\) is replaced by \(1/(2d)\), where \(d\) is the total degree. [Pinned definition of the arithmetic reference and normalization](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md#positive-count-and-fixed-reference-subtraction)

For \(y\ge1\), Mellin inversion gives the inner sum
\[
\sum_n a(n)\log n\,K_B(n/y)
=\frac1{2\pi i}\int_{(2)}-L'(s)\,y^s
\frac{e^{(s-1)B}-1}{s(s-1)}\,ds.
\tag{2}
\]
The factor in the numerator makes the kernel regular at \(s=1\). To shift to \(\Re s=\epsilon>0\), fix \(0<\epsilon<1/4\) and put \(a_0=\epsilon/8\). Absolute Euler convergence bounds \(L\) on \(\Re s=1+a_0\). The functional equation with degree-two gamma factors and Stirling bounds \(L(-a_0+it)\) by \(O_{L,a_0}((1+|t|)^{1+2a_0})\). Phragmén–Lindelöf across this strip gives the exponent \(1+a_0-\Re s\). Applying Cauchy's formula in discs of radius at most \(a_0\) gives \(L'(s)=O_{L,\epsilon}((1+|\Im s|)^{1-3\epsilon/4})\) on the portion \(\epsilon\le\Re s\le2\), using absolute convergence separately near and to the right of \(1+a_0\). The kernel in (2) decays as \((1+|\Im s|)^{-2}\) on these lines at large height, so the horizontal integrals vanish and the shifted vertical line is absolutely integrable. No pole is crossed. Hence the inner sum is \(O_{L,\epsilon}(y^\epsilon)\), uniformly for \(B>0\). The shifted line has \(\Re s=\epsilon<1\), so the numerator of the kernel has magnitude at most \(2\). The contour shift itself is justified at each fixed \(B\). [Standard automorphic analytic input](https://doi.org/10.1007/BFb0070263) [Artin induction](https://doi.org/10.1007/BF02941010) [Hecke analytic input](https://sites.math.rutgers.edu/~alexk/2023S572/Tate1950.pdf)

It follows from \(\sum_{m\le M}\tau(m)m^{-\epsilon}\ll_\epsilon M^{1-\epsilon}\log(2M)\) that the part of (1) with \(m\le M\le x\) is
\[
O_{L,B,\epsilon}\bigl(x^\epsilon M^{1-\epsilon}\log(2M)\bigr).
\tag{3}
\]
In particular \(M\le\sqrt x\) gives \(O_{L,B,\epsilon}(x^{1/2+\epsilon})\), after reducing \(\epsilon\) in (2) to absorb the logarithm. One may keep a fixed \(M=\lfloor\sqrt Y\rfloor\) throughout a window starting at \(Y\).

The exact remaining signed sum is
\[
R_{B,M}(x)=-\frac14\sum_{n\le e^B x/(M+1)}a(n)\log n
 \sum_{M<m\le e^B x/n}\mu_L(m)K_B(mn/x).
\tag{4}
\]
It includes the long inverse-coefficient ranges as well as balanced pairs. There is no change of the dilation support or of the signs. For a self-dual factor or a dual-closed family, the window statistic is real. On \([Y,Y^b]\) with fixed \(b>1\), choose the \(\epsilon\) in (3) small enough relative to \(\eta/b\). Then the removed part contributes at most \(O(Y^{\eta/2}\log Y)\) to the absolute window integral with weight \(x^{-1/2}dx/x\). Since \(|v_+-w_+|\le|v-w|\), the same one-sided subpower window criterion holds for (4) if and only if it holds for (1). The same comparison applies on shorter windows. The bound in (3) is a hand proof. The required estimate for (4) remains open. These deductions have no new Lean verification or numerical input.
