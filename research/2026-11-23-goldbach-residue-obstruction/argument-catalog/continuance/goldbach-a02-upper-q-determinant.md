# A higher determinant cutoff on the upper \(q\) part of unmatched \(A_{02}\)

**Unconditional hand proof at each sufficiently large fixed \(N=2^k\).** In the pinned long reflected row keep all original parameters and tests, including \(U=V=N^{1/10}\), \(D_q=\sqrt{N/q}/L^B\), \(Q\le q\le\min(\alpha,H/2)\), odd squarefree \(q\), \(H<h<N/q\), \((h,2q)=1\), and
\[
 qh+wbs=N,\qquad w>V\text{ prime},\quad b\le U,\quad bs>U,\quad wb>D_q.
\]
The signed weight on the further slice \(q\ge N^{49/100}\), \(wb\le N^{51/100}\), is \(O_A(N/L^A)\) for every fixed \(A>0\). Thus in this upper \(q\) range the exact reflected row may require \(wb>N^{51/100}\). The result keeps the original \(+\mu(h)\mu(b)\log h\log w\) signs and the actual prime \(w\). [Pinned adaptive reflected support](https://github.com/Sodelin/Research-Commons/blob/eb8764f7be7658e10cba6b942ad94bbd97ed81bc/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-unmatched-outer-adaptive-mobius.md).

## Trim, group, and smooth the exact support

Use the fixed-product divisor-moment argument in the complementary Poisson proof. Trim \(m=qh\) and \(n=N-m\) below \(N/L^C\), with a smooth transition up to \(2N/L^C\), at arbitrary log saving. On the retained support \(r=wb\le N^{51/100}\) implies \(s=n/r\ge N^{49/100}/L^C>U\). Hence \(bs>U\) is automatic and \(r\) has coefficient \(\sum_{wb=r,b\le U,w>V\ {\rm prime}}\mu(b)\log w=O(L)\). Open the squarefree \(q\) and coprimality masks on \(q,h\) using \(d^2\mid q\), \(c\mid(q,h)\) with odd \(d,c\le L^{C_1}\). The discarded terms require a square divisor \(j^2\mid m\) with \(j>L^{C_1}\), hence lie over \(O(N/L^{C_1})\) products. Cauchy–Schwarz with the fixed moments of \(\tau(m)\tau(n)\) absorbs both the original and truncated arithmetic weights. Put \(E=[d^2,c]\le L^{3C_1}\), and keep \(c\mid h\) in the signed \(h\) coefficient. [Fixed-target tails, zero mode and odd progression](https://github.com/Sodelin/Research-Commons/commit/da2d8b33d1d17fda62722507cde8ac66a470e0e3).

Use dyadic boxes \(q\asymp X,\ h\asymp Y,\ r\asymp R\). On a contributing box \(N/L^C\ll XY\ll N\), \(X\ge N^{49/100}/2\), \(Y\le 2N^{51/100}\), and \(R\le N^{51/100}\). Leave \(h>H\) and \(r\le N^{51/100}\) sharp in their coefficients. As \(q h+r s=N\) and \(n>0\), the upper cut \(h<N/q\) is automatic. Smooth the fixed \(q\) edges, including \(N^{49/100}\) and \(\alpha\), at scale \(X/L^J\). The moving \(q\) edge from \(r>D_q\) occurs at \(q=N/(r^2L^{2B})\), for which \(R\ll N^{51/200}\ll X\) on a box it intersects. Smooth it on the same scale. Equivalently multiply the smooth \(q\) weight by a transition in \(\log q+2\log r-L+2B\log L\) of width \(L^{-J}\). This description gives uniformly polylogarithmic normalized derivatives also in \(r/R\).

For \(R\le X\), including the moving edge, each \(r\) has \(O(X/L^J+1)\) possible changed \(q\)'s. At fixed \(q,r\), \(h\) lies in one class modulo \(r\), so the changed placements are
\[
 O((X/L^J+1)(Y+R))=O(N/L^J+N^{51/100}).
\]
The residue class is reduced because a common odd factor would divide \(N\). For \(R>X\) only fixed \(q\) edges are active. Fix such a changed \(q\) and \(s\le N/R\), and count \(r\asymp R\) in its reduced class modulo \(q\), giving
\[
 O((X/L^J+1)(N/R)(R/X+1))=O(N/L^J+N^{51/100}).
\]
The case \(X,R\) within a fixed factor is covered by either bound after enlarging the constant. The discarded products and their original/log mask weights are thus negligible by the same fixed divisor-moment bound. This step counts the exact moving-edge discrepancy before applying any nonzero-frequency estimate.

## Bettin–Chandee on the retained frequencies

At fixed odd \(h,r\), the exact equation forces \((Eh,r)=1\). Put \(q=E(2j+1)\). The residue for \(j\bmod r\) is \((N/2)\overline{Eh}-\overline2\). Poisson in \(j\) has phase
\[
 (-1)^\nu e\bigl(\nu (N/2)\overline{Eh}/r\bigr),\qquad e(t)=e^{2\pi i t},
\]
after changing the integral variable to \(q/X\): the factor \(e(-\nu\overline2/r)\) is \((-1)^\nu e(-\nu/(2r))\), and its latter factor cancels the translation phase from the integral. Set \(T_0=2ER/X\). The normalized integral at \(x=h/Y,y=r/R\) consists of the smooth \(q\) edge tests, the two endpoint product masks and
\[
 \frac1{T_0 y}e\!\left(-\frac{\nu u}{T_0 y}\right),\qquad u=q/X.
\]
Derivatives in \(u,x,y\) of the real masks cost only powers of \(L\), including the original moving edge. By integration by parts in \(u\), the frequencies \(|\nu|>T_0 N^\eta\), for a sufficiently small fixed \(\eta>0\), have total power-saving error. This follows from \(O_j(L^{C_j}T_0^{j-1}|\nu|^{-j})\) per position, uniformly also when \(T_0N^\eta<1\).

For a retained dyadic frequency block \(|\nu|\asymp T\), perform three-variable partial summation in \(x,y,\nu/T\). The normalized derivative bound for the integral is \(O(T_0^{-1}N^{O(\eta)}L^{O(1)})\). The dyadic prefixes in \(h,r,\nu\) are absorbed by zeroing the corresponding coefficients. The \(Eh\) coefficient is \(\mu(h)\log h\) with the fixed odd and \(c\mid h\) tests; its norm is \(O(L\sqrt Y)\). The \(r\) coefficient has norm \(O(L\sqrt R)\), and \((-1)^\nu\) contributes norm at most \(O(\sqrt T)\). The only joint arithmetic test is the primitive condition \((Eh,r)=1\) in the trilinear theorem. Treat the two frequency signs separately.

Apply [Bettin–Chandee, Theorem 1, equation (1.2)](https://arxiv.org/pdf/1502.00769) at scales \(M\asymp EY,\ R,\ T\), with phase parameter \(N/2\) in absolute value. The phase factor is \((1+(N/2)T/(MR))^{1/2}=N^{O(\eta)}L^{O(1)}\), by \(T\le T_0N^\eta\) and \(XY\gg N/L^C\). The prefactor from amplitude and norms is
\[
 T_0^{-1}\sqrt{YRT}
 \ll \sqrt{XY}\,N^{\eta/2}\ll N^{1/2+\eta/2}.
\]
The polylogarithmic mask periods fit in \(N^{o(1)}\). Up to \(N^{O(\eta)+o(1)}\), \(M,R\le N^{.51}\), \(T\le N^{.02}\), hence \(TMR\le N^{1.04}\). The theorem's two terms, including the leading \(N^{1/2}\), have exponents
\[
 \frac12+\frac{7}{20}(1.04)+\frac14(.51)=.9915,
 \qquad
 \frac12+\frac38(1.04)+\frac18(.02+.51)=.95625 .
\]
Choose \(\eta\) and the theorem's arbitrarily small exponent loss below this fixed slack. This proves power saving after summing the logarithmically many boxes and masks. The moving cutoff is present only in the smooth coefficient dependence already handled by partial summation.

At \(\nu=0\) the kernel has factor \(X/(2Er)\), with polylogarithmic size and variation in \(h/Y\). The same uniform Davenport prefix for \(\mu(h)\mathbf1_{(h,2r)=1,c\mid h}\) used in complementary Poisson applies, since \(r\) remains polynomial and \(Y\gg H\). Partial summation and \(XY\ll N\) give arbitrary logarithmic savings after all masks. Thus the zero mode, nonzero modes, original strict cuts and fixed-target tails all have the stated saving.

To combine the two signed estimates, use the complementary \(r\le qN^{-\varepsilon}\) deletion only for \(q<N^{49/100}\), and the present \(r\le N^{51/100}\) deletion above that \(q\) threshold. These are disjoint subregions of the existing long reflected sum. The exact remaining signed lower bound, and the full powers-of-two ledger, stay open. This is a hand proof with no new Lean check.
