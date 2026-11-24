# A variable determinant cutoff for the unmatched Goldbach outer row

**Unconditional hand proof at each sufficiently large fixed \(N=2^k\).** Use the pinned unmatched long reflected row and keep its original cuts, including \(L=\log N\), \(H=\sqrt N\), \(Q=N^{1/4}\), \(\alpha=H/L^{K_0}\), \(U=V=N^{1/10}\), and \(D_q=\sqrt{N/q}/L^B\). The exact equation and weight are
\[
 qh+wbs=N,\qquad +\mu(h)\mu(b)\log h\log w,
\]
with \(Q\le q\le\min(\alpha,H/2)\), odd squarefree \(q\), \(H<h<N/q\), \((h,2q)=1\), actual prime \(w>V\), \(b\le U\), \(bs>U\) and \(wb>D_q\). Write \(a=\log q/L\), and define
\[
 \kappa(a)=
 \begin{cases}
 a, & a\le 2/5,\\
 (19a-2)/14, & 2/5<a\le16/33,\\
 (3+14a)/19, & 16/33<a\le1/2 .
 \end{cases}
\]
For every fixed \(0<\varepsilon<1/20\) and \(A>0\), the signed subregion with
\[
 D_q<r=wb\le N^{\kappa(a)-\varepsilon}
 \tag{1}
\]
has weight \(O_{A,\varepsilon}(N/L^A)\). Thus the same long reflected row may retain \(wb>\max(D_q,N^{\kappa(a)-\varepsilon})\) with arbitrary logarithmic saving. The first branch is complementary small-frequency Poisson. The other two branches give genuinely larger cutoffs, including values closer to \(10/19\) on the upper \(q\) exponents. [Pinned exact reflected row](https://github.com/Sodelin/Research-Commons/blob/eb8764f7be7658e10cba6b942ad94bbd97ed81bc/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-unmatched-outer-adaptive-mobius.md).

## Fixed-target tails and smoothing the variable edge

At fixed \(m=qh\) the weight multiplicity is bounded by \(L^2\tau(m)\tau(N-m)^2\) before the divisor masks. Fixed moments and Cauchy–Schwarz give arbitrary log savings on \(m\) or \(n=N-m\) below \(2N/L^C\), for sufficiently large fixed \(C\). Insert smooth cutoffs vanishing below \(N/L^C\) and equal to one above \(2N/L^C\). Since \(r\le N^{10/19}\), one then has \(s=n/r\ge N^{9/19}/L^C>U\). Thus \(bs>U\) is automatic and the coefficient on \(r=wb\) is exactly
\[
 c(r)=\sum_{\substack{wb=r,\ b\le U\\w>V\ {\rm prime}}}\mu(b)\log w=O(L).
\]
Open squarefree \(q\) and the \((q,h)=1\) test by \(d^2\mid q\), \(c\mid q\), \(c\mid h\) with odd \(d,c\). Truncate them at \(L^{C_1}\). Their tails force a square divisor exceeding \(L^{2C_1}\) on \(m\), hence occur on \(O(N/L^{C_1})\) products. The same fixed moments absorb these tails, including both expanded divisor multiplicities. The resulting \(q\) period is \(E=[d^2,c]\), with \(E\le L^{3C_1}\), and the \(h\) side retains \(c\mid h\).

Use \(q\asymp X,h\asymp Y,r\asymp R\) boxes, with \(N/L^C\ll XY\ll N\), \(X\ll H\), \(Y\gg H\) and \(Y\ll N^{3/4}\). Keep \(h>H\) and the dyadic \(h,r\) intervals sharp. The condition \(h<N/q\) follows from the positive \(n\) mask. Split at the two exact \(q\)-values where the formula for \(\kappa\) changes. On each branch both bounds on \(r\) in (1) are \(q\)-only **affine inequalities in \(\log q,\log r\)**, with strictness inherited from (1). Smooth the fixed \(q\) cuts and the moving log cuts at normalized width \(L^{-J}\). The derivative bounds in \(q/X,r/R\) are fixed log powers. A changed point is within \(O(X/L^J)\) of a fixed \(q\)-edge at fixed \(r\). For a moving edge it is also within \(O(R/L^J)\) in \(r\) at fixed \(q\), since all branch slopes are bounded away from zero.

Here is a uniform fixed-target count for these changes, even when \(R\) crosses \(X\) or \(Y\).

* If \(R\le YL^K\), fix \(r\) and count \(O(X/L^J+1)\) changed \(q\)'s. Each such pair yields at most \(O(Y/r+1)\) values of \(h\) in the residue class modulo \(r\). A successful pair is coprime since \(q,r\) are odd and any common divisor would divide \(N\). The total is \(O(NL^{K-J}+N^{3/4}L^K)\).
* If \(R>YL^K\), then \(R\gg XL^K\). For a moving edge, fix \(q\) and \(s\le N/R\); \(r\) is in one reduced class modulo \(q\) and in the short edge interval. This gives \(O(X(N/R)(R/(X L^J)+1))=O(N/L^J+N/L^K)\). For a fixed \(q\)-edge instead count \(O(X/L^J+1)\) \(q\)'s, with \(s\le N/R\) and \(r\asymp R\) in its class modulo \(q\). The bound is \(O(N/L^J+N/X)\).

Choose \(K,J\) in that order large enough for the fixed-moment losses. For each case the number of affected fixed products is at most the indicated placement count. The original arithmetic weights, including the opened masks, are bounded by fixed divisor powers times log powers at each product. Thus Cauchy–Schwarz makes the smoothed discrepancy \(O_A(N/L^A)\) after summing all boxes. This argument preserves the two sharp sides of (1).

## One Poisson phase and the variable size bounds

At fixed \(h,r\), \(q=E(2j+1)\) solves
\[
 j\equiv(N/2)\overline{Eh}-\overline2\pmod r ,
\]
where \((Eh,r)=1\) is forced by the original equation and oddness. Poisson in \(j\) yields reciprocal phase \((-1)^\nu e(\nu(N/2)\overline{Eh}/r)\) after changing its integral to \(u=q/X\). The shift \(\overline2=(r+1)/2\bmod r\) gives \(e(-\nu/(2r))\), which is canceled by the translation in that integral. Put \(T_0=2ER/X\). The normalized amplitude is
\[
 \frac{1}{T_0 y}\int f(u,y)\,W_m(Xu h)\,W_n(N-Xu h)
                       e\!\left(-\frac{\nu u}{T_0 y}\right)\,du,
 \qquad y=r/R,
\]
where \(f\) holds all the smoothed \(q,r\) edges. The two endpoint masks have normalized derivatives bounded by powers of \(L\) since \(XY\ll N\). Integration by parts gives the uniform bound \(O_j(L^{C_j}T_0^{j-1}|\nu|^{-j})\). Thus the frequencies outside \(|\nu|\le T_0N^\eta\) may be discarded at a fixed power cost for any fixed small \(\eta>0\). This also handles the case \(T_0N^\eta<1\). In the first branch \(R\ll X N^{-\varepsilon}\) and all nonzero modes are then negligible.

For a retained frequency block \(|\nu|\asymp T\), separate the amplitude by partial summation in \(h/Y,r/R,\nu/T\). The mixed first derivatives are \(O(T_0^{-1} N^{O(\eta)}L^{O(1)})\), because only \(\nu/T_0\) appears in its oscillatory factor and the real masks have polylogarithmic derivatives. The resulting three prefix arrays have \(\ell^2\) norms \(O(L\sqrt Y)\), \(O(L\sqrt R)\), \(O(\sqrt T)\), including the fixed \(c\mid h\) condition and \((-1)^\nu\). The adjoining condition \((Eh,r)=1\) is exactly the primitive restriction of Bettin–Chandee. Separate the two signs of \(\nu\). [Bettin–Chandee, Theorem 1, equation (1.2)](https://arxiv.org/pdf/1502.00769).

In that theorem use scales \(M\asymp EY,R,T\) and phase parameter \(N/2\) in absolute value. Its phase amplification is \(N^{O(\eta)}L^{O(1)}\), since \((N/2)T_0/(MR)\ll N/(XY)\ll L^C\). The prefactor satisfies \(T_0^{-1}\sqrt{YRT}\ll\sqrt{XY}\,N^{\eta/2}\ll N^{1/2+\eta/2}\). Put \(a_0=\log X/L\) and \(b_0=\log R/L\); actual \(q,r\) exponents in these boxes differ by \(O(1/L)\). Then \(Y\ll N^{1-a_0}\), \(T\ll N^{b_0-a_0+\eta+o(1)}\), and the two nonzero terms, including the leading \(N^{1/2}\), have exponents up to \(O(\eta)+o(1)\)
\[
 F_1(a_0,b_0)=.85+.7(b_0-a_0)+.25\max(1-a_0,b_0),
\]
\[
 F_2(a_0,b_0)=.875+.875(b_0-a_0)+.125\max(1-a_0,b_0).
\]
For \(2/5\le a_0\le16/33\) use \(b_0\le(19a_0-2)/14-\varepsilon+O(1/L)\le1-a_0\). The first exponent is at most \(1-.7\varepsilon+o(1)\). The second is at most \(.875+.1875a_0+o(1)<.97\). For \(a_0\ge16/33\), both \(b_0\) and \(1-a_0\) are bounded by \((3+14a_0)/19+O(1/L)\), and \(b_0\) has the further \(\varepsilon\) saving. The first exponent is again at most \(1-.7\varepsilon+o(1)\), and the second at most \(.875+(3+14a_0)/19-.875a_0+o(1)<.97\). Boxes crossing a branch boundary are covered by its exact \(q\) cut and \(O(1/L)\) exponent loss. Choose \(\eta\) and the theorem's small exponent loss below this uniform strict slack. All nonzero frequencies thus have a power saving.

At zero frequency the kernel has factor \(X/(2Er)\) times a function with polylogarithmic normalized size and variation in \(h/Y\). The exact primitive condition leaves \((h,2r)=1\) in the \(\mu(h)\) prefix with the fixed test \(c\mid h\). The usual convolution with the indicator of integers supported on primes of \(2r\), followed by Davenport and additive Fourier for \(c\mid h\), gives arbitrary log-saving prefixes uniformly for \(Y\gg H\). This uses only \(r\le N^{10/19}\). Partial summation handles the actual \(\log h\) and the sharp \(h\) interval. Summing \(r\asymp R\), the mask periods and the boxes preserves arbitrary log savings since \(XY\ll N\). Together with the original fixed-target tails and the moving-edge estimate, this proves (1). [Davenport's uniform Möbius estimate](https://doi.org/10.1093/qmath/os-8.1.313).
