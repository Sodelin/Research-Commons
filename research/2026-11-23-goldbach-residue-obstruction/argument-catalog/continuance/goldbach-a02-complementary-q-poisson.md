# Complementary Poisson removal in the long reflected \(A_{02}\) row

**Unconditional hand proof at every sufficiently large fixed \(N=2^k\).** Use the pinned unmatched reflected row with \(L=\log N\), \(H=\sqrt N\), \(Q=N^{1/4}\), \(\alpha=H/L^{K_0}\), \(U=V=N^{1/10}\), and \(D_q=\sqrt{N/q}/L^B\). Keep \(Q\le q\le\min(\alpha,H/2)\), odd squarefree \(q\), \(H<h<N/q\), \((h,2q)=1\), and
\[
 qh+wbs=N,\quad w>V\text{ prime},\quad b\le U,\quad bs>U,\quad wb>D_q .
\]
The signed weight is \(+\mu(h)\mu(b)\log h\log w\). For every fixed \(0<\varepsilon<1/4\) and \(A>0\), the further slice with \(wb\le qN^{-\varepsilon}\) has signed weight \(O_{A,\varepsilon}(N/L^A)\). Both original strict inequalities remain in the sum. This is a complementary signed charge in the already reflected arithmetic sum, with its same fixed parameters. [Pinned adaptive Möbius cutoff and reflection](https://github.com/Sodelin/Research-Commons/blob/eb8764f7be7658e10cba6b942ad94bbd97ed81bc/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-unmatched-outer-adaptive-mobius.md).

## Exact grouping and fixed-target tails

Put \(m=qh\), \(n=N-m\), and \(r=wb\). At each fixed \(m\), the number of \(q,h,w,b,s\) placements is at most \(\tau(m)\tau(n)^2\); all logarithmic weights are at most \(L^2\). Multiplying the weight by any of the finite divisor mask expansions used below costs at most fixed extra powers of \(\tau(m)\tau(n)\). For an exceptional set of \(K\) products on either side, fixed divisor moments and Cauchy–Schwarz therefore give an absolute upper bound \(O(\sqrt{KN}L^{C_0})\), with a constant \(C_0\) depending only on these powers. This is pointwise in \(N\). In particular remove the parts \(m\) or \(n\le 2N/L^C\) at arbitrary log saving, choosing fixed \(C\) large. Use smooth masks in \(m,n\), vanishing below \(N/L^C\) and equal to one above \(2N/L^C\), with derivatives on that scale. On their support \(s=n/r\gg H/L^C>U\), as \(r\le qN^{-\varepsilon}\le H\). Thus \(bs>U\) is automatic in the grouped sum.

The grouped index coefficient is exactly
\[
 c(r)=\sum_{\substack{wb=r,\ w>V\text{ prime}\\b\le U}}\mu(b)\log w,
\]
of magnitude at most \(\log r\). The signs left in the equation \(qh+rs=N\) are \(+\mu(h)c(r)\). Open the exact squarefree \(q\) and \((q,h)\) tests into \(d^2\mid q,\ c\mid q,\ c\mid h\), with coefficients \(\mu(d)\mu(c)\). Here \(d,c\) are odd. Truncate both at \(L^{C_1}\) for fixed large \(C_1\). If a discarded \(d\) occurs then \(d^2\mid m\); if a discarded \(c\) occurs then \(c^2\mid m\). There are \(O(N/L^{C_1})\) such products, by summing \(N/j^2\) over \(j>L^{C_1}\). The preceding fixed-target moment bound absorbs the entire truncated or untruncated weight on these products at arbitrary log saving. The resulting progressions are \(q=E(2j+1)\) with \(E=[d^2,c]\le L^{3C_1}\), and the \(h\) coefficient retains the test \(c\mid h\) and oddness. This keeps all original squarefree factors and coprimality after the negligible tails.

## The moving cut on \(q\)

For fixed \(r\) the two added inequalities are precisely the \(q\)-only cutoffs
\[
 q>\frac{N}{r^2 L^{2B}},\qquad q\ge rN^\varepsilon .
\]
Use dyadic scales \(q\asymp X,\ h\asymp Y,\ r\asymp R\), intersecting the original \(q\) and \(h\) intervals. The original \(H<h<N/q\) keeps its sharp lower endpoint. The upper endpoint is automatic from \(s\ge1\), enforced by the equation and the positive \(n\) mask. In a contributing box \(XY\ll N\), \(Y\ll N^{3/4}\), and \(r\ll X N^{-\varepsilon}\). Smooth the \(q\) intervals separately at each \(r\), with transition width \(X/L^J\), keeping the strict arithmetic endpoints through the error estimate. A changed integer \(q\) is within this width of a bounded number of boundaries, including the two moving ones above. At each \(r\) there are \(O(X/L^J+1)\) changed positions. For a position with a solution, \((q,r)=1\) because \(q,r\) are odd and \(N\) is a power of two. The congruence places \(h\) in one residue class modulo \(r\), with \(O(Y/r+1)\) positions in its actual interval. Thus, before multiplier weights, the exceptional pairs cost at most
\[
 O\!\left((X/L^J+1)\sum_{r\ll XN^{-\varepsilon}}(Y/r+1)\right)
 =O\!\left(NL^{1-J}+N^{1-\varepsilon}+N^{3/4}L\right).
\]
The fixed-target divisor moments absorb their full weights, including opened mask multiplicities, after choosing \(J\) large and allowing the logarithmically many boxes. This argument handles the moving lower edges without introducing a boundary depending on a new additive target.

## Small-frequency Poisson and the signed zero mode

At fixed odd \(h,r\) a contribution forces \((Eh,r)=1\). The progression \(q=E(2j+1)\) has one residue for \(j\bmod r\). Poisson in \(j\) has frequency scale \(T_r=2Er/X\ll L^{3C_1}N^{-\varepsilon}\). Its amplitude is \(T_r^{-1}\) times the integral of the normalized smooth \(q\) weight against \(e(-\nu u/T_r)\), where \(u=q/X\). The \(m,n\) masks occur as smooth functions of \(X u h\) and \(N-X u h\) on scale \(N/L^C\). Because \(XY\ll N\), all fixed derivatives in \(u\) and \(h/Y\) are fixed powers of \(L\), uniformly in \(h,r\) and in the location of the smoothed \(q\) interval. For every fixed \(j_0\ge2\), integration by parts gives the explicit nonzero bound
\[
 O_{j_0}\!\left(L^{C(j_0)}T_r^{\,j_0-1}|\nu|^{-j_0}\right).
\]
The accompanying progression phase has modulus one. Choose \(j_0\) in terms of \(\varepsilon,A\). Summing this bound over nonzero integers, over all \(r,h\) positions, over the dyadic boxes and the polylogarithmically many \(d,c\), gives a fixed power saving, hence arbitrary log savings. This estimate does not need trilinear Kloosterman cancellation.

At zero frequency the integral retains the factor \(X/(2Er)\); its normalized size and variation as \(h/Y\) varies are log-power bounded. The remaining arithmetic prefix has coefficient \(\mu(h)\) and tests \((h,2r)=1,\ c\mid h\). Uniformly for subintervals of the actual \(h\) interval at scale \(Y\), its sum is \(O_{A'}(Y/L^{A'})\) for every fixed \(A'>0\). One can verify this by \(\mu(h)\mathbf1_{(h,2r)=1}=(\mu*g_{2r})(h)\), where \(g_{2r}(t)\) is the indicator of prime support dividing \(2r\). Use additive Fourier for \(c\mid h\) with norm one. On \(t\le Y^{1/2}\), Davenport applies uniformly to the \(\mu\) prefix at length at least \(Y^{1/2}\) with the resulting additive phase. Its reciprocal coefficient norm is \(\ll L^{O(1)}\). The tail \(t>Y^{1/2}\) costs \(Y^{3/4+o(1)}\), since \(\sum_{t>Y^{1/2}}g_{2r}(t)/t\le Y^{-1/4}\prod_{p\mid2r}(1-p^{-1/2})^{-1}\) and the product is \(N^{o(1)}\) uniformly for \(r\le H\). Sharp endpoints \(h>H\) and dyadic \(h\) bounds are difference-of-prefix tests. If a sharp endpoint on \(h\) from \(qh<N\) is used instead of the positive \(n\) mask, the smooth \(q\) integrand already vanishes there. Thus no continuation of a prefix past its prescribed endpoint is needed. [Davenport's uniform Möbius estimate](https://doi.org/10.1093/qmath/os-8.1.313).

Partial summation in \(h\) now handles the original \(\log h\) weight and the zero-frequency kernel. At fixed \(r\) this gives \(O_{A'}(XY/(Er L^{A'}))\) after increasing the prefix saving to absorb all log factors. Restoring \(c(r)=O(L)\), summing over dyadic \(r\) and the polylogarithmically many masks preserves arbitrary log savings since \(XY\ll N\). Along with the nonzero bound and fixed-target tails, this proves the complementary charge.

The two small-index estimates act on different variables and can be placed in disjoint order. After the pinned removal of \(r\le D_q\), the present result removes \(D_q<r\le qN^{-\varepsilon}\). In particular the remaining signed row may require \(wb>\max(D_q,qN^{-\varepsilon})\) with negligible error. This additional range is present on upper \(q\) exponents above \(1/3+2\varepsilon/3\). The latter reflected long row retains its original two Möbius signs and actual prime \(w\).

This also gives a uniform cutoff. On the remaining sum,
\[
 (wb)^3>D_q^2\,qN^{-\varepsilon}
             =\frac{N^{1-\varepsilon}}{L^{2B}} .
\]
Thus \(wb>N^{(1-\varepsilon)/3}/L^{2B/3}\) and the actual prime satisfies \(w>N^{7/30-\varepsilon/3}/L^{2B/3}\), since \(b\le U\). For any fixed sufficiently small \(\delta>0\), using \(\varepsilon=\delta\) allows the weaker, uniform requirement \(wb>N^{1/3-\delta}\) at no extra cost for large \(N\).
