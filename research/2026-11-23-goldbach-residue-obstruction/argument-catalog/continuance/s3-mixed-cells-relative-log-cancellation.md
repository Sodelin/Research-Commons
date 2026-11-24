# Relative signed cancellation in fixed \(S_3\) mixed cells

Keep the exact locked companion, prime, and separation cutoffs from the mixed prime–composite cells. Thus \(U=\lfloor Y^u\rfloor\), \(P=Y^\alpha\), \(0<u<1/2\), \(X=Y^{1+o(1)}\), and the companions lie in \((U,2U]\), are squarefree and \((\log X)^2\)-rough, and satisfy the actual gap test \(k-h>H_0=X^{o(1)}\). Within one hard cell \(I\), retain exactly one prime and one composite companion. This ensures coprimality automatically. [Exact mixed cell and atom masks](https://github.com/Sodelin/Research-Commons/commit/e00455911f112aa1df810b4a5fdd1285f324246a)

Write \(P_I,N_I\) for the positive mass and the magnitude of the negative mass of this exact signed cell covariance. For every \(A>0\),
\[
 |P_I-N_I|\ll_A \frac{\min(P_I,N_I)}{(\log X)^A}.
\tag{1}
\]
This holds with both the original centered atom convention and the one excluding atoms dividing \(hk\) and coincident discrete atoms. It applies to each full cell chosen by the original shift tolerance, of subpower-relative size \(Q=UX^{-o(1)}\). It also holds uniformly for any prescribed hard cell of length \(Q=X^\tau\) with
\[
 \max\{5u/6,\ u-\alpha/4\}<\tau<u .
\tag{2}
\]
The argument covers the actual zero supremum \(\beta_*=1\), including nonattainment. It only compares the signed covariance with its sign masses in these cells.

## Class counts and the signed prime prefix

For the fixed \(S_3\) splitting field of degree six, Balog–Ono's short-interval Chebotarev theorem gives every class its main term on every interval of length \(J\ge T^{5/6+\delta}\) at height \(T\), for fixed \(\delta>0\). The proof gives any prescribed logarithmic saving for the weighted error on this strict subrange. Namely in their equation (3.2) take the zero truncation height \(T_1=T(\log T)^{A+3}/J\). The truncation error is \(O(J/\log^{A+1}T)\), and their zero density bound has \(T_1^{6+\eta}/T\le T^{-c(\delta)}\) for small \(\eta>0\). Their zero-free region then gives the same stretched-exponential estimate as in their equation (3.4). The finitely many small ordinates are separated from \(\Re s=1\) for this fixed field. Proper powers contribute \(O(\sqrt T\log^2 T)\), absorbed by this range. Thus the logarithmically weighted prime count has class-density main term and \(O_A(J/\log^A T)\) error. [Balog–Ono, Theorem 2 and equations (3.2)–(3.5)](https://uva.theopenscholar.com/files/ken-ono/files/062.pdf)

The trace \(a(p)\) has class mean zero. This gives within each stated cell the unweighted sharp prefix
\[
 \sup_{t\in I}\left|
   \sum_{\substack{q\in I,\ q\le t\\q\ {\rm prime}}}a(q)\right|
       \ll_A Q/(\log U)^A.
\tag{3}
\]
For subinterval lengths at least \(U^{5/6+\delta}\), use the weighted estimate and partial summation with \(1/\log q\). Shorter subintervals cost \(O(U^{5/6+\delta}\log U)\) trivially, and fit (3) on choosing \(\delta\) below the fixed exponent margin in (2), or a fixed small \(\delta\) for subpower-relative cells.

Choose one split prime \(q_0\in((\log X)^2,2(\log X)^2]\). The first third of the cell contains \(\asymp Q/\log U\) split prime companions \(h\). The last third contains \(\asymp Q/(q_0\log U)\) composite companions \(k=q_0r\) of either of two types, according as \(r\) is a three-cycle prime or a split prime. Apply short-interval Chebotarev to the scaled interval at height \(U/q_0\). The two thirds ensure \(k-h>H_0\), and the factors \(q_0,r\) are distinct and exceed the roughness cutoff for large \(X\). On \((U,2U]\) the inverse coefficient is exactly \(\beta_U=\mu_L\). Therefore \(\beta_U(h)=-2\), and \(\beta_U(k)=-2\) or \(+4\), respectively. This is a pair count on the required support for each sign.

## Signed Hilbert-space comparison

Write \(f_h(v)=g_P(v-\log h)\) on the original window. Choose \(h_I\in I\) and put \(A_I=\|f_{h_I}\|_2\). In the off-line case \(\beta_*>1/2\), the shift tolerance defining the subpower-relative cells makes \(\int_I\|\partial_h f_h\|_2dh\le A_I/4\). The same holds for (2), since a fixed polynomial relative shift is smaller than that tolerance. It follows that \(\|f_h\|_2\asymp A_I\), that \(\langle f_h,f_k\rangle\gg A_I^2\) for every two companions in the cell, and that the supremum plus total variation in \(L^2\) of \(h^{-1/2}f_h\) is \(O(A_I/\sqrt U)\). [Relative-shift tolerance and lower norms](https://github.com/Sodelin/Research-Commons/commit/371ff8bc2032a4a70c0db9a4ed3b81eece58bb52)

At \(\beta_*=1/2\), the previous critical-line formula gives \(A_I\asymp\sqrt{V-v_0}\) and the same kernel lower bound on the chosen relative cells. For total variation one can use \(|g'_P|\ll(\log X)^C\) on the active band. This follows from truncated Perron for the Artin and Dirichlet logarithmic prime prefixes on \(1/2+1/\log t\), after their principal terms are removed. The local logarithmic derivative costs \(O((\log t)\log(3+|\Im s|))\), and the higher powers cost at most an additional logarithmic factor. This gives the standard square-root times polylogarithmic prime-prefix bound, then the differentiated \(K_B\) identity bounds \(g'_P\). Thus \(h^{-1/2}f_h\) has the same \(L^2\) variation bound up to a fixed logarithmic power, which is absorbed in (3).

Abel summation of the prime-companion scalar, using (3) and this variation, gives
\[
 \|S_{\rm pr}\|_2\ll_A \frac{QA_I}{\sqrt U(\log U)^A}.
\]
For the composite scalar use \(|\beta_U(h)|\le d_2(h)\) on \((U,2U]\). Counting the smaller factor in each factorization gives \(\sum_{h\in I}d_2(h)\ll Q\log U+\sqrt U\), so
\[
 \|S_{\rm co}\|_2\ll \frac{QA_I\log U}{\sqrt U}.
\]
The resulting all-mixed-pairs value is \(2\langle S_{\rm pr},S_{\rm co}\rangle\ll_A Q^2A_I^2/(U(\log U)^A)\), after increasing the exponent in (3). The selected first-third and last-third strata contribute at least \(Q^2A_I^2/(Uq_0(\log U)^2)\) to each sign mass. This gives the claimed logarithmic ratio at the all-pair level.

## Comparison on the actual separated and masked pairs

Close pairs cost a fixed power below the selected mass even within one cell. Their number is \(O(QH_0)\), their normalized weights cost \(U^{-1}X^\varepsilon\) by the divisor bound, and their kernel has absolute size \(O(A_I^2)\), with at most a logarithmic factor after atom masking at the critical line. Compare with the selected count of order \(Q^2/(q_0(\log U)^2)\). Since \(Q\) exceeds a fixed positive power of \(X\), the logarithmic ratio is preserved.

In an off-line case the individual divisor and coincidence masks are negligible relative to the original kernel in each selected pair, by the per-pair comparison in the mixed-cell proof. At the critical line the coincidence subtraction instead reverses the sign of each selected kernel and enlarges its magnitude by a factor of order \(\log X\), so there are still selected positive and negative masses with at least the displayed lower size.

For clarity on the signed atom comparison in a polynomial cell, put \(\Delta=\beta_*-1/2\). The previous exact mixed atom sums are
\[
 O_\varepsilon\!\left(
 X^{(1+u)\Delta+\varepsilon}
 +X^{(2-\alpha)\Delta+\varepsilon}
 +X^{2u-1+\varepsilon}\right)
\]
when \(\Delta>0\). The first term is the same-coordinate divisor cost. The second uses the crossed-mask or coincident-atom tail at \(p>P\), whose exponent saving is at least \(P^{-\Delta+\varepsilon}\) from \(p^{-2\beta_*+\varepsilon}\) or \(p^{-\beta_*-\sigma+\varepsilon}\), \(\sigma>1/2\). The last is the intersection cost. At \(\Delta=0\), all these signed errors are subpower. The selected sign exponent for a polynomial cell is \(2\tau-u+2(1-u)\Delta\). It exceeds the first atom exponent because \(\tau>5u/6\), \(u<1/2\) and \(0<\Delta\le1/2\). It exceeds the second by the bound \(\tau>u-\alpha/4\), and it exceeds the last since \(2u-1<0\). For the original subpower-relative cells replace \(\tau\) by \(u+o(1)\), yielding the same strict gaps. Thus the signed atom and close corrections do not affect (1). No support is averaged over its position.
