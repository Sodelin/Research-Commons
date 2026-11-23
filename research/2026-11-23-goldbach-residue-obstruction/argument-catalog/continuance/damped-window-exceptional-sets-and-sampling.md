# Exceptional sets and sampling for the original upper window

The original normalized observable can be tested outside power-saving exceptional sets or on grids with power-saving relative spacing. Neither result requires an attained rightmost zero. The proof also identifies the negative prime-prefix estimate that would suffice with such holes. These are hand consequences of the original smoothed explicit formula and the long-window rate. They leave the arithmetic input open. [Pinned original kernel](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md) · [Pinned long-window rate and exact threshold](https://github.com/Sodelin/Research-Commons/blob/a4f70e178b29f71ac91d8f29c14f89bb23209725/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/damped-window-threshold-and-prime-ideal-audit.md)

## An off-line zero forces large positive values on large sets

Write \(F(x)=x^\delta C_{\delta,B}(x)\) for the original normalized count of the fixed completed family \(H\), with \(0\le\delta<1/2\) and \(B>0\). Let \(\beta=\sup_\rho\Re\rho\) and suppose \(\beta>1/2\). The full smoothed explicit formula of the pinned note gives
\[
 F(e^u)=\sum_\rho b_\rho e^{\rho u}+O_{H,\delta,B}((1+u)e^{\delta u}),
 \qquad \sum_\rho|b_\rho|<\infty .
\]
A possible shift of a real zero to the kernel point \(s=0\) is already included in the remainder. Consequently \(|F(e^u)|\ll e^{\beta u}\) even if no zero is on \(\Re s=\beta\). [Pinned absolute explicit formula](https://github.com/Sodelin/Research-Commons/blob/e00069c40dd17f50a10f57bb76d7300c8f0e3cdf/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/rightmost-zero-short-log-windows.md)

Fix \(\kappa>0\), put \(V=(1+\kappa)U\), \(Y=e^U\), \(X=e^V\), and take the square-root exponent \(\theta=1/2\). The proved long-window rate gives
\[
 J(U)=\int_U^V F(e^u)_+e^{-\theta u}\,du
       =\exp\big((\beta-\theta)V+o(U)\big).
\]
Define \(E\) by \(F(e^u)e^{-\theta u}>J(U)/(2(V-U))\) within that interval. The complement contributes at most \(J(U)/2\). The envelope \(O(e^{(\beta-\theta)V})\) thus gives \(|E|\ge\exp(-o(U))\) in log measure. The envelope at each individual \(u\in E\) forces \(u\ge V-o(U)\), since \(\beta-\theta>0\). Hence \(F(e^u)\ge\exp(\beta V-o(U))\) on \(E\), and its image in \(x\) has ordinary measure at least \(\exp(V-o(U))\). In particular for every fixed \(\epsilon>0\), for all sufficiently large \(X\) there is a subset of \([X^{1/(1+\kappa)},X]\) of measure at least \(X^{1-\epsilon}\), lying at \(x\ge X^{1-\epsilon}\), on which \(F(x)\ge X^{\beta-\epsilon}\).

It follows that the following almost-all input would suffice for GRH of the fixed family. For each \(\epsilon>0\), require \(F(x)\le x^{1/2+\epsilon}\) outside a set of ordinary measure \(O_\epsilon(X^{1-c_\epsilon})\), for some \(c_\epsilon>0\), on arbitrarily late windows \([Y,X]\) with \(X=Y^{1+\kappa}\). One can instead require an exceptional log measure \(O_\epsilon(Y^{-c_\epsilon})\). An off-line case contradicts the preceding near-envelope estimate by choosing the tolerances below both the zero gap and the saving. More generally one can discard the entire first fixed fraction of the window in log coordinates, since the near-envelope set lies near the right end. The hypothesis allows power-saving holes. It makes no assumption of an attained rightmost line. Under GRH, the pinned converse gives \(F(x)=O(\sqrt x)\), so the stated almost-all bounds hold.

A logarithmic saving or a finite exceptional log measure alone cannot be judged by these two estimates. For example a smooth function model with positive bumps near integer \(u\), of width \(e^{-\sqrt u}\) and height \(e^{\beta u-\sqrt u}\), satisfies the same envelope and positive integral rate, while the union of bumps has finite log measure. This tests the information in the envelope and the rate only. It does not model an automorphic zero set.

## From a negative prime-prefix bound

Let \(A_\delta(t)=\sum_{n\le t}\Lambda_H(n)n^{-\delta}\) and \(P(t)=-t^\delta A_\delta(t)\). Then
\[
 F(e^u)=\frac1{2d}\int_0^B e^{-(1+\delta)v}P(e^{u+v})\,dv .
\]
This is the same original difference kernel written as a positive-weight average of the negative damped prefix. In particular \(J(U)\ll_{\delta,B}\int_U^{V+B}P(e^u)_+ e^{-u/2}\,du\). [Pinned prefix identity and earlier averaged-input audit](https://github.com/Sodelin/Research-Commons/blob/fc73be153974ee9ada2e73013a7997465ba211de/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/dilation-window-boundary-and-prime-mean-obstruction.md)

The prefix has the upper envelope \(|P(t)|\ll_H t^\beta(1+\log t)^3\). For the undamped prefix write truncated Perron at \(x=M+1/2\), \(c=1+1/\log x\), height \(T=x^3\). The sum of absolute log coefficients through \(t\) is \(O_H(t)\) by the self Rankin–Selberg and Chebyshev argument in the preceding memo. Thus \(\sum_n|\Lambda_H(n)|n^{-c}\ll_H\log x\). Since \(|\log(x/n)|\gg1/x\) for integer \(n\), the truncated Perron error is \(O_H(x^{c+1}\log x/T)\). If \(\beta<1\), shift to \(\sigma=\beta+1/\log x\). This line and the region to its right are separated from every zero by \(1/\log x\) in real part. The standard local log-derivative expansion bounds \(-H'/H\) there by \(O_H(\log x\log(3+|t|))\) for \(x\) large. The new vertical integral is \(O_H(x^\sigma\log x\log^2 T)\), and the horizontal terms cost \(O_H(x^c\log x\log T/T)\). Any real \(x\) can use the half-integer with the same floor. At \(\beta=1\), the absolute coefficient bound suffices directly. Partial summation with \(n^{-\delta}\) proves the asserted envelope. [Perron and local log-derivative bounds, Iwaniec–Kowalski](https://doi.org/10.1090/coll/053)

This envelope transfers the near-maximum conclusion to the prefix inside a single fixed log interval. Apply the near-envelope result to the same proportional log window ending at \(V-B\), whose left endpoint differs from \(U\) by only \(B/(1+\kappa)\). Choose one large value of \(F(e^u)\) from its near-end set, so \(u=V-o(U)\), \(u+B\le V\), and \(F(e^u)\ge e^{\beta V-o(U)}\). On the interval \([u,u+B]\), points where \(P(e^v)\) is below \(dF(e^u)/\int_0^B e^{-(1+\delta)t}dt\) can account for at most half of that value in the positive-weight integral. The prefix envelope at the remaining points is \(O(e^{\beta V}(1+V)^3)\). Those points must therefore have log measure at least \(e^{-o(U)}\). The corresponding ordinary measure is at least \(e^{V-o(U)}\), and \(P\) there is at least \(e^{\beta V-o(U)}\).

So an upper bound for the negative normalized damped prefix at \(t^{1/2+\epsilon}\) outside a power-saving exceptional set on these windows would supply the required arithmetic input. In degrees at most four the same conclusion uses prime ideals alone, because deleting the higher prime powers has \(O(\sqrt t)\) effect after normalization, by the proved exterior-trace estimate. The classical almost-all square-root estimate for the standard prefix in Qu, Theorem 5.1, assumes GRH for that same factor. The fixed-family prime number theorem and the short-increment estimates examined earlier do not supply this square-root assertion. [Prime-ideal deletion](https://github.com/Sodelin/Research-Commons/blob/e6df498fa097a5569f6260825b50ac7e41179aae/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/prime-ideal-windows-exterior-traces.md) · [Qu, Theorems 5.1 and 5.2](https://arxiv.org/pdf/0902.0955)

If the largest real zero abscissa is strictly below \(\beta\), the analogous negative near-envelope result also holds. In the damped variable take the negative centered statistic and restore the finitely many real positive-strip residue terms to subtract those poles. Its positive-half-plane poles are then all nonreal, so the generic real-residue sign condition is vacuous. The same proportional-log-window lower-rate argument applies to it and its absolute envelope is unchanged. The modification is \(O(x^{\beta_{\rm real}})\) after normalization, for some \(\beta_{\rm real}<\beta\), and cannot alter the near-envelope measure conclusion. Applying the kernel relation to \(-F,-P\) gives the negative version for the prefix as well. In particular this case includes a nonattained rightmost supremum, because the real completed zeros in the closed strip are finite. This sign statement uses the original observable once the finite lower-order real terms have been accounted for.

## Power-spaced sampling

The same explicit formula yields a modulus of continuity adequate for sparse samples. For \(0<|h|\le1\), use \(|e^{\rho h}-1|\ll\min(1,(1+|\Im\rho|)|h|)\). Summing up to \(1/|h|\) and bounding the absolute tail above it by the local zero count give
\[
 |F(e^{u+h})-F(e^u)|\ll
 e^{\beta u}|h|\log^2(2/|h|)+e^{\delta u}(1+u).
\]
In the lower sum use \(\sum_{1\le j\le1/|h|}\log(2+j)/j\ll\log^2(2/|h|)\); the high-zero tail costs \(O(|h|\log(2/|h|))\). Real parts of the exponents are at most \(\beta\), and the final term bounds the two explicit formula remainders.

Partition a tested \([U,V]\) into cells with sample points \(u_j\) inside them and log widths at most \(C e^{-c u}\) for \(u\) in the cell, with any fixed \(c>0\). This is a gap of order \(x^{1-c}\) in the original variable. Weight each sample of \(F(e^{u_j})_+\) by the exact integral of \(e^{-u/2}\) on its cell. By the modulus bound and \(|a_+-b_+|\le|a-b|\), the difference between the sampled sum and \(J(U)\) is bounded by
\[
 \ll \int_U^V \left[e^{(\beta-1/2-c)u}(1+u)^2
                  +e^{(\delta-1/2)u}(1+u)\right]du .
\]
If \(\beta>1/2\), this is exponentially smaller than \(J(U)\) on the log scale, so the sampled positive-part sum has the same growth rate and detects the off-line case. If GRH holds, the pinned pointwise converse makes the sampled sum \(O(V-U)\). The smoothing allows any fixed power saving in the relative spacing for this implication. Neither a numerical sampling run nor a new square-root estimate is used here.

All these deductions are by hand using the previously pinned Landau rate and smoothed explicit formula. The generic window theorem is the Lean-verified part. The new almost-all and sampling implications are not formalized here, and neither provides the missing prime bound without further input.
