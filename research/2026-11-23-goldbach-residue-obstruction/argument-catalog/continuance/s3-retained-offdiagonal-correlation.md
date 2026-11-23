# The off-diagonal moment in the retained \(S_3\) upper window

The first and second moment bounds for individual centered split-prime counts control the diagonal terms in the retained balanced window. In an off-line case those diagonal terms are smaller by a fixed power than the required window signal. This identifies an exact signed off-diagonal estimate sufficient for the same \(S_3\) critical-line conclusion. The assertion uses the actual zero supremum in a proved envelope and leaves the arithmetic off-diagonal estimate open. [Pinned polynomial factor cutoffs](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd) · [Exact abelian centering on that support](https://github.com/Sodelin/Research-Commons/commit/4bfc76b31db848316d834a98b0b468381feee86a)

## The exact correlation

Fix the standard \(S_3\) Artin factor and \(B>0\). Let \(\beta_*=\sup_\rho\Re\rho\) for its completed zeros. Choose \(u,\alpha>0\) with \(u+\alpha<1\), for example \(u=\alpha=1/2-\eta\), \(0<\eta<1/6\). On a window starting at \(Y\), keep \(U=\lfloor Y^u\rfloor\) and \(P=Y^\alpha\) **fixed**. Write \(V=\log X\), \(v_0=\log Y\). Take \(V-v_0\to\infty\) and \(V-v_0=o(V)\). The pinned fixed-length detector is sufficient for the off-line lower rate on such windows, including nonattained supremum. [Pinned fixed-length result](https://github.com/Sodelin/Research-Commons/commit/304b341ad0a4a99eb16055613bfafceb7c476850)

With \(\beta_U=\mu_{L,>U}*a\) and the original \(K_B\), put
\[
 E_P(t)=\sum_{\substack{p>P\\p\ {\rm splits\ completely}}}(\log p)K_B(p/t)
               -\frac16\int_P^\infty K_B(r/t)\,dr,\qquad
 g_P(v)=e^{-v/2}E_P(e^v).
\]
The supports are exact at the endpoint \(p=P\): the prime sum is strict and the continuous reference starts at \(P\). At \(v\in[v_0,V]\), the centered split-prime remainder from the pinned proof, divided by \(e^{v/2}\), is exactly
\[
 -\frac34 S(v),\qquad
 S(v)=\sum_{U<h\le e^BX/P}b_h\,g_P(v-\log h),\qquad
 b_h=\frac{\beta_U(h)}{\sqrt h}.
 \tag{1}
\]
The terms with \(h>e^{B+v}/P\) are zero by the original kernel. Therefore the scalar covariance
\[
 \mathcal C(Y,X)=2\sum_{U<h<k\le e^BX/P} b_h b_k
       \int_{v_0}^V g_P(v-\log h)g_P(v-\log k)\,dv
 \tag{2}
\]
is the exact off-diagonal part of \(\int_{v_0}^V S(v)^2\,dv\). The products in (2) retain the signed inverse and smooth companion weights. The locked \(P\) makes the two arguments genuine shifts of the same centered prime function. All sums are finite on the window.

## The diagonal is below an off-line signal

For every \(\epsilon>0\), on the active support,
\[
 |E_P(t)|\ll_{L,B,\epsilon} t^{\beta_*+\epsilon}.
 \tag{3}
\]
Indeed the unramified prime trace is \(3\mathbf1_{\rm split}-(1+\chi)/2\), where \(\chi\) is the resolvent Dirichlet character. Its ordinary signed prime prefix is \(O(t^{\beta_*+\epsilon})\) by truncated Perron to the right of the actual supremum. Verified abelian GRH controls the two character prefixes at square-root order with an arbitrary \(\epsilon\) power. The finitely many ramified primes contribute bounded mass. Thus the unweighted centered splitting prefix is \(O(t^{\beta_*+\epsilon})\). Partial summation with \(K_B(\cdot/t)\) on the clipped range \(P<p\le e^Bt\) gives (3), since the kernel's supremum and total variation are bounded and \(P\le e^Bt\) on the active support. When \(t<P/e^B\) the left side is zero. [Pinned prime-prefix envelope and Dirichlet comparison](https://github.com/Sodelin/Research-Commons/commit/1dcdd242401023541592d0126a999ae6cb43c8c5)

The coefficient bound \(|\beta_U(h)|\le d_4(h)\) follows from \(|\mu_L(m)|,|a(m)|\le d_2(m)\) and ordinary convolution. Write
\[
 D(Y,X)=\sum_{U<h\le e^BX/P}b_h^2
             \int_{v_0}^V g_P(v-\log h)^2\,dv.
\]
If \(\beta_*>1/2\), use (3) and sum \(h^{-2\beta_*+\epsilon}\) in the active support. With any sufficiently small \(\epsilon>0\), and enlarging it harmlessly in the resulting estimates,
\[
 D(Y,X)\ll_{L,B,\epsilon}
      X^{2\beta_*-1+\epsilon}U^{1-2\beta_*+\epsilon}
    =X^{(1-u)(2\beta_*-1)+o(1)+O(\epsilon)} .
 \tag{4}
\]
Indeed the integral in \(v\) costs at most \(O_\beta(X^{2\beta_*-1+\epsilon})\) and \(U=Y^{u+o(1)}=X^{u+o(1)}\). If \(\beta_*=1/2\), the same calculation with the harmonic sum gives \(D(Y,X)\ll_\epsilon X^\epsilon\) for every \(\epsilon>0\).

## Consequence for the signed comparison

When \(\beta_*>1/2\), the known lower rate and the prior square-root or power-gap comparisons give
\[
 \int_{v_0}^V (-S(v))_+\,dv
     =X^{\beta_*-1/2+o(1)}.
\]
By Cauchy–Schwarz, the full second moment of \(S\) is at least \(X^{2\beta_*-1+o(1)}\), since \(V-v_0\le\log X\). Choose the tolerance in (4) small in terms of \(u(2\beta_*-1)>0\). The diagonal is then smaller by a fixed power, so
\[
 \mathcal C(Y,X)\ \ge\ X^{2\beta_*-1-o(1)}
\]
on every such sufficiently late window. This conclusion follows from the pole-driven signal even when zeros fail to attain the supremum and even when individual off-diagonal summands cancel.

Consequently the exact signed inequality \(\mathcal C(Y,X)\le X^\epsilon\) for each \(\epsilon>0\) on arbitrarily late windows of this type would suffice for GRH of the fixed factor. Under GRH of this factor, the original statistic has a square-root envelope and both pinned arithmetic comparisons cost \(O_\epsilon(x^{1/2+\epsilon})\). This gives \(\int S(v)^2\,dv\ll_\epsilon X^\epsilon\) on the same windows, hence the same subpower budget for \(\mathcal C\). The criterion is directed at the covariance of shifted centered prime counts with the actual signed coefficients. Removing off-diagonal terms or treating them as automatically negligible would discard the necessary off-line signal. These deductions are hand arguments. No bound for (2), new Lean verification, or additive Goldbach estimate is supplied here.

## Close companion pairs can be removed from the covariance test

Let \(H_0(X)\ge1\) satisfy \(\log H_0(X)=o(\log X)\), for example \(H_0(X)=\exp(\sqrt{\log X})\). Restrict (2) to \(k-h>H_0(X)\) to form \(\mathcal C_{>H_0}\). The terms removed have total absolute value \(O_{L,B,\epsilon}(H_0(X)X^{2\beta_*-1+\epsilon}U^{1-2\beta_*+\epsilon})\) if \(\beta_*>1/2\). Indeed \(h,k\) are comparable since \(U=X^{u+o(1)}\), and (3) with the divisor bound gives the same integrand majorant as in (4) for each nearby \(k\). At each \(h\) there are at most \(H_0(X)\) such \(k\). The identical harmonic argument gives subpower total cost under \(\beta_*=1/2\). Therefore the lower bound \(X^{2\beta_*-1-o(1)}\) under an off-line case holds for \(\mathcal C_{>H_0}\) itself, and the exact signed subpower criterion can use only these separated companion pairs.
