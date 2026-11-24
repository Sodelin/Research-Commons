# The all-prime companion signal without a top-line gap

Fix the standard \(S_3\) Artin factor \(L\), the original dilation \(K_B\), and the hard locked cutoffs for a window starting at \(Y\):
\[
 T=\log Y,\qquad U=\lfloor e^{aT}\rfloor,\quad H=e^{bT},\quad P=e^{\alpha T},
 \qquad 0<a<b,\quad \alpha+b<1 .
\]
Write \(V=\log X\) with \(V-T\to\infty\) and \(V-T=o(V)\). The prime sector of the retained covariance uses \(U<h<k\le H\) with both companions prime, the original subpower additive separation, and both output-atom masks. Its one-variable scalar before the companion and atom diagonals is
\[
 S_{\rm pp}(v)=-e^{-v/2}
         \sum_{U<q\le H,\ q\ {\rm prime}}a(q)E_P(e^v/q).
\tag{1}
\]
The sign is exact because \(\beta_U(q)=-a(q)\) for prime \(q>U\). The covariance of all its pairs, including the diagonal, is \(\int_T^V S_{\rm pp}(v)^2\,dv\). [Original covariance and hard cutoffs](https://github.com/Sodelin/Research-Commons/commit/db66db1688943b76a404d6db5dc5a9477cbe2ed3) · [Exact output-atom masks](https://github.com/Sodelin/Research-Commons/commit/47e3ea8ecc114caac8d8afda0447b19920072d5a)

Assume that the actual rightmost abscissa \(\beta=\beta_*>1/2\) is attained. No gap to lower zeros and no finiteness of the top line are assumed. There is a set of good starting logarithms \(T\), with complement of measure \(O(R^{-1/2})\) in each block \([R,2R]\), such that the exact retained all-prime signed covariance satisfies
\[
 \mathcal C_{\rm pp}(Y,X)\gg X^{2\beta-1}
\tag{2}
\]
on those starts, uniformly on the stated log windows. The comparison uses the verified Dirichlet inputs for the two abelian centering terms. It extends the finite isolated top-line case and still allows an exceptional sparse sequence of starts. [Earlier isolated-line calculation](https://github.com/Sodelin/Research-Commons/commit/99f45afcdd885d79b3474d4b867f3d0b0e640e21)

## A square-mean statement for the unsmoothed prime prefix

Let
\[
 M(t)=e^{-\beta t}\sum_{p\le e^t}\Lambda_L(p).
\]
For any fixed \(0<c<d\), on a block \(cR\le t\le dR\), this has the \(L^2(dt/R)\) expansion
\[
 M(t)\ \sim\
 -\sum_{\Re\rho=\beta}\frac{m_\rho}{\rho}e^{i\Im\rho\,t}.
\tag{3}
\]
Here and below the expansion means that the upper limit of the \(L^2\) error tends to zero after increasing a fixed ordinate cutoff in the displayed series. Explicitly, for every \(N\ge2\) the contribution from all zeros of ordinate greater than \(N\) in absolute value is bounded in this norm, uniformly in large \(R\), by a quantity tending to zero with \(N\). No absolute convergence of the unsmoothed series is claimed.

To prove (3), take truncated Perron for the full logarithmic derivative at height \(T_R\) between \(e^{K R}\) and \(e^{K R}+1\), with \(K\) fixed large in terms of \(d\), and keep that height for the whole block. The local zero count gives an inverse-log distance to every ordinate at some such height. The contour can be moved to a fixed negative real line avoiding the gamma poles, where the functional equation gives a logarithmic vertical bound. On the horizontal segments the local zero expansion gives \(O_L((\log T_R)^2)\). The standard truncation error for \(|\Lambda_L(n)|\le 2\log n\) is \(O(e^t(\log(e^tT_R))^C/T_R+\log(e^t+2))\). Indeed the nearest integer contributes at most \(O(\log(e^t+2))\) and the remaining integers in the comparable range give a harmonic sum using \(e^t/(T_R|n-e^t|)\). The distant range is bounded by absolute convergence at \(1+1/t\). The same error covers the half weight at an exact endpoint. Trivial zero and origin terms have at most polylogarithmic size here. Prime powers \(p^j,\ j\ge2\), cost \(O(e^{t/2})\) by Chebyshev and the local bound, and are negligible after normalization. Hence a uniform \(o(1)\) error in \(M\) is obtained by writing the truncated zero terms
\[
 -\sum_{|\Im\rho|\le T_R}
     \frac{m_\rho}{\rho}e^{-(\beta-\Re\rho)t}e^{i\Im\rho t}.
\tag{4}
\]
[Local logarithmic derivative and zero counts, Iwaniec–Kowalski Proposition 5.7](https://doi.org/10.1090/coll/053)

The high-ordinate tail of (4) is bounded in square mean without any gap. Use a nonnegative smooth weight \(w(t/R)\) supported in \(c/2<t/R<2d\) and at least one on the block. For \(\delta_1,\delta_2\ge0\), repeated integration by parts shows
\[
 \left|\int w(t/R)e^{-(\delta_1+\delta_2)t}
                       e^{i(\gamma_1-\gamma_2)t}\,dt\right|
 \ll_N R(1+R|\gamma_1-\gamma_2|)^{-N}.
\tag{5}
\]
The constants are uniform in the \(\delta_i\), since derivatives of the damping cost \(R^{-1}\) per derivative after using \(t\ge cR/2\). Group ordinates into unit intervals. The sum of \(m_\rho/|\rho|\) in the \(j\)-th large interval is \(O_L(\log(3+|j|)/(1+|j|))\). Nearby interval pairs in (5) cost the sum of squares of these bin masses. Distant bins are bounded by convolution with an absolutely summable sequence, giving the same estimate. That square sum is finite and its high tail tends to zero. After truncating to finitely many low ordinates, all terms strictly below \(\beta\) decay on the whole block. This proves (3) and
\[
 \int_{cR}^{dR}|M(t)|^2\,dt\ll_{L,c,d}R.
\tag{6}
\]
The proof of (3) does not itself require attainment. If the top line is empty then its square mean tends to zero.

## Sharp prime moments on a full-measure set of starts

Call \(T\) good if
\[
 |M(aT)|+|M(bT)|\le T^{3/4}.
\tag{7}
\]
By (6), rescaling and the square-mean inequality, the excluded set has measure \(O(R^{-1/2})\) in each block \([R,2R]\). Let
\[
 B_T(s)=\sum_{U<q\le H,\ q\ {\rm prime}}a(q)q^{-s}.
\]
Because the weights are \(\Lambda_L(q)/\log q\), exact Stieltjes integration at these hard cutoffs gives, for \(s=\sigma+i\tau\) and \(\delta=\beta-\sigma\),
\[
 B_T(s)=
 \left[\frac{ M(t)e^{\delta t-i\tau t}}{t}\right]_{aT}^{bT}
 +\int_{aT}^{bT} M(t)e^{\delta t-i\tau t}
                  \left(\frac{s}{t}+\frac1{t^2}\right)\,dt.
\tag{8}
\]
The lower endpoint uses the prefix inclusive at \(e^{aT}\), implementing the strict cut \(q>U\) even if that real threshold is itself an integer. The same convention includes the upper endpoint.

For every zero \(s=\rho\), (6)–(8) show, on all good \(T\),
\[
 |e^{-(\beta-\Re\rho)bT} B_T(\rho)|\ll_L 1+|\rho|.
\tag{9}
\]
Indeed the endpoint contribution is \(O(T^{-1/4})\) after extracting the indicated factor, and \(\int_{aT}^{bT}|M(t)|\,dt/t=O(1)\) uniformly. For any fixed top zero \(\rho\), (3) shows more precisely
\[
 B_T(\rho)=-m_\rho\log(b/a)+o(1)
\tag{10}
\]
uniformly on good \(T\). To see this, the \(1/t^2\) term and the endpoints in (8) vanish. Approximate \(M\) in the remaining integral by a finite top series on the encompassing log block. Cauchy–Schwarz against \(1/t\) makes the error uniformly small. Then every nonmatching ordinate integrates to \(O_\rho(1/T)\) for the fixed finite approximation, while the matching coefficient \(-m_\rho/\rho\) is multiplied by \(\rho\log(b/a)\). Let the finite approximation grow after taking the large-\(T\) limit. This proves the sharp-cutoff moment without a pointwise approximation to an unsmoothed prime prefix.

## The top resonance in the actual scalar

The difference \(E_P(y)-E_0(y)=-(1-e^{-B})F(P)\) is exact throughout the support \(y=x/q\ge Y/H\gg P\), with \(F(P)=\theta_{\rm split}(P)-P/6\). Its contribution before square-root normalization in (1) is \(O_\epsilon((PH)^{\beta+\epsilon})\), by the signed Artin prime prefix. This has a fixed gap below \(x^\beta\).

For the uncut split prime statistic, the exact prime trace relation gives one third of the full smoothed Artin logarithmic derivative after removing the higher Artin prime powers and inserting the two abelian centered terms. In the convolution with \(B_T(s)\), all those corrections still have a fixed lower exponent. For each, shift its Mellin integral to fixed \(\sigma>1/2\) close to \(1/2\). The power series is absolutely convergent there. The Dirichlet centered prime transforms are holomorphic there after the principal main term, whose residue exactly supplies the continuous centering. The finite prime polynomial has
\[
 |B_T(\sigma+it)|\ll_\epsilon
      H^{(\beta-\sigma)_++\epsilon}(3+|t|)^\epsilon
\]
uniformly in all heights on each fixed line \(\sigma>1/2\), including \(\sigma<\beta\). Specifically the twisted logarithmically weighted prime prefix up to \(W\) uses Perron in \(w\) for the prime logarithmic series at \(s+w\), shifted to \(\Re w=(\beta-\sigma)_++\delta>0\). The new argument stays strictly to the right of \(\beta\), so no pole is crossed. The truncation error is independent of \(t=\Im s\) because \(|p^{-it}|=1\), and the logarithmic growth in \(|t+\Im w|\) is absorbed by an arbitrary power of \(3+|t|\) and \(W\). This is the pinned bound (2). Abel summation of that prefix against \(1/\log q\) on \((U,H]\) gives the displayed bound, since its total variation is \(O(1/\log U)\). Combined with \(H_B(s)=O_B((1+|t|)^{-2})\), this bounds the corrections by \(O_\epsilon(x^{1/2+\epsilon}H^{\beta-1/2+\epsilon})\), strictly below \(x^\beta\). Finite ramified corrections are smaller by the same signed prefix. [Twisted Artin prefix, equation (2)](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd) · [Exact abelian prime centering](https://github.com/Sodelin/Research-Commons/commit/4bfc76b31db848316d834a98b0b468381feee86a)

For the full Artin term times \(B_T(s)\), shift the original smooth integral to a fixed sufficiently negative real line \(-C\) avoiding the poles of its real gamma factors. By the functional equation and Hecke nonvanishing on \(\Re s=1\), the completed Artin function is nonzero on \(\Re s\le0\). Thus the only uncompleted zeros there are the trivial zeros at gamma poles. The logarithmic derivative on the chosen negative line has logarithmic growth by the functional equation, Stirling and the absolutely convergent reflected Euler product. Its integral is \(O(x^{-C}H^{1+C})\), negligible for fixed \(C\) large because \(b<1\). A crossed trivial zero at \(-j<0\) gives a simple residue involving \(x^{-j}B_T(-j)\), which is \(O_\epsilon(H^{\beta+\epsilon})\) by the signed prime prefix. At the origin \(H_B\) has at most a simple pole and the logarithmic derivative has at most a simple pole, so the contribution uses only \(B_T(0),B_T'(0)=O_\epsilon(H^{\beta+\epsilon})\), with at most an additional \(\log x\). There is no kernel pole at \(1\). The nontrivial-zero sum is absolutely convergent at fixed \(T,x\), since \(B_T\) is finite and \(H_B\) supplies the quadratic ordinate decay. Thus after the corrections the normalized scalar is
\[
 e^{-(\beta-1/2)v}S_{\rm pp}(v)
 =\frac13\sum_\rho m_\rho H_B(\rho)B_T(\rho)
           e^{-(\beta-\Re\rho)v}e^{i\Im\rho\,v}
      +o(1).
\tag{11}
\]
The sign is positive before \(B_T\), because the zero residue of \(-L'/L\) is negative and (1) has a minus sign.

On any fixed terminal interval \([V-L,V]\), (9) makes the high-ordinate tail of (11) uniformly small in \(L^2\) on good starts. Indeed factor each coefficient using \(e^{-(\beta-\Re\rho)bT}B_T(\rho)\); the residual damping is \(e^{-(\beta-\Re\rho)(v-bT)}\). The coefficient bin masses are again \(O(\log(3+|j|)/(1+|j|))\), because of the quadratic decay of \(H_B\) and the linear factor in (9). The fixed-width version of (5) applies uniformly since \(v-bT\gg T\), and gives the same square-summable tail bound. Each fixed lower zero is suppressed by that damping. For each top zero use (10). Consequently, uniformly on good \(T\), the normalized scalar (11) converges on every fixed terminal interval in \(L^2\) to the moving function
\[
 -\frac{\log(b/a)}3
   \sum_{\Re\rho=\beta}m_\rho^2H_B(\rho)e^{i\Im\rho\,v}.
\tag{12}
\]
Convergence here means that the norm of the difference on the moving interval tends to zero. The series in (12) is absolutely convergent: the square of the total zero multiplicity in a unit ordinate interval is \(O(\log^2(3+|j|))\). It is a nonzero real trigonometric series, since every top coefficient is nonzero. Its square mean is bounded below uniformly on every sufficiently long fixed interval, by approximation by finitely many frequencies and Fourier orthogonality. Choose such an \(L\). The terminal interval is contained in the tested window and \(e^{(2\beta-1)v}\asymp_L X^{2\beta-1}\) there. We obtain \(\int_T^V S_{\rm pp}(v)^2\,dv\gg X^{2\beta-1}\) on good starts.

## Returning to the exact covariance

Distinct prime companions are automatically rough, squarefree and coprime. The companion diagonal and the actual excluded short gaps contribute a fixed lower power \(O_\epsilon(X^{2\beta-1+\epsilon}U^{1-2\beta}H_0)\), with \(H_0\) subpower, by the original absolute envelope.

The output masks can also be restored within this prime sector. For a coincident output atom \(p\), put the first companion in a dyadic band of scale \(R\) and the second in one of scale \(S\ge R\). The signed \(K_B(ph/x)\) companion sum on the first band is \(O_\epsilon(R^{\beta+\epsilon})\) and on the second \(O_\epsilon(S^{\beta+\epsilon})\), by the signed prime prefix and monotone weight. The output cutoff \(p\ll x/S\), Chebyshev and normalization give \(O_\epsilon(R^\beta S^{\beta-1}X^\epsilon)\) for the signed correction. Summed over bands this is at most \(O_\epsilon(H^{2\beta-1}X^\epsilon)\), below \(X^{2\beta-1}\).

For a linear divisor mask where the output atom equals the companion in its own coordinate, the atom kernel forces that companion below \(O_B(\sqrt x)\). Its weighted prime sum costs \(O_\epsilon(\sqrt x\,X^\epsilon)\) absolutely. On the other companion's dyadic interval \(h\asymp S\), the exact \(\log y\) derivative of \(E_P(y)\) is the integral of \(y/t\) against its centered prime measure on \(t>P,\ y<t<e^By\). The centered prime prefix and partial summation bound both \(E_P(y)\) and this derivative by \(O_\epsilon(y^{\beta+\epsilon})\). Therefore \(E_P(x/h)\) has supremum plus variation \(O_\epsilon((x/S)^{\beta+\epsilon})\) on the dyadic interval. Applying the signed prime prefix in \(h\) gives \(O_\epsilon(x^{\beta+\epsilon})\) per dyadic interval and hence also after summation with a harmless exponent loss. This bounds the self-divisor correction by \(O_\epsilon(X^{\beta-1/2+\epsilon})\) after normalization. For a crossed divisor atom, fix the companion \(k\asymp S\) carrying that atom. The other companion enters with kernel \(K_B(hk/x)\), and its signed sum is \(O_\epsilon(\min(H,x/S)^{\beta+\epsilon})\) by the exact product cutoff. The \(k\)-absolute weight with \(E_P(x/k)\) then gives
\[
 O_\epsilon\!\left(
 X^{\beta-1+\epsilon}S^{1-\beta}\min(H,X/S)^\beta
 \right)
 \ll_\epsilon X^{2\beta-1+\epsilon}(H/X)^{2\beta-1}.
\]
Split at \(S=X/H\) for the last inequality. The analogous terms are the same. A product of two divisor masks is subpower: its support has either \(h,k\ll_B\sqrt x\) or \(hk\ll_B x\), each \(O_B(x\log X)\) integer pairs before normalization.

For clarity, expand the two divisor masks first and then subtract the coincident atom from the result. At a split output prime \(p>P\), write
\[
 Q_p=x^{-1/2}\log p\sum_{U<h\le H,\ h\ {\rm prime}}\beta_U(h)K_B(ph/x),
 \qquad
 Q_p^{\rm self}=x^{-1/2}\log p\,\beta_U(p)K_B(p^2/x)\mathbf1_{U<p\le H}.
\]
The exact coincident-atom correction after the divisor masks on all ordered prime pairs is \(\sum_p(Q_p-Q_p^{\rm self})^2\). In both coordinates, a prime atom can divide a prime companion only by equaling it. Thus this formula treats both possible self overlaps without a further inclusion–exclusion sign change. The companion diagonal is removed at the end, so a temporary double label for a self-divisor mask at \(h=k\) does not affect any retained term.

The difference from the unmasked diagonal \(\sum_p Q_p^2\) consists of the cross terms \(-2\sum_p Q_pQ_p^{\rm self}\) and the self-square. On the cross support \(p\asymp R\ll_B\sqrt x\) by \(K_B(p^2/x)\), and the other companion in \(Q_p\) can reach \(\min(H,e^Bx/p)\), even if it is larger than \(\sqrt x\). Its signed \(K_B(ph/x)\) sum is \(O_\epsilon(\min(H,x/R)^{\beta+\epsilon})\). Thus the cross term in that dyadic band costs \(O_\epsilon(X^{-1+\epsilon}R\min(H,X/R)^\beta)\), at most \(O_\epsilon(X^{(\beta-1)/2+\epsilon})\) after summing bands. This bound includes the case where the output prime is the smaller companion. The self-square is \(O_\epsilon(X^{-1/2+\epsilon})\) by its support. Both are below the target.

All close-pair corrections can be removed absolutely on the original gap: for a single divisor mask use \(O(X^{-1/2}\log X)\) times the other normalized envelope, and for a coincident atom use \(O(X^\epsilon/\max(h,k))\) per normalized pair. The intersections are smaller. Thus the signed mask comparison on the exact prime subsector costs a fixed lower power. This proves (2).

In the nonattained case the same good-start analysis of (11) gives a normalized terminal \(L^2\) limit of zero, since there is no top frequency. It does not exclude an \(X^{2\beta-1-o(1)}\) signal there. These are hand estimates for a fixed factor. They are conditional on attainment for the positive conclusion and do not prove the desired upper bound or a new Lean result.
