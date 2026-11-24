# Separated log-ratio cells in the exact Artin covariance

Fix one standard \(S_3\) factor \(L\), its completed zero supremum \(\beta_*\), and the original kernel \(K_B\) with Mellin transform \(H_B\). Use the locked cutoffs \(U=\lfloor Y^u\rfloor\), \(P=Y^\alpha\), \(H=Y^{u+\kappa}\), with \(0<u<1/2\), \(\alpha,\kappa>0\) and \(u+\alpha+\kappa<1\). The log windows are \(v_0=\log Y\le v\le V=\log X\) with \(L_0=V-v_0\to\infty\), \(L_0=o(V)\). The original roughness, coprimality, companion separation, and output-atom restrictions remain in place. Write \(E_P(y)\) for the exact centered split-prime sum with strict cutoff \(p>P\) and continuous reference from \(P\), and set \(g_P(w)=e^{-w/2}E_P(e^w)\). The Dirichlet critical-line inputs are only those for the Riemann zeta function and the quadratic resolvent character. [Original signed covariance and close relative shifts](https://github.com/Sodelin/Research-Commons/commit/371ff8bc2032a4a70c0db9a4ed3b81eece58bb52) · [Exact output-atom masks](https://github.com/Sodelin/Research-Commons/commit/47e3ea8ecc114caac8d8afda0447b19920072d5a)

## The critical Gram kernel is rigid at far separated log ratios

Suppose first \(\beta_*=1/2\). On the full retained shift range \(w=v-\log h\), \(U<h\le H\), the pinned critical-line formula gives
\[
 g_P(w)=T(w)+o(1),\qquad
 T(w)=-d+\sum_{\gamma\ne0}b_\gamma e^{i\gamma w},\qquad
 d>0,\quad \sum_\gamma|b_\gamma|<\infty .
\tag{1}
\]
The drift \(d\) includes the positive prime-square subtraction \(H_B(1/2)/3\) and any central zero terms. Indeed \(y=e^w\ge Y/H\gg P\), so the exact locked-cutoff difference \(E_P(y)-E_0(y)=-(1-e^{-B})(\theta_{\rm split}(P)-P/6)\) is \(o(\sqrt y)\) uniformly. The uncut error in the critical formula is also uniform on this range. The coefficients in (1) are grouped by ordinate and conjugate paired since the function is real. [Critical-line prime-square correction and exact cutoff](https://github.com/Sodelin/Research-Commons/commit/371ff8bc2032a4a70c0db9a4ed3b81eece58bb52)

For \(U<h<k\le H\), the unmasked averaged normalized kernel is
\[
 \frac1{L_0}\int_{v_0}^V
        g_P(v-\log h)g_P(v-\log k)\,dv
       =\mathcal G(\log(k/h))+o(1),
 \qquad
 \mathcal G(t)=d^2+2\sum_{\gamma>0}|b_\gamma|^2\cos(\gamma t).
\tag{2}
\]
The error is uniform. Approximate (1) by finitely many frequencies uniformly and integrate products over \(v\). Terms of nonzero total frequency have integral divided by \(L_0\) tending to zero uniformly in the translations. The remaining frequencies give (2), and the absolutely summable tails can be made arbitrarily small afterwards.

The exact output-atom masks give another explicit term. Put \(r=h/k\), \(y=x/k\), \(x=e^v\), and \(I_B(r)=\int_0^\infty K_B(t)K_B(rt)\,dt\). If \(\mathcal G_{\rm mask}(h,k;Y,X)\) is the averaged normalized kernel after imposing both masks, then
\[
 \mathcal G_{\rm mask}(h,k;Y,X)
 =\mathcal G(\log(k/h))
  -\frac{\sqrt r}{6}I_B(r)\left(\frac{V+v_0}{2}-\log k\right)
  +o\bigl(1+\sqrt r\log X\bigr).
\tag{3}
\]
The error is uniform on the same support. For this, the coincident split-prime output atom term is
\[
 \frac{\sqrt r}{y}\sum_{\substack{q>P\\q\ {\rm split}}}
      (\log q)^2 K_B(q/y)K_B(rq/y).
\]
Chebotarev partial summation against \(\log t\,K_B(t/y)K_B(rt/y)\), whose bounded-variation norm is \(O_B(\log y)\) uniformly in \(r\), gives
\(\tfrac16\sqrt r I_B(r)\log y+o(\sqrt r\log y)\). The finite-divisor masks on either coordinate cost \(o(1)\) pointwise in the normalized kernel, since their total logarithmic weight is at most \(\log(hk)\), and \(y\gg X^{1-u-\kappa+o(1)}\). Excluding these same divisors from the coincident-atom sum costs \(o(1)\) as well. Averaging \(\log y=v-\log k\) gives (3). [Fixed-field Chebotarev, Lagarias–Odlyzko Theorem 1.3](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf)

The function \(I_B(r)\) is uniformly positive for \(0<r\le1\), and equals \(B(1-e^{-B})\) for \(r\le e^{-B}\), because then \(K_B(rt)\) is constant throughout the support of \(K_B(t)\). In particular the masked kernel is uniformly negative when \(\log(k/h)\le(2-\delta)\log\log X\) for any fixed \(\delta>0\). For \(\log(k/h)\ge(2+\delta)\log\log X\), the mask contributes \(o(1)\) and the limiting kernel is \(\mathcal G\). Its nonzero mean is \(d^2\), and it has recurrent positive values at arbitrarily far ratios. Thus neither the original kernel nor its atom-distinct version admits general decay in the log separation.

More precisely, fix \(0<\omega<\min\{\kappa,\,1/2-u\}\). There are \(t_X=\omega\log X+O(1)\) with \(\mathcal G(t_X)\ge\mathcal G(0)/2>0\). For finitely many frequencies, the phase map of \(\mathbb R\) has compact group closure. Cover that closure by finitely many translates of a small neighborhood of the identity using points on the orbit. At any time a bounded shift then returns all these phases close to the identity. Approximate the tail in (2) uniformly to get the stated conclusion. Uniform continuity of \(\mathcal G\) gives a fixed small \(\delta_1>0\) for which \(\mathcal G\) stays positive throughout \(|t-t_X|\le\log(1+\delta_1)\).

Take the two exact prime-companion intervals
\[
 I_X=(U,(1+\delta_1)U],\qquad
 J_X=(R,(1+\delta_1)R],\qquad R=Ue^{t_X}.
\tag{4}
\]
Every cross pair of rational primes from these bands is rough, squarefree, coprime, in \(U<h<k\le H\), and satisfies the sharp original additive gap. Their log ratios lie in the positive region. Chebotarev gives \(\asymp U/\log U\) and \(\asymp R/\log R\) completely split primes in the two bands. For those companions \(\beta_U(h)=-a(h)=-2\), since \(h>U\) is prime. Therefore the exact positive cross slice, including the output-atom masks, has order
\[
 \frac{\sqrt{UR}\,(V-v_0)}{\log U\,\log R}
       =X^{u+\omega/2+o(1)}.
\tag{5}
\]

## Exact signed two-cell bound after both masks

For the same bands (4), now include every prime companion with its actual signed coefficient. This calculation works irrespective of the zeros, with the actual exponent \(\beta_*\). For \(M=U\) or \(R\), the exact scalar sum is
\[
 S_{I}(v)=x^{-1/2}\sum_{h\in I,\ h\ {\rm prime}}\beta_U(h) E_P(x/h),
 \qquad I=(M,(1+\delta_1)M].
\]
The Artin prime prefix is \(\sum_{p\le t}a(p)=O_\epsilon(t^{\beta_*+\epsilon})\). Differentiating the unchanged \(K_B\) shows that the supremum plus total variation of \(x^{-1/2}E_P(x/h)\) on \(I\) is
\(O_\epsilon(X^{\beta_*-1/2+\epsilon}M^{-\beta_*+\epsilon})\).
Indeed the logarithmic derivative of \(E_P(y)\) is the integral of \(y/t\) against the centered prime measure on \(P<t\) and \(y<t<e^By\), so it obeys the same signed-prefix estimate as \(E_P\). Partial summation gives \(S_I(v)=O_\epsilon(X^{\beta_*-1/2+\epsilon})\). The unmasked exact signed cross covariance is \(2\int S_{I_X}S_{J_X}\), of size \(O_\epsilon(X^{2\beta_*-1+\epsilon})\).

For each pair \(h,k\) in (4), every companion prime atom dividing \(hk\) is one of \(h,k\). Since \(R<X^{1/2-c}\) for a fixed \(c>0\), all products \(h^2,hk,k^2\) are below \(x\) on these windows. Thus from each \(E_P\) coordinate the exact divisor mask subtracts the same
\[
 (1-e^{-B})\bigl(\mathbf1_{h>P,\ h\ {\rm split}}\log h
                      +\mathbf1_{k>P,\ k\ {\rm split}}\log k\bigr).
\tag{6}
\]
The linear divisor-mask terms factor into scalar sums in \(h\) and \(k\). For instance if the \(\log h\) factor is in the same coordinate as \(E_P(x/h)\), bound that side absolutely by \(O(X^{\beta_*+\epsilon}U^{1-\beta_*})\) and use \(O(R^{\beta_*+\epsilon})\) for the other signed companion sum. If the factors are in different coordinates, bound the \(\log h\)-weighted side by \(O(U X^\epsilon)\) and use the signed \(O(X^{\beta_*+\epsilon})\) for the \(E_P\)-weighted side. The symmetric cases have the same bound \(O(X^{\beta_*+\epsilon}R)\), since \(U^{1-\beta_*}R^{\beta_*},R^{1-\beta_*}U^{\beta_*}\le R\). After normalization these linear terms are \(O(X^{\beta_*-1+\epsilon}R)\), strictly below \(X^{2\beta_*-1}\) as \(R<X^{1/2-c}\) and \(\beta_*\ge1/2\). The double divisor-mask term costs \(O_\epsilon(X^{-1+\epsilon}UR)\) absolutely.

For the remaining coincident-atom correction, fix a split output prime \(q>P\) and use the signed companion scalars
\[
 Q_{q,I}(v)=x^{-1/2}(\log q)
       \sum_{h\in I,\ h\ {\rm prime}}\beta_U(h)K_B(qh/x).
\]
The monotone kernel and the signed Artin prime prefix give
\(|Q_{q,I}|\ll_\epsilon x^{-1/2}(\log q)M^{\beta_*+\epsilon}\).
The product \(Q_{q,I_X}Q_{q,J_X}\) vanishes for \(q>e^Bx/R\). Summing its absolute value gives \(O_\epsilon(U^{\beta_*}R^{\beta_*-1}X^\epsilon)\) by Chebyshev with \((\log q)^2\). For the exact divisor-masked diagonal, subtract the self companion \(h=q\) in the first scalar when \(q\in I_X\), and \(k=q\) in the second when \(q\in J_X\). The two removed companion ranges are disjoint. The cross errors are \(O_\epsilon(X^{-1+\epsilon}(UR^{\beta_*}+RU^{\beta_*}))\), by the same signed scalar bound on the other side. All correction bounds hold pointwise and the log-window length is subpower. Hence on the fully atom-separated original support the exact signed prime cross covariance is
\[
 O_\epsilon(X^{2\beta_*-1+\epsilon}).
\tag{7}
\]
On the critical line this is subpower. But all kernels between the cells are positive by (3) and the choice of \(t_X\). So the completely split slice in (5) requires cancellation by actual mixed identity–3-cycle pairs between these same cells. No near-cell or composite companion contribution is allocated to that cancellation.

## Attained off-line top line

There is also a cross-cell result if \(\beta_*>1/2\) is attained. It needs no gap or finiteness assumption on the top line. The absolutely convergent smoothed Artin explicit formula, divided by \(y^{\beta_*}\), gives
\[
 e^{-(\beta_*-1/2)w}g_P(w)=T_*(w)+o(1),
\]
uniformly on all retained shifts, where
\[
 T_*(w)=-\frac13\sum_{\Re\rho=\beta_*}m_\rho H_B(\rho)e^{i\Im\rho\,w}.
\]
The attained supremum is below 1 by nonvanishing on \(\Re s=1\), and the functional equation places every completed Artin zero in \([1-\beta_*,\beta_*]\) in real part. The contour for the log derivative may therefore be shifted to a fixed line \(0<\sigma<1-\beta_*\), uniformly separated from the completed zeros. The kernel \(H_B\) decays quadratically in height and the local zero count makes the zero expansion absolutely convergent. It is legitimate to send its horizontal edges to infinity at heights bounded away from the zero ordinates by an inverse log factor. The leading coefficients in \(T_*\) are nonzero because \(H_B(\rho)=(e^{B(\rho-1)}-1)/(\rho(\rho-1))\) is nonzero for \(\Re\rho=\beta_*\). The terms strictly below \(\beta_*\) give uniform \(o(1)\) on late tails by dominated convergence. The split-prime trace identity supplies the factor \(1/3\). Its Dirichlet and prime-power terms, and the exact locked-cutoff error on \(y\ge Y/H\), are of strictly smaller size. [Pinned smoothed explicit formula and local zero count](https://github.com/Sodelin/Research-Commons/commit/e00069c40dd17f50a10f57bb76d7300c8f0e3cdf)

For the same \(\omega\), choose \(t_X=\omega\log X+O(1)\) to be a return of \(T_*\) in uniform norm, by the compact finite-frequency argument and its uniform Fourier tail. Choose \(\delta_1>0\) small enough to preserve the approximation \(T_*(w-t)\approx T_*(w)\) throughout the ratios in (4). The mean square of \(T_*\) on every sufficiently long fixed log interval is bounded below uniformly in its starting point, since its Fourier square mean is positive. At the terminal interval, after writing \(s=\beta_*-1/2>0\), this implies
\[
 \int_{v_0}^V e^{2s(v-V)}T_*(v-\log h)^2\,dv\gg 1.
\]
The contribution of the uniform small discrepancy between the \(h,k\) shifts to the exponentially weighted product integral is at most its supremum times \(\|T_*\|_\infty/(2s)\). It can be made smaller than the lower bound. The uniform \(o(1)\) errors are also negligible by the same integrable weight. Thus every cross kernel has positive size \(\asymp(X/\sqrt{hk})^{2\beta_*-1}\). The atom masks are negligible for this comparison on individual pairs: the coincident-atom term is \(O(\log X)\), and each normalized divisor-atom sum is \(O((h/x)^{1/2}\log X)\) or \(O((k/x)^{1/2}\log X)\), compared to the corresponding polynomial off-line size. Consequently the positive same-sign cross slice has exponent
\[
 2\beta_*-1+(2u+\omega)(1-\beta_*).
\]
Since an attained off-line line has \(\beta_*<1\) by nonvanishing on \(\Re s=1\), this strictly exceeds (7), forcing mixed-class cancellation on the same original cross-cell support. The attained-line condition is used for positivity of the far-shift kernel in this off-line case. Formula (7) itself uses no attainment assumption.

These are hand bounds on fixed-\(S_3\) cross-cell slices and obstructions to kernel-only decorrelation. They do not give a bound for the complete retained covariance or a new Lean check.
