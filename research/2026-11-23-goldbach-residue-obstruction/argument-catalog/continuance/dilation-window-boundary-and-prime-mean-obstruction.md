# What sparse dilation windows require at their boundary

Research instruction for the Riemann/Artin track. Keep the original two-scale kernel and its upper sign. A proposed input should identify what the finite upper window gains over a direct centered prime-count bound, and state exactly which averaged estimate would provide that gain. The following hand results quantify the boundary and test two classical types of prime estimate. They give no new zero exclusion for an automorphic family. [Pinned original kernel](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md)

## Exact reversal and the price of stopping

Use the damped coefficients \(a(n)=\Lambda_H(n)n^{-\delta}\). Put \(S(x)=\sum_n a(n)(x/n-1)_+\). If \(c=\sum_n a(n)/n\) converges, write \(G(x)=S(x)-cx\), so \(G(x)=o(x)\) by summation by parts. Convergence is absolute for \(\delta>0\) in the standard-family setup. The original upper-window observable is \(C_{\delta,B}=(G-T_B G)/(2d)\), with \(T_B G(x)=e^{-B}G(e^Bx)\). For the boundary calculation write
\[
 g(u)=G(e^u),\qquad h(u)=g(u)-e^{-B}g(u+B),\qquad
 I_j(U,W)=\int_U^W (j(u))_+e^{-\theta u}\,du.
\]
Iteration for \(m\ge1\) gives the exact identity
\[
 g(u)=\sum_{k=0}^{m-1}e^{-kB}h(u+kB)+e^{-mB}g(u+mB).
\]
The terminal term tends to zero at fixed \(u\) because \(G=o(x)\). Hence \(h(u)\le A e^{\theta u}\) at every sufficiently large \(u\), with \(0<\theta<1\), gives \(g(u)\le A e^{\theta u}/(1-e^{-(1-\theta)B})\). This is the all-\(x\) reversal with the same exponent.

For a finite window, assume only \(g(u)_+\le C e^{bu}\), with \(b<1\). For \(U<W\le V\), stop at the first \(u+mB\) at or beyond \(V\). Every occurrence of \(h\) then lies inside \([U,V]\) and the terminal point is in \([V,V+B)\). The linear identity, the positive part and a geometric sum give
\[
 I_g(U,W)\le
 \frac{I_h(U,V)}{1-e^{-(1-\theta)B}}
 +\frac{C e^{-(1-b)V}}{1-\theta}
       \bigl(e^{(1-\theta)W}-e^{(1-\theta)U}\bigr).
 \tag{1}
\]
For the first term change variables \(v=u+kB\) after integrating each \(h\) term. Its weight is \(e^{-(1-\theta)kB}\) and its \(v\) range is contained in \([U,V]\). The second term uses \(e^{-mB}g(u+mB)_+\le C e^{u-(1-b)V}\).

In the standard-family setup with \(\delta>0\), one can take \(b=1-\delta\) unconditionally. In fact \(\sum_{n\le X}|\Lambda_H(n)|\ll_H X\). For each unramified factor use \(|p_k|\le(1+|p_k|^2)/2\) on its local power trace, with the prime-ideal Chebyshev bound for the first term and the self Rankin–Selberg prime number theorem for the second. The finite exceptional primes are bounded by the available local growth exponent below \(1/2\). Rank-one factors have unit-modulus finite roots. The self-pair bound follows from its nonnegative coefficients, pole and boundary nonvanishing. Partial summation in
\[
 G(x)=-\sum_{n\le x}a(n)-x\sum_{n>x}\frac{a(n)}n
\]
then gives \(G(x)=O_{H,\delta}(x^{1-\delta})\). [Pinned self Rankin–Selberg argument](https://github.com/Sodelin/Research-Commons/blob/e6df498fa097a5569f6260825b50ac7e41179aae/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/prime-ideal-windows-exterior-traces.md)

At the required \(\theta=1/2-\delta\), (1) can transfer a good window on \([U,(1+\kappa)U]\) to a nonzero proportional subwindow on its left only when there is room for
\[
 (1+\kappa')(1/2+\delta)\le (1+\kappa)\delta,\qquad \kappa'>0 .
\]
In particular this bound alone needs \(\kappa>1/(2\delta)\) to recover any proportional subwindow. For instance \(\delta=7/64\) needs \(\kappa>32/7\). The remaining boundary term explains why the all-\(x\) argument does not reverse a general sparse upper window.

## A sharp boundary in a prime-supported model

The boundary power in (1) is unavoidable using only the convergent linear term and the coefficient cap. Work over rational primes with \(0<\delta<1/2\), and choose disjoint, very widely separated blocks starting at \(X_j\). On \(X_j<p\le2X_j\) put \(a(p)=-c_0 p^{-\delta}\log p\), with small fixed \(c_0>0\). On \(3X_j<p\le4X_j\) put \(a(p)=c_j p^{-\delta}\log p\), choosing \(0<c_j\le1\) to make the sum of \(a(p)\) in the block exactly zero. The prime number theorem gives this choice, and the absolute cap \(|a(p)|\le p^{-\delta}\log p\) follows directly from the weights. Put \(a(n)=0\) at all other norms. Each block has harmonic mass \(\sum a(p)/p\) negative and comparable in size to \(X_j^{-\delta}\), since its two equal total masses are separated by a fixed ratio of \(p\). The harmonic series converges and the same bound on \(G(x)\) follows from the cap.

Take \(X_j=\exp(V_j+B+2)\) and choose the blocks so widely separated that \([U_j,V_j+B]\), with \(U_j=V_j/(1+\kappa)\), falls in the gap before block \(j\). The raw sums of the earlier blocks are zero. Hence \(G(e^u)\asymp e^{u-\delta V_j}\) there, with the multiplier of \(e^u\) exactly constant at all points of that gap. Consequently \(h=0\) on \([U_j,V_j]\), but \(I_g(U_j,W)\) has the boundary order \(\exp((1-\theta)W-\delta V_j)\) when \(W-U_j\to\infty\). This example obeys the prime coefficient cap and gives a nonnegative raw split count with the exact reference. To realize the first-power data with actual local unitary degree-two factors, choose reciprocal unit roots whose trace is \(a(p)/(p^{-\delta}\log p)\) at every prime. The higher damped powers change \(G\) and \(h\) by \(O(x^{1/2-\delta})\), by the elementary prime-power estimate. Thus the \(h\) windows still meet every positive-exponential budget, and the exponential boundary obstruction for \(g\) survives. This model supplies no global automorphic continuation or functional equation.

## Testing candidate mean estimates

Write \(A_\delta(t)=\sum_{n\le t}a(n)\) and retain the original kernel. The exact identity
\[
 C_{\delta,B}(e^u)=-\frac{1}{2d}\int_0^B e^{-v} A_\delta(e^{u+v})\,dv
\]
shows the concrete averaged input that would suffice. An arbitrarily late bound by \(e^{\eta U}\), for every \(\eta>0\), on
\[
  \int_U^{(1+\kappa)U+B}(-A_\delta(e^u))_+e^{-\theta u}\,du
  \tag{2}
\]
implies the required upper window by positivity of the kernel weights and Fubini. Alternatively, a weighted negative-part second moment with weight \(e^{-2\theta u}\) of size \(e^{\eta U}\) there suffices by Cauchy–Schwarz and tightening \(\eta\). On a dyadic \(x\) interval the corresponding sufficient mean-square scale for \(A_\delta\) is \(X^{2-2\delta+o(1)}\) with respect to \(dt\), across the successive dyadic intervals in one of the required long windows. This only demands a one-sided average on some windows. It does not follow from the self-pair prime mean used for coefficient control.

For a concrete comparison, Akbary–Wong, Theorem 1.1(a) at modulus one, give a prime-ideal prefix error \(O_\pi(t e^{-c\sqrt{\log t}})\) in degrees two and three and for non-essentially-self-dual degree-four forms. After damping this gives \(O(t^{1-\delta}e^{-c'\sqrt{\log t}})\) by partial summation. Its resulting upper bound for \(x^\delta C_{\delta,B}\) is \(O(xe^{-c''\sqrt{\log x}})\). Relative to square root it still has exponent \(1/2\) in \(\log x\), and it does not supply the \(e^{\eta U}\) budgets for arbitrarily small \(\eta\). In the other direction, Qu's square-root mean square for the undamped standard automorphic prefix over \(\mathbb Q\) is of the needed order after dyadic decomposition and partial summation, and assumes GRH for the same standard factor. [Akbary–Wong, Theorems 1.1 and 1.5](https://www.math.nsysu.edu.tw/~pjwong/stuff/automorphic-Siegel-Walfisz.pdf) · [Qu, conditional mean square](https://doi.org/10.1016/j.jnt.2006.03.007)

One can test this limitation with explicit tempered local data. Let \(b(p)=e^{-\sqrt{\log p}}\). Choose \(a_p\in\{-1,1\}\) successively over rational primes so that the running error \(\sum_{p\le t}(a_p+b(p))\log p\) has magnitude at most \(2\log t\). At each new prime pick the sign that moves the error toward zero. Each step has size at most \(2\log p\), which proves the bound by induction. Each \(a_p\) is the trace of a determinant-one unitary pair of roots. Thus the local standard trace satisfies \(|a_p|^2=1\) exactly, and the formal self-pair prime number theorem holds, since its higher powers have total size \(O(\sqrt t)\). Prime number theorem summation and partial summation give
\[
 \sum_{p\le t}a_p\log p\sim -t e^{-\sqrt{\log t}},\qquad
 \sum_{p\le t}a_p p^{-\delta}\log p\sim
 -\frac{t^{1-\delta}e^{-\sqrt{\log t}}}{1-\delta}.
\]
For the second asymptotic the damped rounding error is at most \(O(1+\log t)\), and the weighted prime-number-theorem main term follows by differentiating \(t^{1-\delta}e^{-\sqrt{\log t}}\). The higher powers of these unitary roots are negligible at the displayed scale. In the original difference kernel this bias gives \(C_{\delta,B}(x)\asymp_B x^{1-\delta}e^{-\sqrt{\log x}}\) with positive sign for all large \(x\). Its square-root-normalized upper window fails at every sufficiently large \(Y\) for every fixed \(\eta<(1+\kappa)/2\). The model meets both a strong prime-number-theorem error bound without a fixed power saving and the standard self-pair prime mean. Their conclusions alone cannot yield (2) or the original upper window. It is a local data model, not a counterexample to an automorphic theorem.

Even square-root control in the interval length on a fixed submacroscopic range need not imply the needed macroscopic average from local data alone. In the same construction take \(b(p)=p^{-a}\) with \(0<a<1/2\). The prime discrepancy on \((x,x+h]\), \(1\le h\le x^{2a}\), is \(O(\sqrt h\log x)\) by the rounding bound and the elementary estimate \(O(hx^{-a}\log x)\) for the bias in that interval. Its damped prefix nevertheless has a persistent negative bias of order \(x^{1-a-\delta}\) when \(a+\delta<1\), giving a normalized upper-window failure at the square-root scale. This distinguishes fixed short-interval information from (2), which is an average of prefixes at the required tilted scale.

## Finite-height leverage from smoothing

There is a restricted gain when finite-height zero information is available. Suppose all completed zeros of the chosen family with \(|\Im\rho|\le T\), \(T\ge2\), lie on the line. For a fixed family and fixed \(\delta,B\), write \(\mathcal L\) for the log-conductor quantity in the pinned note and \(D=[F:\mathbb Q]d\) for the real gamma degree. The smoothed explicit formula gives
\[
 |x^\delta C_{\delta,B}(x)|
 \ll_{H,\delta,B}\sqrt x\,\mathcal L
       +x\,\frac{\mathcal L+D\log(T+3)}{T},\qquad x\ge2.
\]
Shift the contour for the two-scale difference to a fixed negative unshifted line, avoiding the gamma poles there. The functional equation and absolute Euler convergence on the reflected line bound the new integral. The factor \(1-e^{(s-1)B}\) removes the pole at \(1\); the \(s=0\) term and the finitely many reached trivial zeros contribute \(O_{H,\delta,B}(x^\delta(1+\log x))\) after normalization. This is absorbed by \(\sqrt x\). The low-zero sum is \(O(\sqrt x\,\mathcal L)\) by the quadratic denominator and the local zero count. At height above \(T\), each term is at most \(O(x/(1+|\Im\rho|^2))\). Summing the local zero counts gives the stated tail. The quadratic denominator is the source of this advantage over a direct unsmoothed prefix estimate. The same tail gain is available for the undilated smoothed count. The bound is useful on finite windows with upper endpoint up to about \(T^2\) after logarithmic losses. A fixed \(T\) gives no arbitrarily late windows. No finite-height zero check is carried out here. [Pinned smoothed explicit-formula inputs](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md)

The bounds and models are hand arguments. The only Lean input referenced here is the original generic window implication. Among the inputs checked here, the self-pair prime second moment, prime-number-theorem savings without a fixed power, and interval-length square-root control on a fixed submacroscopic range do not supply the averaged bound (2). The sparse upper window itself remains open.
