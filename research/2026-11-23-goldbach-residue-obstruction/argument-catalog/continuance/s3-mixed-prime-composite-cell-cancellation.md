# Signed cancellation in the actual mixed prime–composite cells

Keep the fixed \(S_3\) Artin factor, original centered prime function \(g_P\), and locked windows \(v_0=\log Y\le v\le V=\log X\) with \(V-v_0\to\infty\) and \(V-v_0=o(\log X)\). Let \(U=\lfloor Y^u\rfloor\), \(P=Y^\alpha\), \(H=Y^{u+\kappa}\), \(0<u<1/2\), and \(u+\alpha+\kappa<1\). The roughness threshold is \(z=(\log X)^2\), and the exact separation is \(k-h>H_0=X^{o(1)}\).

Partition \((U,2U]\) into the same cells used for the close-relative-shift detection, of length at most \(Q_X=UX^{-o(1)}\). In an off-line case \(\beta_*=\sup\Re\rho>1/2\), take \(Q_X=U\delta_X\) with the small shift \(\delta_X\) from that proof. At \(\beta_*=1/2\), take \(Q_X=\delta U\) for sufficiently small fixed \(\delta>0\). Retain actual pairs in the same cell with exactly one companion prime and one composite, both squarefree and \(z\)-rough, retaining the strict separation. They are automatically coprime because a multiple of a prime \(h>U\) other than \(h\) itself exceeds \(2U\). All these companions lie below \(H\) for large \(Y\). [Positive relative-shift cells](https://github.com/Sodelin/Research-Commons/commit/371ff8bc2032a4a70c0db9a4ed3b81eece58bb52) · [Exact surviving squarefree companions](https://github.com/Sodelin/Research-Commons/commit/99f45afcdd885d79b3474d4b867f3d0b0e640e21)

For every \(\varepsilon>0\), the signed mixed covariance of these cells is
\[
 O_\varepsilon(X^{2\beta_*-1+\varepsilon}).
\tag{1}
\]
This holds both with the original centered kernel and after excluding discrete prime atom divisors of \(hk\) and coincidences of the two discrete prime atoms. For \(1/2\le\beta_*<1\), the positive and negative masses of the actual same-cell mixed sum are separately of exponent
\[
 u+(1-u)(2\beta_*-1).
\tag{2}
\]
Thus the signed total is smaller by a fixed power than either mass, and those two masses are asymptotically equal. At \(\beta_*=1/2\) the same-cell signed upper bound is subpower. No square-root evaluation for the full separated covariance is inferred.

## Hard endpoint bounds for the composite scalar

In the entire band \(U<h\le2U\), the exact inverse coefficient is \(\beta_U(h)=\mu_L(h)\). In fact \(h=mn\) with \(m>U\) forces \(n<h/U\le2\), so only \(n=1\) is allowed. In a cell \(I\), write \(S_{\rm pr}(v)\) and \(S_{\rm co}(v)\) for the scalar sums \(\sum b_hg_P(v-\log h)\) over its prime and composite companions with the prescribed rough and squarefree restrictions. The original prime companion scalar is
\[
 S_{\rm pr}(v)=-x^{-1/2}\sum_{q\in I,\ {\rm prime}} a(q)E_P(x/q),
 \qquad x=e^v.
\]
Its bound \(O_\varepsilon(X^{\beta_*-1/2+\varepsilon})\) follows from the signed Artin prime prefix and the bounded variation of the fixed kernel, as in the all-prime cell proof.

For the whole cell the same bound holds on the sharp support, uniformly in its exact endpoints. For an unrestricted \(d\)-lane use the difference of the two sharp upper-tail estimates at the cell endpoints \(J_1,J_2\in[U,2U]\). In the auxiliary negative Perron integral take \(a=\Re s>\beta_*\) and \(a-\lambda>1/2\). At \(d=1\) use \(G_{U,1}=1-LM_U\). At \(d>1\) use \(G_{U,d}=-L^{(d)}J_{U,d}\) in that integral, which gives an additional \(d^{-c}\) for some fixed \(c>1/2\). Each cutoff \(J_i\ge U\) gives \(J_i^{-\lambda}U^{(\beta_*-(a-\lambda))_+}\le1\). The exact rough and squarefree projections preserve the same \(X\)-power and, at \(d>1\), an exponent of \(d\) still greater than \(1/2\), by their convergent weighted lcm products. Thus the whole cell gives \(O_\varepsilon(X^{\beta_*-1/2+\varepsilon})\). Subtract the prime scalar to obtain that same bound for \(S_{\rm co}\). [Sharp companion and \(d\)-projection Mellin proofs](https://github.com/Sodelin/Research-Commons/commit/cee389512c24de3ea6d0a90bb3c82f3b0c1e7ecc) · [Squarefree projection](https://github.com/Sodelin/Research-Commons/commit/99f45afcdd885d79b3474d4b867f3d0b0e640e21)

The all-mixed-pairs covariance within the cells is exactly
\[
 2\sum_I\int_{v_0}^V S_{\rm pr}(v)S_{\rm co}(v)\,dv ,
\]
before deleting close pairs. There are \(X^{o(1)}\) cells and the log-window length is subpower. The bound is therefore (1). The usual absolute estimate on the deleted short gaps is \(O_\varepsilon(H_0X^{(1-u)(2\beta_*-1)+\varepsilon})\), which fits the upper exponent in (1).

## Atom masks on the same mixed cells

For an individual split-prime atom \(p>P\), let \(A_{p,{\rm pr}}\) and \(A_{p,{\rm co}}\) be the scalar sums over the prime and composite companions in the cell, replacing each centered prime count by that atom:
\[
 A_{p,{\rm pr}}(v)
 =x^{-1/2}(\log p)\sum_{h\in I,\ {\rm prime}}\beta_U(h)K_B(ph/x),
\]
with the analogous sum over the prescribed composite support for \(A_{p,{\rm co}}\). A subscript \(d\) on a scalar denotes imposing \(d\mid h\) on that companion. With \(\Delta=\beta_*-1/2\), the whole-cell versions obey
\[
 |A_{p,{\rm all},d}|\ll_\varepsilon
              X^{u\Delta+\varepsilon}p^{-\sigma}d^{-\sigma},
 \qquad
 |S_{{\rm all},d}|\ll_\varepsilon X^{\Delta+\varepsilon}d^{-\sigma},
 \qquad \sigma>1/2.
\]
The single-atom proof is the same sharp Mellin difference at the two cell endpoints, now with scale \(x/p\) and without any prime transform in the integral. The rough and squarefree projections use the same weighted lcm estimates. For a prime-only atom scalar the prime prefix and \(K_B\) variation give
\[
 |A_{p,{\rm pr}}|\ll_\varepsilon X^{\Delta+\varepsilon}p^{-\beta_*+\varepsilon},
 \qquad
 |S_{{\rm pr},p}|\ll_\varepsilon X^{\Delta+\varepsilon}p^{-\beta_*+\varepsilon}.
\]
The first follows from the clipped prime companion range \(U<q\le e^Bx/p\). The second just selects the single companion \(h=p\) if it lies in the cell. Also
\(\sum_{p>P}|A_{p,{\rm pr},p}|\ll X^\varepsilon\) by Chebyshev, since the diagonal kernel \(K_B(p^2/x)\) forces \(p\ll_B\sqrt x\). Subtract the prime bounds from the whole-cell bounds when a composite-only restriction is needed. [Single-atom and masked covariance comparison](https://github.com/Sodelin/Research-Commons/commit/47e3ea8ecc114caac8d8afda0447b19920072d5a)

In the linear collision terms, when the atom divides its own companion the sums are \(\sum_p A_{p,{\rm pr},p}S_{\rm co}\) and \(\sum_p A_{p,{\rm co},p}S_{\rm pr}\). The preceding Chebyshev bound and the whole-cell bound \(\sum_p |A_{p,{\rm all},p}|\ll_\varepsilon X^{u\Delta+\varepsilon}\) put them strictly below \(X^{2\Delta}\) in an off-line case, and at subpower on the critical line. When the atom divides the other companion the sums are \(\sum_p A_{p,{\rm pr}}S_{{\rm co},p}\) and \(\sum_p A_{p,{\rm co}}S_{{\rm pr},p}\). The bounds reduce them to \(X^{2\Delta+\varepsilon}\) times tails of \(\sum_{p>P}(p^{-2\beta_*+\varepsilon}+p^{-\beta_*-\sigma+\varepsilon})\), with a fixed power saving when \(\Delta>0\) because \(P=Y^\alpha\), and at most subpower loss when \(\Delta=0\). The same estimate handles the coincident atom product \(\sum_p A_{p,{\rm pr}}A_{p,{\rm co}}\).

Intersections of two divisor masks, and the overlaps of a prime coincidence with a divisor mask, have a simpler absolute bound. Each normalized atom sum with its prime required to divide \(hk\) is \(O(X^{-1/2+\varepsilon})\), since the sum of its logarithmic factors is at most \(\log(hk)\). Each intersecting product then costs \(O(X^{-1+\varepsilon})\) per pair. There are \(O(U^2)\) pairs even before the cells, so \(u<1/2\) gives a fixed negative power. This handles the union by exact mask expansion, without assuming signs. Finally restore the separation. For a single divisor mask on close pairs the other coordinate uses the usual centered envelope, giving \(O_\varepsilon(X^{\beta_*-1+\varepsilon}H_0 U^{1-\beta_*+\varepsilon})\). For a coincident pair of atoms the absolute value is \(O_\varepsilon(X^\varepsilon/\max(h,k))\) per companion pair by Chebyshev. The resulting close corrections are below the off-line exponent and are subpower at the critical line. This proves (1) after the two atom deletions as well. The continuous references have stayed unchanged.

## Actual mixed contributions of each sign

For \(1/2\le\beta_*<1\), the \(\log p\)-weighted prime prefix in each Frobenius class has its Chebotarev main term and \(O_\varepsilon(t^{\beta_*+\varepsilon})\) error. This follows from the exact class indicators in terms of \(1,\chi,a\), the verified two Dirichlet prefixes, and the Artin prime prefix at its actual rightmost exponent. The identity and three-cycle densities are \(1/6\) and \(1/3\). On every full cell the first and last thirds have length comparable to \(Q_X=UX^{-o(1)}\), so the same fixed power error is smaller than the class main term there.

Choose one completely split prime \(q_0\in(z,2z]\), which exists by fixed-field Chebotarev. In each full cell take as first companions the completely split primes \(h\) in its first third. In the last third take \(k=q_0 r\), with \(r\) in either the three-cycle class or the completely split class. The same class prefix estimate after scaling by \(q_0\) applies, since \(q_0\) is polylogarithmic. Per cell there are \(\asymp Q_X/\log U\) choices of \(h\) and \(\asymp Q_X/(q_0\log U)\) choices of \(k\) of either type. Here \(r\) is eventually larger than \(q_0\), so each product is squarefree and rough. The gap exceeds \(H_0\) because the two thirds are separated by \(\gg Q_X\). This gives \(\asymp UQ_X/(q_0(\log U)^2)\) actual pairs of each type over the full cells.

The inverse signs on these pairs are exact. The prime \(h\) has \(\beta_U(h)=-2\). The composite \(k\) has \(\beta_U(k)=-2\) when \(r\) is a three-cycle, and \(+4\) when \(r\) splits completely. The original kernel correlations within a cell are positive, with off-line size \((X/U)^{2\Delta+o(1)}\) and critical-line size \(\asymp V-v_0\). Hence the chosen strata give both sign masses with exponent (2) before atom deletions.

In an off-line case the per-pair divisor-mask corrections are smaller by a fixed power. The per-pair coincident atom kernel, before multiplying by \(b_hb_k\), is \(O((V-v_0)\log X)\), which is also negligible against \((X/U)^{2\Delta-o(1)}\). Thus the signs of the chosen strata remain unchanged on the masked support. At \(\beta_*=1/2\) the effect is different. The normalized centered prime functions are uniformly bounded in these shifts by their absolutely convergent critical-line explicit formula, so their product integral is \(O(V-v_0)\). In contrast, the coincident atom contribution after removing divisors of \(hk\) is between positive constants times \((V-v_0)\log X\). To see this, at each \(v\) put \(T=x/\max(h,k)\asymp x/U\). The completely split primes in \((T/4,T/2]\) exceed \(P\) by a fixed power. Both kernels are constant and positive there, and fixed-field Chebotarev gives \(\sum \log^2 p\asymp T\log X\). Excluding the prime divisors of \(hk\) costs only \(O((\log X)^2)\) in that sum. The normalized product of prime weights supplies \(\sqrt{hk}/x\asymp1/T\), proving the lower bound, and Chebyshev proves the upper bound. This subtraction reverses the sign of the effective kernel on each such pair. The two actual inverse signs still yield both signs, now with the labels reversed and each selected mass of order
\[
 U(V-v_0)/(\log X)^3 .
\]
Before atom deletion each selected critical-line mass has order \(U(V-v_0)/(\log X)^4\). These logarithmic differences do not change exponent (2).

For an upper exponent on the entire mixed sign mass, there are at most \(O(UQ_X)\) ordered integer choices in the same cells. Use the divisor bound for \(\beta_U\), the individual centered kernel envelope, and the above absolute collision bounds per pair. This gives at most \(X^{u+(1-u)(2\beta_*-1)+\varepsilon}\) for each \(\varepsilon>0\), matching the selected lower exponent. Since
\[
 u+(1-u)(2\beta_*-1)-(2\beta_*-1)=2u(1-\beta_*)>0,
\]
the exact signed sum is \(o(1)\) times either mass. This is cancellation on the actual mixed prime–composite cells, with locked support and signs. These are hand arguments. The case \(\beta_*=1\) is covered by the signed upper bound (1), while the sign-mass count here uses the strict power error available for \(\beta_*<1\).

## Fixed polynomial cells and a cellwise conclusion

Fix \(\tau\) with \(u\beta_*<\tau<u\), possible when \(\beta_*<1\), and take any hard interval \(I\subset(U,2U]\) of length \(Q=X^\tau\). The signed estimate \(O_\varepsilon(X^{2\beta_*-1+\varepsilon})\) holds for this single cell, including the two prime-atom deletions. No averaging over cell positions is needed. Indeed the hard endpoint and single-atom bounds are uniform over all such positions, and the absolute close-gap corrections only decrease on the smaller support.

The relative shift \(Q/U=X^{\tau-u+o(1)}\) is smaller than the shift tolerance used in the off-line kernel lower bound. At the critical line all sufficiently small relative shifts are allowed as well. In the first and last thirds of this single cell the two Frobenius-class counts remain valid, since \(Q\gg U^{\beta_*+\varepsilon}\) after choosing a sufficiently small fixed \(\varepsilon>0\). This gives \(Q^2/(q_0(\log U)^2)\) pairs of each selected type, with the same atom-mask signs as before. The two sign masses in the entire cell therefore have exponent
\[
 2\tau-u+(1-u)(2\beta_*-1)
\]
each, using the \(O(Q^2)\) count for the upper exponent. This exceeds the signed exponent \(2\beta_*-1\) by \(2(\tau-u\beta_*)>0\). If the full band is divided into polynomial cells, summing the individual signed estimates gives \(O_\varepsilon(X^{2\beta_*-1+u-\tau+\varepsilon})\), while either sign mass has exponent \(\tau+(1-u)(2\beta_*-1)\). The same strict exponent gap remains. This is an actual cellwise cancellation statement at polynomial additive separations.
