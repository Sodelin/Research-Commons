# A signed cross-cell bound with a large prime in one companion

Fix the standard \(S_3\) Artin factor and the original locked cutoffs \(U=\lfloor Y^u\rfloor\), \(P=Y^\alpha\), \(H=Y^{u+\kappa}\), where \(u+\alpha+\kappa<1\). As before \(v_0=\log Y\), \(V=\log X\), \(V-v_0\to\infty\), and \(X=Y^{1+o(1)}\). The retained companions are in \((U,H]\), squarefree, coprime in pairs, and \((\log X)^2\)-rough. Write \(b_h=\beta_U(h)/\sqrt h\) and \(f_h(v)=g_P(v-\log h)\), keeping the original kernel and centering. [Exact surviving pair support](https://github.com/Sodelin/Research-Commons/commit/99f45afcdd885d79b3474d4b867f3d0b0e640e21) · [Exact prime-atom masks](https://github.com/Sodelin/Research-Commons/commit/47e3ea8ecc114caac8d8afda0447b19920072d5a)

Take two hard cells \(I,J\) in possibly different dyadic companion bands of scales \(R_1,R_2\), with \(U\le R_i\le H\), and lengths \(Q_1,Q_2\). For each \(k\in J\), impose on the first companion \(h\) any exact interval restriction within \(I\), in addition to the original squarefree, rough and coprime requirements. This allows strict additive or relative gaps, including the original separation. Require the first companion to have \(P^+(h)>T\). The threshold can be any fixed \(T=Y^\theta\) with \(\theta>0\), or the subpower threshold
\[
 T=T_I=\exp(\sqrt{\log X})(R_1/Q_1)^{12}
\]
on the subpower-relative cells specified below. The second companion may be prime or composite, with any extra restriction on \(k\) alone. The first companion may also be required composite.

Choose the local cells as below, with \(Q_i=R_iX^{-o(1)}\), and write \(A_I,A_J\) for the \(L^2([v_0,V])\) norms of \(f_h,f_k\) at reference companions in the respective real cells. For every fixed \(A>0\), the signed covariance of these actual pairs is
\[
 O_A\left(
 \frac{Q_1Q_2 A_I A_J}
      {\sqrt{R_1R_2}(\log X)^A}
 \right).
\tag{1}
\]
This bound applies also after excluding the discrete prime atoms dividing \(hk\) and coincident discrete atoms. It uses no upper estimate for the full Artin covariance. It applies in particular to composite–composite cross cells with a large prime factor on one side.

## Local variation on the actual shifted windows

On a dyadic range \([R,2R]\) clipped to \((U,H]\), with \(\beta_*=\sup\Re\rho\) and \(\Delta=\beta_*-1/2>0\), the original fixed-length detector and the prefix comparison give, uniformly over \(h\) in the band,
\[
 (X/R)^{\Delta-o(1)}\ll\|f_h\|_2\ll (X/R)^{\Delta+o(1)}.
\]
The proof from the lower companion band works here because \(PH\ll Y\) by a fixed power. For the fixed zero chosen in the lower proof, its real part can be taken close enough to \(\beta_*\) that \((1-u-\kappa)\Re\rho>\alpha\beta_*\). This makes the exact finite prime cutoff error negligible at every shift in the band. The differentiated \(K_B\) identity bounds \(\|\partial_h f_h\|_2\) by \(R^{-1}(X/R)^{\Delta+o(1)}\) uniformly there. A cell of length at most \(R\delta_R\), for a suitable \(\delta_R=X^{-o(1)}\), therefore gives \(L^2\) variation at most \(A_I/4\) for \(f_h\) on that cell. In particular all norms there are comparable to \(A_I\), and the supremum plus total variation of \(h^{-1/2}f_h\) is \(O(A_I/\sqrt R)\).

At \(\beta_*=1/2\), the critical-line formula gives \(A_I\asymp\sqrt{V-v_0}\) uniformly on these shifts. The differentiated kernel and the square-root times polylogarithmic prime prefix bound give the same variation estimate with a fixed logarithmic factor, which can be absorbed. These claims hold whenever the cells are contained in the dyadic ranges stated above. [Original relative shift proof](https://github.com/Sodelin/Research-Commons/commit/371ff8bc2032a4a70c0db9a4ed3b81eece58bb52) · [Critical-line derivative and Hilbert Abel estimate](https://github.com/Sodelin/Research-Commons/commit/7972455b5c69c9a3c4a0d9dd3bc9b88ad75336d2)

## Prime trace cancellation in the exact largest-prime lanes

For the fixed degree-six splitting field, short-interval Chebotarev gives arbitrary log-power error on each Frobenius-class prime count on lengths at least \(t^{5/6+\delta}\) at height \(t\), where \(\delta>0\) is fixed. This is the \(c(L)=6\) case of Balog–Ono's theorem. The logarithmic strengthening follows by increasing the power of \(\log t\) in their truncation height. Since the class mean of the Artin trace is zero, the signed prime-trace prefix over any clipped subinterval of a window of length \(Q'\ge t^{5/6+2\delta}\) is \(O_A(Q'/\log^A t)\). For prefixes shorter than \(t^{5/6+\delta}\) this bound follows from the trivial count and the fixed margin. [Balog–Ono, Theorem 2 and equations (3.2)–(3.5)](https://uva.theopenscholar.com/files/ken-ono/files/062.pdf)

Take \(h=q r\), where \(q=P^+(h)>T\) is the unique largest prime of the squarefree \(h\). The squarefree formula \(\beta_U(h)=\mu_L(h)\sum_{c\mid h,\,c<h/U}\mu(c)\) separates exactly into \(c=d\) and \(c=qd\), where \(d\mid r\). In the first part the criterion is \(q>Ud/r\). In the second part it is \(d<r/U\), independent of \(q\), and \(\mu(qd)=-\mu(d)\). Since \(\mu_L(qr)=-a(q)\mu_L(r)\), the exact identity is
\[
 \beta_U(qr)=-a(q)\mu_L(r)
      \sum_{d\mid r}\mu(d)
             \left(\mathbf1_{q>Ud/r}-\mathbf1_{d<r/U}\right).
\tag{2}
\]
Both tests remain strict. For fixed \(k,r,d\), the condition \(h=qr\in I\) and its allowed interval for that \(k\) are a real interval in \(q\). The conditions \(q>P^+(r)\) and \(q>T\) move the lower endpoint in each term of (2). In the first term one also moves that endpoint by \(q>Ud/r\). In the second one either keeps or discards the interval via the \(q\)-independent test. Coprimality asks \((r,k)=1\) and \(q\nmid k\). All factors of \(r\) must be rough and \(r\) squarefree. If the first companion must be composite, simply omit \(r=1\).

The \(q\)-scale is \(t=R_1/r\), and the corresponding full cell has length \(Q'=Q_1/r\). Whenever either term has nonempty support, \(t\ge T/2\). For fixed polynomial \(T=Y^\theta\) and subpower-relative \(Q_1\) one has \(Q'\ge t^{5/6+2\delta}\) for a fixed \(\delta>0\) uniformly. For \(T=T_I\), use \(\delta=1/24\). Indeed \(t^{1/12}\ge 2^{-1/12}\exp(\sqrt{\log X}/12)(R_1/Q_1)\), which gives \(Q'=t(Q_1/R_1)\ge t^{11/12}\) for large \(X\). Also \(\log t\gg\sqrt{\log X}\), so arbitrary logarithmic savings in \(t\) give arbitrary logarithmic savings in \(X\). At most \(O(\log X/\log T)\) primes \(q>T\) divide \(k\), and this is at most \(O(\sqrt{\log X})\) for the subpower threshold. Their bounded coefficients are absorbed by \(Q'/(\log X)^A\) for every fixed \(A\). The clipped prime-trace prefix bound therefore applies on both exact cutoff terms in (2).

Apply \(L^2\)-valued Abel summation to \(q\mapsto(qr)^{-1/2}f_{qr}\) on that exact interval. Its variation is bounded by the whole \(h\)-cell variation. After expanding (2), sum over \(r,d\) using
\[
 \sum_{r\le 2R_1/T}\frac{|\mu_L(r)|d_2(r)}r
       \ll(\log X)^4 ,
\]
which follows from \(d_2(r)^2\le d_4(r)\). It gives, for each fixed \(k\), a signed first-companion \(L^2\) norm at most \(O_A(Q_1A_I/(\sqrt{R_1}(\log X)^A))\). On \(J\), the absolute weight sum satisfies \(\sum_{k\in J}|\beta_U(k)|\ll Q_2(\log X)^3\). Indeed \(|\beta_U|\le d_4\), and \(\sum_{k\in J}d_4(k)\ll Q_2(\log X)^3+R_2^{3/4}(\log X)^2\) by choosing a largest member of a four-factor decomposition and counting multiples of the product of the three others. Multiply the first signed bound by the absolute second-companion norm \(A_J|\beta_U(k)|/\sqrt{R_2}\), and sum over \(k\). This proves (1) before atom edits.

## The exact discrete-atom masks

For any fixed companion pair, one divisor-selected normalized atom sum has \(L^2\) norm
\(O(X^{-1/2+o(1)}|\beta_U(h)|\sqrt{V-v_0})\), since its \(\log p\) weights have sum at most \(\log(hk)\). Multiplication by the other coordinate and summation by the two absolute divisor bounds therefore cost a fixed power below the scale \(Q_1Q_2A_IA_J/\sqrt{R_1R_2}\): the ratio includes
\(\sqrt{R_i/X}\sqrt{V-v_0}/A_I\), and both \(R_i\) lie below \(X\) by a fixed power. The analogous two-mask product is smaller. Expand the two masks exactly, so the intersection signs are included.

After those two masks, the coincident discrete atom term is a sum over \(k\) and split primes \(p>P\) with \(p\nmid k\). Its first-companion sum is the same one from (2), but against \(K_B(ph/x)\) and with \(p\nmid h\). For fixed \(k,p,r,d\) this adds \((p,r)=1\) and omits at most one more prime \(q=p\). The \(K_B\) factor is bounded and monotone as a function of \(h\), so scalar Abel summation gives \(O_A(Q_1/(\log X)^A)\) after the same sum over \(r,d\). The remaining output-prime sum of \((\log p)^2\) is \(O((x/\max(R_1,R_2))\log X)\) by Chebyshev, on its exact product support. The \(x^{-1}\) normalization of the two atoms and \(k\)-absolute bound give
\[
 O_A\left(
 \frac{(V-v_0)Q_1Q_2}
      {\max(R_1,R_2)(\log X)^A}
 \right).
\]
This is within (1) because \(A_IA_J\gg V-v_0\) for sufficiently late windows, with a fixed power margin in the off-line case. Hence the exact masks and moving separation remain valid, without changing the continuous reference.

If \(Q_1\) is a fixed polynomial cell length, the short-interval condition used above holds whenever, with a fixed exponent margin, \(Q_1\ge R_1 Y^{-\theta/6+\epsilon}\) and \(Q_1/R_1\) is within the local shift tolerance. The second cell only needs the interval divisor bound to be at the claimed scale. The main scope of (1) is the original subpower-relative cell width on both sides, at arbitrary separation between the cells.

The bound is relative to the product of the two Hilbert norms times \(Q_1Q_2/\sqrt{R_1R_2}\). It need not make this sector smaller than the absolute covariance scale \(X^{2\beta_*-1}\). For example with \(R_1\asymp R_2\asymp U\) and subpower-relative lengths, the reference product can have exponent \(u+(1-u)(2\beta_*-1)\). When the cross-cell kernel has a uniform lower bound of the appropriate sign, the result also bounds the signed value relative to actual sign masses obtained from Frobenius strata. For arbitrary ratios with no isolated top spectrum, the small-shift argument supplies no such lower bound on the angle between reference functions. Using the subpower threshold \(T_I\) leaves the contribution where both companions are smooth at the appropriate cell thresholds unestimated by this row argument. These are hand arguments.

## An absolute smooth-row bound for quantitatively longer cells

There is a useful further case where the smooth–smooth contribution is negligible *on the same relative scale*. Suppose the selected cells satisfy both the variation condition and
\[
 R_i e^{-C\sqrt{\log X}}\le Q_i\le R_i
\]
for a fixed \(C>0\). Then (1) holds without requiring a large prime factor in either companion. Indeed \(\log T_i=O_C(\sqrt{\log X})\) for the two subpower thresholds. Put \(L=\log X\), \(R=R_i\), \(T=T_i\) and \(\eta=(\log L)/(4\log T)\). The elementary Rankin bound gives
\[
 \sum_{\substack{n\le 2R\\P^+(n)\le T}}d_4(n)
 \le (2R)^{1-\eta}
        \prod_{p\le T}(1-p^{-1+\eta})^{-4}.
\]
Here \(T^\eta=L^{1/4}\), and the logarithm of the product is at most \(O(L^{1/4}\log\log T)\) by the prime reciprocal sum. On the other hand \(\eta\log R\gg\sqrt L\log L\) because \(R\ge U\). Thus the bound is \(O(R\exp(-c\sqrt L\log L))\), and is \(O_A(Q_i/(\log X)^A)\) for every \(A\).

This controls the smooth companion's absolute weight independently of the other companion and every pair restriction. Each original pair kernel is at most \(A_IA_J\) up to fixed constants by Cauchy–Schwarz. Removing divisor atoms changes its absolute bound by only a smaller power, and removing the coincident atom term costs at most a logarithmic factor relative to \(A_IA_J\), by the same Chebyshev estimate on the output support. Hence this smooth bound absorbs both masks. Partition by the first companion only. The smooth first companion is covered by the absolute estimate, and (1) handles its large-prime complement. Thus the same exact interval-shaped restriction on the first coordinate continues to suffice. This proves the full cross-cell relative upper bound in the stated width regime. It still does not give the absolute subpower bound for the original covariance.

The width regime is available on the critical line and also whenever an off-line rightmost abscissa is attained. In the attained case, no gap to lower zeros is needed. The absolute smoothed residue expansion, divided by \(t^\Delta\) for the normalized observable at the shifted scale \(t=x/h\), is its top-frequency series plus a uniform \(o(1)\) by dominated convergence. A fixed length has positive normalized mean square for this nonzero top series. The same applies to the clipped prime profile by the strict \(P\)-cutoff comparison. Thus \(A_I\gg(X/R_i)^\Delta\) on every relevant late shifted window. On the other hand truncated Perron at \(s=\beta_*+1/\log t\) gives the sharp bound \(O(t^{\beta_*}(\log t)^3)\) for the ordinary signed Artin prime prefix. On that line all zero denominators are separated horizontally by \(1/\log t\), so the local logarithmic derivative costs \(O((\log t)\log(3+|\Im s|))\). The original derivative identity for \(K_B\) then gives log-cell variation strength \(O((X/R_i)^\Delta(\log X)^C)\). It follows that a polylogarithmic relative cell width retains the Hilbert variation requirement. At \(\beta_*=1/2\), the critical-line formula and derivative bound give the same conclusion. For a general nonattained off-line supremum the earlier proof gives only \(Q_i=R_iX^{-o(1)}\) with no rate, which is why the Rankin comparison does not alone handle the remaining smooth–smooth cells there. [Pinned attained-line expansion and terminal mean square](https://github.com/Sodelin/Research-Commons/commit/30ae754053ae028ae3a5c24e4383ca330a532a70)
