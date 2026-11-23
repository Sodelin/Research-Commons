# Prime-atom collision removal in the actual \(S_3\) covariance

Use the original locked cutoffs \(U=\lfloor Y^u\rfloor\), \(P=Y^\alpha\), \(H=Y^{u+\kappa}\) with \(u+\alpha+\kappa<1\), \(X=Y^{1+o(1)}\), and \(z=(\log X)^2\). The remaining companions are squarefree, \(z\)-rough, and have \(U<h<k\le H\), \((h,k)=1\), \(k-h>H_0=X^{o(1)}\). Expand each centered prime measure into its discrete split-prime atoms and its exact continuous reference on \(t>P\). The following exact sectors can be deleted at a fixed off-line exponent gap, and at subpower cost on the critical line.

- Any term in which a discrete prime atom divides \(hk\).
- Any term in which both prime coordinates are discrete and coincide.

All continuous references stay on the original support. In a discrete–continuous term only the discrete atom is subject to the divisibility restriction. The comparison leaves the original sign in every retained summand and the same integral against the window kernel. [Exact surviving companion band](https://github.com/Sodelin/Research-Commons/commit/99f45afcdd885d79b3474d4b867f3d0b0e640e21)

## A single atom tested against the inverse coefficients

Let \(\mathcal H=\{h:U<h\le H,\ P^-(h)>z,\ \mu^2(h)=1\}\). Write \(x=e^v\) and
\[
 A_{p,d}(v)=x^{-1/2}(\log p)
      \sum_{\substack{h\in\mathcal H\\d\mid h}}\beta_U(h)K_B(ph/x),
 \qquad
 S_d(v)=\sum_{\substack{h\in\mathcal H\\d\mid h}}b_hg_P(v-\log h).
\]
Here \(p>P\) is a split rational prime, \(d\ge1\), and \(S_d\) retains both its discrete part and its exact continuous reference. Put \(\Delta=\beta_*-1/2\). For every prescribed \(\varepsilon>0\), some fixed \(\sigma>1/2\) gives
\[
 |A_{p,d}(v)|\ll_\varepsilon
          X^{u\Delta+\varepsilon}p^{-\sigma}d^{-\sigma},
 \qquad
 |S_d(v)|\ll_\varepsilon X^{\Delta+\varepsilon}d^{-\sigma}.
\tag{1}
\]
The second bound is the full companion envelope at \(d=1\) and the known divisibility-lane estimate together with the existing squarefree and rough projections at \(d>1\). [Sharp divisibility lanes](https://github.com/Sodelin/Research-Commons/commit/cee389512c24de3ea6d0a90bb3c82f3b0c1e7ecc)

For the first bound start without the rough and squarefree restrictions. The untruncated Dirichlet series for the \(d\)-lane is \(G_{U,d}=1-LM_U\) at \(d=1\), and \(-L^{(d)}J_{U,d}\) at \(d>1\), with the twisted bound
\[
 |J_{U,d}(s)|\ll_\eta
 d^{-\Re s+\eta}U^{(\beta_*-\Re s)_++\eta}(3+|\Im s|)^\eta
\]
on a fixed real line greater than \(1/2\). The same bound with \(d=1\) holds for \(M_U\). In Mellin inversion for this single atom the scale is \(x/p\), and no prime transform occurs. Shift the Mellin line to \(a=1/2+2\delta\) for sufficiently small fixed \(\delta>0\). The \(H_B\) decay and degree-two convexity make the untruncated integral convergent.

To impose the hard upper endpoint \(H\), subtract the tail using a truncated auxiliary Perron integral at \(\Re w=-\delta\), with height \(X^{10}\) and half-integer \(H'=\lfloor H\rfloor+1/2\), which gives the same integer cutoff. The \(G_{U,d}\) factor is now evaluated at \(\Re(s+w)=1/2+\delta\). The fixed degree-two mean square of \(L\) on this line and the \(1/w\) integral give the auxiliary bound used for sharp companion localization. The local Euler factors from \(L^{(d)}\) cost an arbitrary small power of \(d\). This bounds the tail, before normalization, by
\[
 O_\eta\left(
 (x/p)^a H^{-\delta}
 U^{(\beta_*-(a-\delta))_++\eta}
 d^{-(a-\delta)+\eta}X^{O(\eta)}\right),
\]
with the same bound interpreted at \(d=1\) by treating the constant in \(G_{U,1}\) separately. On active support \(p\le e^Bx/U\), so \(x/p\) is still at least a fixed positive power of \(X\). All half-integer truncation errors are negligible uniformly in \(p,d\le O_B(X)\). The full lane has the bound without \(H^{-\delta}\), using real argument \(a\) for \(G_{U,d}\). Since \(H>U\), the factor \(H^{-\delta}U^{(\beta_*-(a-\delta))_+}\) is at most \(U^\Delta\). Multiply by \(x^{-1/2}\log p\). Choose \(\delta\) small relative to the final \(\varepsilon\), then choose \(\eta\) small relative to \(\delta\), leaving a fixed exponent greater than \(1/2\) in both \(p\) and \(d\). This proves the first bound before the two remaining restrictions.

For rough and squarefree support use the exact double inclusion
\[
 A^{\rm rough,sf}_{p,d}
 =\sum_{e\mid\mathfrak p_z}\sum_{m\ge1}
       \mu(e)\mu(m) A^{\rm unfiltered}_{p,\operatorname{lcm}(d,e,m^2)} .
\]
If \(d\) has a prime factor at most \(z\) or is nonsquarefree, the actual left side vanishes. Otherwise \(d\) is squarefree and coprime to \(\mathfrak p_z\). At local primes \(q\le z\) the absolute sum in \(e,m\) gives \(1+q^{-\sigma}+2q^{-2\sigma}\). At \(q>z\) outside \(d\) it gives \(1+q^{-2\sigma}\). At \(q\mid d\) it gives \(q^{-\sigma}(1+q^{-\sigma})\). Their product costs \(X^{o(1)} d^{-\sigma+\eta}\) since \(\sigma>1/2\) and \(z=(\log X)^2\), as in the previous rough and squarefree projections. Lower the common exponent slightly, staying above \(1/2\). This proves (1) for the actual \(\mathcal H\).

## Divisibility, shared primes and the exact gcd projection

First work with all ordered pairs \((h,k)\) in \(\mathcal H\) subject to \((h,k)=1\). The equality
\(\sum_{d\mid h,\,d\mid k}\mu(d)=\mathbf1_{(h,k)=1}\)
imposes that condition exactly. For example the covariance product in which the atom in the first coordinate divides \(k\) is, pointwise in \(v\), exactly
\[
 \sum_d\mu(d)\sum_{p>P,\ {\rm split}}
       A_{p,d}(v) S_{\operatorname{lcm}(d,p)}(v).
\tag{2}
\]
For the atom dividing \(h\), use \(A_{p,\operatorname{lcm}(d,p)}S_d\). Their sums are absolutely majorized by
\[
 X^{(1+u)\Delta+O(\varepsilon)}
       \sum_d d^{-\sigma}\sum_p
                  p^{-\sigma}\operatorname{lcm}(d,p)^{-\sigma}.
\]
The inner sum is \(O_{\sigma,\eta}(d^{-\sigma+\eta})\), by treating \(p\nmid d\) with the absolutely summable \(p^{-2\sigma}\), and \(p\mid d\) with \(\sum_{p\mid d}p^{-\sigma}\ll_\eta d^\eta\). Choose \(\eta<2\sigma-1\). Thus the total in (2) is \(O(X^{(1+u)\Delta+O(\varepsilon)})\), with a strict gap from \(2\Delta\) if \(\Delta>0\).

For each coprime pair, let \(B_h\) be the normalized first-coordinate atom sum over \(p\mid hk\), and let \(B_k\) be the analogous second-coordinate atom sum. The masked product equals the original product minus the two linear collision terms plus \(B_hB_k\). Within a single atom sum the cases \(p\mid h\) and \(p\mid k\) are disjoint. Expand \(B_hB_k\) into the four possible assignments of the two prime divisors. If the two atoms divide different companions, its Möbius lanes have factors \(A_{p,\operatorname{lcm}(d,p)} A_{q,\operatorname{lcm}(d,q)}\), or the crossed assignment \(A_{p,\operatorname{lcm}(d,q)} A_{q,\operatorname{lcm}(d,p)}\). The same majorant above now factors into two \(p\)-sums and is square summable in \(d\). If both atoms divide the same companion, the factors use \(A_{p,\operatorname{lcm}(d,p,q)} A_{q,d}\) or its reverse. For distinct \(p,q\) the sums split according to whether each prime divides \(d\), with \(p^{-2\sigma}\) and \(q^{-2\sigma}\) on the uncaptured primes. For \(p=q\) the product has \(p^{-2\sigma}\) already. This again gives a square-summable \(d\)-weight up to arbitrarily small divisor powers. All these intersection costs are \(O(X^{2u\Delta+O(\varepsilon)})\). These identities ensure that the sign of the union of collisions is preserved.

After removing the divisor collisions, the remaining coincident discrete atoms \(p=q\) have exact Möbius sum
\[
 \sum_d\mu(d)\sum_{p>P,\ {\rm split}}
       \left(A_{p,d}(v)-A_{p,\operatorname{lcm}(d,p)}(v)\right)^2 .
\]
The two \(A\) terms impose \(p\nmid h\) and \(p\nmid k\). The absolute majorant from (1) is \(O(X^{2u\Delta+O(\varepsilon)})\) by \(\sum p^{-2\sigma}\sum d^{-2\sigma}<\infty\). Thus both collision deletions are lower order on the all-pairs coprime support.

## Restoring the actual separation condition

To restrict these comparisons to \(|h-k|>H_0\), subtract the corresponding close pairs. A divisor-selected normalized atom sum \(B_h\) is bounded absolutely by \(O(X^{-1/2+\varepsilon})\). Indeed \(\sum_{p\mid hk}\log p\le\log(hk)\) and \(|\beta_U(h)|\ll_\varepsilon h^\varepsilon\). The other original normalized coordinate is bounded by \(O_\varepsilon(X^{\beta_*-1/2+\varepsilon}k^{-\beta_*+\varepsilon})\). The one-mask close terms therefore cost
\[
 O_\varepsilon\left(
 X^{\beta_*-1+\varepsilon}H_0
       \sum_{U<k\le H}k^{-\beta_*+\varepsilon}\right),
\]
which has a strict off-line gap and is subpower at \(\beta_*=1/2\). Indeed \(u+\kappa<1\) and \(\beta_*\ge1/2\). The two-mask close terms cost \(O(X^{-1+\varepsilon}H H_0)\), smaller still. For the coincident atom term, the exact support is \(p\le e^Bx/\max(h,k)\). Chebyshev bounds its absolute mass in a fixed normalized pair by \(O_\varepsilon(X^\varepsilon/\max(h,k))\), so all the close pairs cost \(O_\varepsilon(X^\varepsilon H_0\log X)\). This is subpower even without the prime-side divisibility restrictions. Integrating over the original log window absorbs its length into the arbitrary power loss. It follows that the two deletion statements are valid on the actual separated covariance with all original sharp endpoints.

This calculation concerns only these atom collisions. The residual signed covariance on the remaining companions and prime coordinates requires an additional estimate. These are hand arguments.
