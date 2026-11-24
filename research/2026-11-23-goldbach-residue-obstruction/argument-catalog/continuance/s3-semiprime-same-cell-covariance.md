# Same-cell cancellation on rough semiprime companions

Fix the standard \(S_3\) factor \(L\) and the original log windows \(v_0=\log Y\le v\le V=\log X\), with \(V-v_0\to\infty\) and \(V-v_0=o(V)\). Use the balanced polynomial cutoffs
\[
 U=\lfloor Y^u\rfloor,\qquad P=Y^u,\qquad H=Y^{u+\kappa},
 \qquad 1/3<u<1/2,\quad 0<\kappa<1-2u.
\]
Let \(z=(\log X)^2\), \(Z=\exp(\sqrt{\log X})\) and \(H_0=X^{o(1)}\) denote the original gap cutoff. Let \(\beta_*=\sup_\rho\Re\rho\) for this fixed Artin factor. The arguments use the verified Dirichlet input where the original split-prime centering does. They retain its locked prime parameter \(P\), the exact inverse coefficients and the same \(K_B(t)=e^{-B}(e^B/t-1)_+-(1/t-1)_+\). [Pinned positive prime slice and same-cell estimate](https://github.com/Sodelin/Research-Commons/commit/371ff8bc2032a4a70c0db9a4ed3b81eece58bb52) · [Pinned squarefree companion support](https://github.com/Sodelin/Research-Commons/commit/99f45afcdd885d79b3474d4b867f3d0b0e640e21)

A fixed integer cofactor \(r>1\) is excluded by the original roughness requirement as \(X\to\infty\). The exact surviving analogue is to take
\[
 \mathcal A=\{h=rp:\ U<h\le2U,\quad z<r\le Z,\quad
 r\text{ a completely split prime},\quad p\text{ prime}\}.
\tag{1}
\]
For each \(h\) the two factors are distinct and uniquely identified by their ranges, since \(p\ge U/Z\gg Z\). Every member is rough and squarefree. Let \(\mathcal A_+\) be the subset where \(p\) also splits completely. At \(h\le2U\), every proper divisor of \(h\) is at most \(U\). Thus the exact coefficient is
\[
 \beta_U(h)=\mu_L(h)=\mu_L(r)\mu_L(p)=2a(p),
\tag{2}
\]
so it equals \(4\) on \(\mathcal A_+\), \(-2\) if \(p\) is a 3-cycle prime and \(0\) on transpositions. If \(h=rp\) and \(k=sq\) are distinct elements of (1), they are coprime exactly when \(r\ne s\) and \(p\ne q\).

## The same-cell coprime slice has macroscopic one-sign mass

Write \(E_P(t)\) for the original centered split-prime function and \(g_P(w)=e^{-w/2}E_P(e^w)\). The covariance contribution of an unordered pair is
\[
 2\frac{\beta_U(h)\beta_U(k)}{\sqrt{hk}}
       \int_{v_0}^V g_P(v-\log h)g_P(v-\log k)\,dv.
\tag{3}
\]
When \(\beta_*>1/2\), use the adaptive cell width \(Q=U X^{-o(1)}\) from the pinned positive prime slice, with \(Q/U\to0\). On \([U,2U]\) the individual correlations of any pair with \(|h-k|\le Q\) are positive with uniform lower and upper exponent \((1-u)(2\beta_*-1)\), regardless of attainment of the supremum. That argument uses only the uniform uncut prime lower signal, exact \(P\)-centering and continuity in the log shift. When \(\beta_*=1/2\), choose instead a small fixed \(Q/U>0\). The critical Fourier expansion and its nonzero square bias give a positive correlation of size \(\asymp V-v_0\) uniformly on these relative shifts. All these comparisons depend only on the positions \(h,k\), so apply to the composite companions (1). Partition \((U,2U]\) into cells \(I_j\) of length at most \(Q\).

There are
\[
 N_+=|\mathcal A_+|\sim \frac{U\log\log X}{72\log U}
\tag{4}
\]
such positive companions. Indeed the split primes in \((U/r,2U/r]\) number \((1+o(1))U/(6r\log U)\), uniformly for \(z<r\le Z\) by fixed-field Chebotarev and \(\log(U/r)=(1+o(1))\log U\). Partial summation gives
\[
 \sum_{z<r\le Z,\ {\rm split}}\frac1r
   =(1+o(1))\frac16(\log\log Z-\log\log z)
   \sim \frac1{12}\log\log X .
\]
The same argument with all primes \(p\) gives \(|\mathcal A|\asymp N_+\). Cells and Cauchy–Schwarz give \(\gg N_+^2 Q/U\) unordered same-cell pairs from \(\mathcal A_+\). This is the scale against which all forbidden pairs are counted. [Fixed-field Chebotarev, Lagarias–Odlyzko Theorem 1.3](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf)

Pairs sharing their small prime \(r\) are bounded by
\[
 \ll \frac{U}{\log U}\!
          \sum_{\substack{z<r\le Z\\r\ {\rm split}}}
            \frac{1+Q/r}{r}
 \ll N_+ + \frac{UQ}{z\log U}.
\]
To see this, use at most \(1+Q/r\) integer companion primes within the permitted gap for each first \(h\), and at most \(O(U/(r\log U))\) choices of that first \(h\). Both displayed terms are \(o(N_+^2Q/U)\) by (4), \(z=(\log X)^2\) and \(Q=X^{u-o(1)}\). Pairs sharing the large prime \(p\) number at most \(O(ZN_+)\), also smaller. Finally at most \(O(N_+(1+Q/(\log X)^3))\) pairs have gap at most \(Q/(\log X)^3\), again smaller. Thus
\[
 \gg \frac{UQ(\log\log X)^2}{(\log U)^2}
\tag{5}
\]
of the actual same-cell pairs from \(\mathcal A_+\) are coprime and have
\(Q/(\log X)^3<k-h\le Q\). This lower endpoint exceeds \(H_0\). Their upper endpoint lies below \(H\). All their weights in (3) have fixed positive sign before output-atom diagonal removal.

When \(\beta_*>1/2\), (3) and (5) give this positive slice the exact exponent
\[
 u+(1-u)(2\beta_*-1),
\tag{6}
\]
where upper and lower estimates are allowed \(X^{o(1)}\) factors. The upper exponent follows from at most \(O(UQ)\) integer pairs and the individual kernel bound. When \(\beta_*=1/2\), the positive slice has order
\[
 \frac{U(V-v_0)(\log\log X)^2}{(\log U)^2}.
\tag{7}
\]
In the critical case \(Q\asymp U\), so the upper bound follows from \(N_+^2\), and the lower bound from (5).

## The signed same-cell semiprime covariance is much smaller

Let \(x=e^v\). In a fixed cell the unmasked scalar for a fixed \(r\) is
\[
 S_{r,j}(v)=x^{-1/2}
       \sum_{\substack{h=rp\in\mathcal A\cap I_j}}
              2a(p)E_P(x/h).
\]
The supremum plus total variation of the multiplicative-coordinate weight
\(x^{-1/2}E_P(x/h)\) on \(U<h\le2U\) is
\(O_\epsilon(X^{\beta_*-1/2+\epsilon}U^{-\beta_*+\epsilon})\), by the exact kernel derivative and fixed prime-prefix bound. The total variation bound is unchanged when the argument is \(h=rp\) and the prime variable is \(p\). The signed prime prefix \(\sum_{p\le t}a(p)=O_\epsilon(t^{\beta_*+\epsilon})\) therefore gives
\[
 S_{r,j}(v)\ll_\epsilon
       X^{\beta_*-1/2+\epsilon}r^{-\beta_*+\epsilon}.
\tag{8}
\]
There are \(X^{o(1)}\) small cofactors and \(X^{o(1)}\) cells. Thus all signed same-cell pairs, including the diagonal, have covariance
\(\sum_j\int(\sum_r S_{r,j})^2\,dv\ll_\epsilon X^{2\beta_*-1+\epsilon}\).
The signed same-\(r\) pairs give exactly \(\sum_{r,j}\int S_{r,j}^2\,dv\) and satisfy the same upper bound. Shared large-prime \(p\) pairs cost at most \(Z X^{(1-u)(2\beta_*-1)+o(1)}\) absolutely, since each integer companion has \(O(Z)\) possible companions sharing \(p\), the coefficients are \(O(1/U)\) per pair and the kernel is bounded on the window. Their intersection is just the diagonal, also covered by this absolute estimate. Finally pairs with gap at most \(H_0\) cost at most \(H_0 X^{(1-u)(2\beta_*-1)+o(1)}\). It follows that the exact same-cell covariance on
\[
 h,k\in\mathcal A,\quad h<k,\quad (h,k)=1,\quad k-h>H_0
\tag{9}
\]
is \(O_\epsilon(X^{2\beta_*-1+\epsilon})\). No deletion of an individual sign class is used here.

Every kernel correlation in these cells is positive before output-atom masks. By (2), the same large-prime conjugacy classes give positive pair products, and mixed identity–3-cycle large-prime classes give negative products. When \(1/2\le\beta_*<1\), the latter cancel the former up to relative \(o(1)\) on (9). The strict exponent gap comes from (6) and \(u>0\), and at \(\beta_*=1/2\) from (7). At \(\beta_*=1\), the exponent comparison is equality and gives no forced relative cancellation.

## The same comparison after the exact output-atom restrictions

The current covariance also omits discrete output prime atoms dividing \(hk\), and omits coincident discrete atoms in both output coordinates. The divisor restriction is automatic on (1): \(r\le Z<P\), and \(p\le2U/z<P\), so no atom \(q>P\) divides a companion. The coincident output atom correction to the normalized kernel of a single pair is exactly
\[
 J_{h,k}(v)=\frac{\sqrt{hk}}x
     \sum_{\substack{q>P\\q\ {\rm split}}}(\log q)^2
                K_B(qh/x)K_B(qk/x).
\tag{10}
\]
It is subtracted, with no change to either continuous coordinate. It is \(O(\log X)\) pointwise by Chebyshev. Thus in an off-line case its integral is negligible relative to the positive individual correlations used in (6), so (6), the support and the sign persist after the output-atom restriction. [Pinned exact atom masks](https://github.com/Sodelin/Research-Commons/commit/47e3ea8ecc114caac8d8afda0447b19920072d5a)

Under the critical-line hypothesis the sign instead reverses. Uniformly for the studied \(h,k,v\), put \(y=x/h\), \(\theta=k/h\in[1,2]\). Fixed-field split-prime counting and partial summation give
\[
 J_{h,k}(v)
  =\frac{\sqrt\theta}{6}\log y
         \int_0^\infty K_B(t)K_B(\theta t)\,dt+o(\log y).
\tag{11}
\]
For the proof, apply the Chebotarev prefix asymptotic to the weight
\((\log t)K_B(t/y)K_B(\theta t/y)\) on \(t>P\). The weight has supremum plus total variation \(O_B(\log y)\) and support \(t\ll_B y\). The prefix error is \(o_P(1)t\) uniformly for \(t\ge P\). In the continuous main term substitute \(t=yr\), use \(P/y\to0\), and note that the integral of \(|\log r|\) against the bounded compact product kernel is uniformly finite. This proves (11). The integral in (11) is uniformly positive, since both kernels are the same positive constant on \(0<t<1/2\). The critical-line Fourier formula makes the unmasked \(g_P\) uniformly bounded on the whole shifted support. Consequently after subtracting (10), each kernel product is negative pointwise, of size \(\asymp\log X\), for all sufficiently late windows. The \(\mathcal A_+\) subset counted in (5) then supplies a **negative** atom-distinct covariance of magnitude
\[
 \asymp \frac{U(V-v_0)(\log\log X)^2}{\log U}.
\tag{12}
\]

The full signed same-cell covariance on (9) still obeys its upper exponent after atom deletion. This needs its own estimate on that slice, since the global mask deletion does not by itself control restrictions to these cells. For each discrete output \(q>P\), let
\[
 A_{q,r,j}(v)=x^{-1/2}(\log q)
       \sum_{\substack{h=rp\in\mathcal A\cap I_j}}
                   2a(p)K_B(qh/x).
\]
Apply the same signed prime prefix in \(p\) as in (8), using bounded variation of the nonnegative monotone \(K_B\), to get
\[
 |A_{q,r,j}(v)|\ll_\epsilon
       x^{-1/2}(\log q)(U/r)^{\beta_*+\epsilon}.
\]
This vanishes for \(q>e^Bx/U\). Therefore the exact full same-cell coincident-atom sum
\(\sum_{q,j}\int(\sum_r A_{q,r,j})^2\,dv\) is \(O_\epsilon(U^{2\beta_*-1}X^\epsilon)\), by Chebyshev for \(\sum_{q\le e^Bx/U}(\log q)^2\) and the subpower number of cells and cofactors. The same-\(r\) restriction gives \(\sum_{q,r,j}\int A_{q,r,j}^2\,dv\) and has the same bound. For shared large prime and short-gap pairs, a fixed pair's correction after companion normalization and coefficients is \(O_B((\log X)/U)\) pointwise by (10). There are \(O(U(Z+H_0))\) such pairs, so that correction is subpower, including the diagonal and the log-window length. This proves the claimed bound on the actual coprime separated comparison.

Only two rough cofactor lanes are needed to obtain the same one-sign exponent. Indeed the admissible pairs in (5) have at most \(Z^2=X^{o(1)}\) distinct pairs of small cofactors. For each \(X\), some distinct \(r,s\) therefore support at least an \(X^{-o(1)}\) fraction of that count. This preserves the exponent in (6), or \(u\) in the critical-line case, with a possible loss in the sharper logarithmic factors. On these two lanes the exact all-pair covariance before subtracting shared large primes and short gaps is \(2\sum_j\int S_{r,j}S_{s,j}\,dv\). The corresponding atom correction is \(2\sum_{q,j}\int A_{q,r,j}A_{q,s,j}\,dv\). Cauchy–Schwarz and the same estimates above bound these quantities and the required subtractions at the same respective signed exponents. The cofactors can depend on the window, as required by the increasing roughness threshold.

Thus for \(1/2<\beta_*<1\), the positive same-conjugacy semiprime pairs still require cancellation by actual mixed large-prime classes on the output-atom-separated support. At the critical line, the same-conjugacy pairs instead give the negative mass (12) and the mixed pairs give the opposite sign. In both cases the signed same-cell sum is strictly smaller on the same retained pair support. These are hand estimates for the fixed factor, with no new Lean verification or numerical checks. The bound for the complete signed covariance remains open.
