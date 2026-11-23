# Short upper windows without an attained rightmost zero

The original upper kernel detects an off-line zero on every sufficiently late interval of log length \(O_H((\log\log X)^2)\), where \(X\) is the right endpoint in the ordinary variable. This removes the rightmost-zero attainment assumption in the fixed-length argument at the cost of a growing length. It shortens the earlier unconditional proportional-log criterion. The estimate needed from primes still has square-root order. [Original kernel](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md) · [Pinned explicit formula and attained-line criterion](https://github.com/Sodelin/Research-Commons/blob/e00069c40dd17f50a10f57bb76d7300c8f0e3cdf/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/rightmost-zero-short-log-windows.md)

## Exact log-window scale

For the fixed completed dual-closed family \(H\) of the pinned memo, take \(0\le\delta<1/2\), \(B>0\), \(F(x)=x^\delta C_{\delta,B}(x)\), and \(\beta=\sup_\rho\Re\rho\). For any fixed \(\xi<\beta\), if \(\beta>1/2\), there is \(K_H>0\) such that, uniformly over \(0\le U<V\) with \(V-U\ge K_H(1+\log^2(3+V))\),
\[
 \log\!\int_U^V F(e^u)_+ e^{-\xi u}\,du
   =(\beta-\xi)V+o(V)\qquad(V\longrightarrow\infty).
 \tag{1}
\]
In fact the lower bound comes from the final \(K_H(1+\log^2(3+V))\) of this interval. The length constant depends on the local zero count of the fixed family, while the onset also depends on the chosen pole, its coefficient, and the fixed kernel parameters.

At \(\xi=1/2\), GRH follows if for every \(\epsilon>0\) the integral is at most \(e^{\epsilon V}\) on arbitrarily late windows of this length. Even if the endpoints are selected as a function of \(\epsilon\), (1) holds on all such windows once sufficiently late. Under GRH the integral is \(O_{H,\delta,B}(V-U)\) by the pinned pointwise converse. For a fixed exponent \(\epsilon\ge0\), an upper bound \(e^{(\epsilon+o(1))V}\) on such a sequence excludes zeros with real part greater than \(1/2+\epsilon\).

## Positive filters for finite ranges of ordinates

Use the pinned explicit formula with distinct completed zeros, incorporating multiplicity into \(b_\rho\):
\[
 F(e^u)=\sum_\rho b_\rho e^{\rho u}+O_{H,\delta,B}((1+u)e^{\delta u}),
 \qquad \sum_\rho |b_\rho|<\infty.
\]
It includes a possible real zero at \(\delta\) in the elementary remainder. Every zero with real part \(b>\max(1/2,\xi)\) has \(b_\rho\ne0\). In the real case the coefficient is positive. More generally every real zero in \((\delta,1)\) has positive coefficient, directly from
\[
 b_\rho=-\frac{m_H(\rho)(1-e^{(\rho-\delta-1)B})}
 {2d(\rho-\delta)(\rho-\delta-1)}.
\]
The real parts lie in the closed critical strip and the boundary at one is nonvanishing in the pinned family. Write \(N_H(I)\) for the zero count with ordinate in \(I\). The local bound \(N_H([j,j+1])\ll_H\log(3+|j|)\) suffices. [Local counts and logarithmic derivative, Iwaniec–Kowalski, Proposition 5.7](https://doi.org/10.1090/coll/053)

Fix such a zero \(\rho_0=b+i\gamma_0\), choosing the largest real part at this ordinate. This maximum exists by the local count. Set \(f(u)=e^{-bu}F(e^u)\) and let \(a\) be a late real log endpoint at which a filter begins. A probability measure \(\nu\) on the real line has transform \(M_\nu(z)=\int e^{zt}\,d\nu(t)\). If \(\Im z\ne0\), put \(\ell_z=\pi/|\Im z|\). The probability measure
\[
 \nu_z=\frac{\Delta_0+e^{-(\Re z)\ell_z}\Delta_{\ell_z}}
                 {1+e^{-(\Re z)\ell_z}}
\]
has \(M_{\nu_z}(z)=0\), where \(\Delta_t\) denotes unit point mass at \(t\). Thus convolution kills prescribed nonreal exponents, preserving positivity of the measure.

For \(T=a\), convolve the factors \(\nu_z\) at \(z=\rho-b\) and \(z=\rho-b-i\gamma_0\) for all \(|\Im\rho|\le T\), omitting real exponents in each list. The support is \([0,S]\) with \(S\le C_H\log^2(3+T)+O_{H,\rho_0}(1)\). Indeed outside the bounded range \(|\Im\rho|\le 2|\gamma_0|+2\), both denominators \(|\Im\rho|\), \(|\Im\rho-\gamma_0|\) are comparable to \(|\Im\rho|\). The contribution of a unit ordinate band is then \(O_H(\log(3+j)/j)\). Inside the bounded range the nonzero denominators give a finite fixed sum. In particular the leading length constant is independent of which zero was fixed.

To control \(|\Im\rho|>T\), also convolve \(m=\lceil 6a\rceil\) uniform probabilities on \([0,10/T]\). For \(T\ge\max(20,2|\gamma_0|)\) and either exponent \(z\) from this range, \(|\Im z|\ge T/2\) and \(\Re z\le1\). Each uniform factor has transform of magnitude bounded by
\[
 \left|\frac{e^{10z/T}-1}{10z/T}\right|
 \le \frac{1+e^{1/2}}5 < \frac35.
\]
These factors cost bounded total length. Finally convolve the unit uniform on \([0,1]\). The resulting probability \(\mu_a\) has a density bounded by \(1\), support length \(O_H(\log^2(3+a))+O_{H,\rho_0}(1)\), and \(M_{\mu_a}(0)=1\). The low-zero annihilations persist. In either moment the total high-zero term is
\[
 O\!\left(e^{a+S+1}(3/5)^m \sum_\rho |b_\rho|\right)=o(1).
\]
Here \(e^a\) bounds the factors at the left endpoint, and \(e^{S+1}\) bounds the transforms of the other probability measures by their support. The elementary remainder is also \(o(1)\) uniformly on the support, since \(b>\delta\) and the support length is \(o(a)\).

## Lower bound for the original positive part

The unmodulated moment \(M_0=\int f(a+t)\,d\mu_a(t)\) contains only the real low zeros up to \(o(1)\). Those with real part above \(\delta\) give nonnegative contributions because the transform of a positive measure at a real number is positive. The finitely many real zeros at or below \(\delta\), if present in the series, contribute \(o(1)\) since \(b>\delta\). Hence \(M_0\ge-o(1)\).

The modulated moment \(M_1=\int f(a+t)e^{-i\gamma_0(a+t)}\,d\mu_a(t)\) keeps just the low zeros at \(\gamma_0\) up to \(o(1)\). The term of \(\rho_0\) equals \(b_{\rho_0}\). The remaining zeros at that ordinate have smaller real part and decay since \(|M_{\mu_a}(\sigma)|\le1\) for \(\sigma<0\). Thus \(M_1=b_{\rho_0}+o(1)\). This includes \(\gamma_0=0\), when both moments coincide and \(b_{\rho_0}>0\). Since \(f\) is real,
\[
 \int f(a+t)_+\,d\mu_a(t)
 =\tfrac12\left(\int |f(a+t)|\,d\mu_a(t)+M_0\right)
 \ge \tfrac12(|M_1|+M_0)\ge |b_{\rho_0}|/4
\]
for sufficiently large \(a\). The density bound transfers this lower bound to Lebesgue measure on the same interval.

For (1), start at \(a=V-K_H(1+\log^2(3+V))\), choosing \(K_H\) large enough to contain the entire filter for any **fixed** target as \(V\to\infty\). The integral there is at least \((|b_{\rho_0}|/4)e^{(b-\xi)a}\). The absolutely convergent explicit formula gives the upper bound \(O_{H,\delta,B,\xi}(e^{(\beta-\xi)V})\). Taking the limit first for each fixed target and then taking \(b\) to \(\beta\) proves (1). It makes no uniform separation assumption on distinct ordinates or on distinct real parts.

At square-root weight, the last \(O_H(\log^2 V)\) of each such window therefore contains a set of ordinary measure \(X^{1-o(1)}\) on which \(F(t)\ge X^{\beta-o(1)}\). To see this, use that last interval alone in (1), discard the portion on which the normalized positive part is below half its integral divided by interval length, and use the uniform \(O(e^{(\beta-1/2)V})\) envelope to bound the measure of what carries the remaining half. Multiplication by \(e^u\ge e^{V-O_H(\log^2 V)}\) converts log measure to ordinary measure. The power-saving exceptional-set and power-spaced sampling criteria thus work on these shortened windows as well. For sampling, the quadrature error estimate in the earlier note is exponentially smaller than (1) on this last interval. [Explicit exceptional-set and quadrature bounds](https://github.com/Sodelin/Research-Commons/blob/a511a288e37ae183f9769249395e088797d021c3/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/damped-window-exceptional-sets-and-sampling.md)

## Fixed length if zeros to the right of the chosen pole are sparse

Suppose a specific \(\rho_0=b+i\gamma_0\) as above satisfies
\[
 \sum_{\Re\rho>b}\frac{1}{1+|\Im\rho|}<\infty.
 \tag{2}
\]
A fixed filter now suffices. Use the same factors for all zeros to the right of \(b\) and for finitely many remaining zeros up to a cutoff \(T_0\). Omit real exponents as before. Total support length is finite by (2) and the local count near \(0,\gamma_0\). The infinite convolution exists as the law of the sum of independent variables in the bounded supports, whose lengths are summable. Its transform keeps each prescribed zero because the sum of the other variables is independent of the corresponding factor. Add the unit uniform to obtain the same density bound. For \(\Re\rho\le b\), the remaining unfiltered residue tail has both moments bounded by \(\sum_{|\Im\rho|>T_0}|b_\rho|\), uniformly in \(a\). Choose \(T_0\) to make this smaller than \(|b_{\rho_0}|/16\). The same argument now gives a positive-part lower bound \(\gg_{\rho_0}e^{(b-\xi)a}\) in every sufficiently late interval of a fixed log length. Any bound \(N_H(\Re\rho>b,|\Im\rho|\le T)\ll T^{1-c}\) with \(c>0\) implies (2) by dyadic summation. The target zero need not be on an attained rightmost line.

For example, take \(H=L(s,\rho)\) for the standard representation of an \(S_3\)-closure of a cubic field \(K\). The entire factor satisfies \(\zeta_K(s)=\zeta(s)L(s,\rho)\), so its strip zeros with multiplicity are bounded by those of \(\zeta_K\). Heath-Brown's Theorem 1, applied at degree three, gives \(N_{\zeta_K}(\sigma,T)\ll_{K,\epsilon}T^{(3+\epsilon)(1-\sigma)}(\log T)^{C(K,\epsilon)}\). It follows that (2) holds for each fixed \(b>2/3\). In particular if \(\beta>2/3\), a fixed log length depending on the detected zero suffices, with no attainment assumption. This application is for a fixed field. The quoted logarithmic exponent, constants and onset provide no uniform field-discriminant bound. [Heath-Brown, Acta Arithmetica 33, Theorem 1](https://doi.org/10.4064/aa-33-2-169-181)


A separate degree-two proof now establishes (2) for every fixed \(b>1/2\) for this \(S_3\) factor, using a smooth approximate functional equation and a short inverse Dirichlet polynomial. Thus any off-line case for this factor has a fixed-length detector. Arbitrarily slowly diverging tested log lengths suffice with no prescribed spectral constant. [Pinned \(S_3\) density and shorter criterion](https://github.com/Sodelin/Research-Commons/blob/304b341ad0a4a99eb16055613bfafceb7c476850/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/s3-degree-two-density-for-fixed-windows.md)

## Arithmetic input and verification status

The exact positive kernel identity from the earlier memo shows that an arbitrarily late square-root negative-part mean bound for the damped prime prefix on these shorter windows, extended by \(B\) at the right, suffices. The shortened window at \(X\) spans only down to \(X\exp(-O_H((\log\log X)^2))\). It avoids an estimate across distinct fixed powers of \(X\) or across all sufficiently large arguments. The known absolute coefficient and short-increment estimates checked in the earlier audit still fail to supply the needed signed prefix bound on this shorter support. A bound for a genuinely centered macroscopic variance of the standard coefficients at square-root order would suffice. [Pinned transfer and arithmetic countermodels](https://github.com/Sodelin/Research-Commons/blob/fc73be153974ee9ada2e73013a7997465ba211de/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/dilation-window-boundary-and-prime-mean-obstruction.md)

The positive filters, scale improvement, and fixed-length criterion under (2) are hand proofs. The generic proportional window theorem remains the Lean-verified result used in the earlier reduction. These new bounds use the pinned explicit formula and have no new Lean verification or zero computation. The square-root prime estimate for the S3 factor and the general family remains open.
