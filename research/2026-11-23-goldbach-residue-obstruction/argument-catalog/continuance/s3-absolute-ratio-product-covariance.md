# Absolute bounds for exact ratio and product sectors of the \(S_3\) covariance

Let \(L\) be the same fixed standard \(S_3\) Artin factor, and let \(\beta_*=\sup\Re\rho\) and \(\Delta=\beta_*-1/2\). Keep \(U=\lfloor Y^u\rfloor\), \(P=Y^\alpha\), \(H=Y^{u+\kappa}\), \(u+\alpha+\kappa<1\), \(X=Y^{1+o(1)}\). As before \(b_h=\beta_U(h)/\sqrt h\) and \(f_h(v)=g_P(v-\log h)\) use the original exact cutoff, split-prime centering, and kernel. Companion pairs lie in two arbitrary hard cells \(I,J\) in \((U,H]\), are squarefree, coprime, \((\log X)^2\)-rough, and satisfy the original strict separation \(k-h>H_0=X^{o(1)}\). In either cell one may prescribe prime or composite companions. Also impose any fixed finite collection of exact ratio and product bounds on \(k/h\) and \(hk\), with either endpoint convention. [Surviving signed covariance](https://github.com/Sodelin/Research-Commons/commit/99f45afcdd885d79b3474d4b867f3d0b0e640e21) · [Original atom masks](https://github.com/Sodelin/Research-Commons/commit/47e3ea8ecc114caac8d8afda0447b19920072d5a)

The actual signed covariance on every such sector is
\[
 O_\varepsilon(X^{2\beta_*-1+\varepsilon}).
\tag{1}
\]
All discrete prime atoms dividing a companion, and coincident discrete prime atoms, may be removed on each such sector at a strict power gap from \(2\beta_*-1\) when \(\Delta>0\), and at subpower cost when \(\Delta=0\). The continuous centering references stay on their original support. This is an absolute bound on the signed sector, uniform over all its hard endpoints. In particular it does not require the cross-cell Hilbert angles or a prime factor of either companion to be large. It does not prove a subpower estimate in an off-line case.

There is an actual strict-gap extension when one companion is restricted to lie above \(R=Y^{u+\kappa_1}\) for a fixed \(0<\kappa_1<\kappa\), using the full companion weight on that side, without selecting primes or composites there. The exact ratio/product sector with this additional high-companion requirement is bounded, before atom edits, by
\[
 O_\varepsilon(X^{2\beta_*-1-\kappa_1\lambda+\varepsilon}),
 \qquad \lambda=(\beta_*-1/2)/2>0.
\tag{2}
\]
All atom edits on the same sector save a fixed power as above. This strengthens the earlier high-companion deletion, which used the full unprojected square. [Sharp companion cutoff](https://github.com/Sodelin/Research-Commons/commit/cee389512c24de3ea6d0a90bb3c82f3b0c1e7ecc)

## Uniform multiplicative twists of the two cells

For each fixed sufficiently small positive tolerance \(\varepsilon\), choose \(\sigma>1/2\). In an off-line case it may be chosen \(\sigma<\beta_*\) independently of the tolerance. For any complex \(w=a+i\tau\) with \(|a|\) sufficiently small in terms of the tolerance, have
\[
 \begin{aligned}
 S_{I,d}(w;v)&=\sum_{\substack{h\in I,\ d\mid h\\h\ {\rm admissible}}}
                b_h f_h(v)h^w
     \ll_\varepsilon X^{\Delta+\varepsilon}d^{-\sigma}(3+|\tau|)^\varepsilon,\\
 A_{I,p,d}(w;v)&=x^{-1/2}(\log p)
     \sum_{\substack{h\in I,\ d\mid h\\h\ {\rm admissible}}}
                   \beta_U(h)h^w K_B(ph/x)
     \ll_\varepsilon X^{\Delta+\varepsilon}
                   p^{-\sigma}d^{-\sigma}(3+|\tau|)^\varepsilon ,
 \end{aligned}
\tag{3}
\]
where \(x=e^v\), \(p>P\), and admissibility in this display only comprises conditions on \(h\) alone. The finitely many multiplicative twists we use have polynomially bounded height.

To see the bounds, first remove the rough, squarefree, and prime/composite restrictions. The untruncated \(d\)-lane generating factor is \(G_{U,1}=1-LM_U\) or \(G_{U,d}=-L^{(d)}J_{U,d}\) for \(d>1\), as in the exact divisibility identity. On each closed sub-half-plane strictly to the right of \(\beta_*\), both \(L\) and \(1/L\) are subpower in the height. The bound for both follows by using the same holomorphic logarithm of \(L\) in Borel–Carathéodory and the three-lines estimate. The sharp reciprocal prefix, and the local-factor expansion of \(J_{U,d}\), give \(G_{U,d}(s)\ll d^{-\Re s+\varepsilon}U^\varepsilon(3+|\Im s|)^\varepsilon\), with \(d=1\) interpreted separately. The exact centered transform \(D_{{\rm sp},>P}(s)\) is likewise subpower in \(P,|\Im s|\) there by the Artin prime and verified abelian tails. [Twisted sharp prefixes](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd) · [Exact centered tail](https://github.com/Sodelin/Research-Commons/commit/4bfc76b31db848316d834a98b0b468381feee86a) · [Divisibility factor](https://github.com/Sodelin/Research-Commons/commit/cee389512c24de3ea6d0a90bb3c82f3b0c1e7ecc)

In a Mellin integral for \(S\), the \(h\)-twist gives \(G_{U,d}(s-w)\), while \(D_{{\rm sp},>P}(s)\) stays untwisted. For \(A\), omit that prime transform and use scale \(x/p\). Impose each hard cell endpoint by the truncated auxiliary Perron integral at real part \(-\delta\), with height \(X^C\) and cutoff half-integer \(\lfloor J\rfloor+1/2\) at endpoint \(J\). The \(G\) factor becomes \(G_{U,d}(s+w_h-w)\). Shift \(s\) to a fixed real line just above \(\beta_*\), taking \(\delta\) and \(|a|\) so small that all of \(s-w\) and \(s+w_h-w\) remain strictly to its right as well. All powers from the shift, \(X^C\), \(U\), \(P\), and the factor \(J^{-\delta}\), fit the final arbitrary \(\varepsilon\). Absolute convergence in \(s\) follows from the original quadratic Mellin decay and the height-subpower bounds. Since the arithmetic \(h\)'s are integers at polynomial height, the endpoint errors are negligible for large fixed \(C\), uniformly in the twist. This proves (3) before the additional filters, with \(\sigma>1/2\) selected below the real exponents retained from \(d\) and \(p\).

Roughness and squarefreeness are exact inclusion–exclusion with the weighted \(\operatorname{lcm}\) products. The smooth weights in \(d\) cost only \(d^\varepsilon X^{o(1)}\), since the reciprocal exponent is strictly above \(1/2\), so the same \(\sigma>1/2\) remains possible. For a prime-only companion and \(d=1\), the generating factor is the corresponding sharp prime-trace prefix, with coefficient \(-a(h)\). The usual twisted prime prefix bound is subpower on the shifted lines, even for the unweighted prime trace by partial summation. At \(d>1\) only \(h=d\) can occur, which gives \(O(X^{\Delta+\varepsilon}d^{-\beta_*+\varepsilon})\) for the single centered term. For an atom, the single term is \(O(X^{-1/2+\varepsilon})\) and occurs only when \(p d\le e^Bx\), so it is at most \(O(X^{\Delta+\varepsilon}p^{-\sigma}d^{-\sigma})\). At \(\beta_*=1/2\), take \(\sigma-1/2\) small and absorb the additional \(X^{\sigma-1/2}\) for these single prime terms. Composite companions follow by subtraction. Thus (3) holds with either exact type filter.

## Ratio and product projections

For a threshold \(k/h>r\), choose a nearby real \(r'\) defining exactly the same strict comparison and separated from all attainable ratios. The denominators and numerators are at most \(H\); successive distinct reduced fractions therefore differ by at least \(H^{-2}\). A midpoint in the jump-free interval gives \(|\log(k/(r'h))|\gg H^{-3}\) on the entire support. If a threshold equals an attainable fraction, select the midpoint on the appropriate side for its strict or inclusive convention. An empty or full comparison needs no projection. For \(hk>N\) use a half-integer threshold, so the logarithmic separation is at least a constant times \(H^{-2}\). These adjustments preserve the pair conditions exactly.

Apply truncated Perron to \((k/(r'h))^w\) or \((hk/N')^w\) with \(\Re w>0\) arbitrarily small and height \(T=X^{C'}\). The resulting factors separate into powers of \(h\) and \(k\). For upper endpoints subtract the corresponding lower-event indicator from \(1\). A fixed number of comparisons introduces a fixed number of Perron integrals. Their errors are negligible uniformly because the distances from the exact jumps are inverse polynomial and absolute coefficient and kernel sums are of some fixed polynomial size. Products of approximants remain bounded up to these same errors. In the main integrals, the real thresholds and real twists cost arbitrarily small powers, and
\(\int_{-T}^{T}(3+|\tau|)^\varepsilon/(1+|\tau|)\,d\tau\)
is subpower after rescaling \(\varepsilon\). For several cutoffs the twist height is bounded by a fixed sum of the individual heights. Coprimality is imposed by the exact common-\(d\) Möbius sum. Products of the \(S_{I,d}\) and \(S_{J,d}\) in (3) are summable in \(d\) because \(2\sigma>1\). This proves (1) before atom edits.

The exact atom masks give the same lcm products as the original collision calculation, now with the two Mellin twists in their respective \(A,S\) factors. Each has an absolutely summable prime-coordinate weight. For example a linear divisor collision uses
\[
 \sum_d d^{-\sigma}
        \sum_{p>P}p^{-\sigma}\operatorname{lcm}(d,p)^{-\sigma}
 \ll P^{1-2\sigma},
\]
since \(p\nmid d\) supplies \(p^{-2\sigma}\) directly and \(p\mid d\) supplies \(p^{-3\sigma}\) after summing its multiples. Both-mask intersections have the same saving after treating differing primes by independent weights and coincident primes by their doubled atom weight. Coincident atoms after the divisor mask have factors \(A_{I,p,d}-A_{I,p,\operatorname{lcm}(d,p)}\) and the corresponding factor for \(J\), also with the \(P^{1-2\sigma}\) saving. Since \(P=Y^\alpha\) and \(\sigma\) can be bounded strictly above \(1/2\) in an off-line case, every correction saves a fixed power there. At the critical line the bounds are subpower. [Exact atom intersection identities](https://github.com/Sodelin/Research-Commons/commit/47e3ea8ecc114caac8d8afda0447b19920072d5a)

In addition to the requested ratio/product masks, insert the mandatory strict ratio projector \(k/h>1\). This imposes the original orientation, even if the hard cells overlap. Finally restore the additive separation by removing just \(0<k-h\le H_0\) on these exact oriented supports. The previous absolute short-gap bounds only decrease when the support is clipped. This preserves the off-line exponent gap for the edits, and preserves (1) including at the critical line. In particular a macroscopic ratio range may already satisfy the separation automatically.

## High companions after an actual ratio projection

To prove (2), keep the exact high cutoff on the unrestricted companion type on the first side. Any further hard cell there is a difference of two upper tails with thresholds at least \(R\). In its auxiliary Perron integral take real part \(-\lambda\), \(\lambda=(\beta_*-1/2)/2\). The shifted main \(s\)-line stays at \(\beta_*+\delta\), for small fixed \(\delta>0\), and after subtracting the real ratio twist the \(G\) argument is still at
\(\sigma_1=\Re(s+w_h-w)>1/2\).
It may now lie to the left of \(\beta_*\), giving
\[
 U^{(\beta_*-\sigma_1)_+}R^{-\lambda}\le (U/R)^\lambda
\]
as long as the main line minus the real ratio twist remains at least \(\beta_*\). The $L^{(d)}$ factor on \(\sigma_1\) has a degree-two mean square \(\ll_\eta T^{1+\eta}\) there, up to the harmless local \(d^\eta\) factor.

Use this mean square jointly in the auxiliary imaginary variable \(\omega=\Im w_h\) and the ratio/product variable \(\tau\). For a single projection, the relevant integrand in these two coordinates is bounded, apart from subpower factors, by
\[
 \frac{|L(\sigma_1+i(t+\omega-\tau))|}
      {(1+|\omega|)(1+|\tau|)},\qquad t=\Im s.
\]
On dyadic blocks take \(M\) to be the larger of the two shift scales. Integrate over that larger variable first, using Cauchy–Schwarz and the mean square with the smaller variable fixed. If \(M\) is at least a fixed multiple of \(|t|\), the height interval is within \(O(M)\) and the result after the \(1/M\) denominator is subpower. If \(M\) is smaller, using the whole height block around \(t\) costs \(O((3+|t|)^{1/2+\eta}M^{-1/2})\). The smaller variable only gives a bounded block factor. Thus after summing the blocks the joint average is at most \(X^\eta(3+|t|)^{1/2+\eta}\) for any fixed positive tolerance. This is integrable against the outer \(H_B(s)\) and the subpower centered prime transform. For several projections use the largest among the shift variables influencing this leg, with the others fixed, giving the same bound. The opposite companion still satisfies the untailored pointwise subpower estimate of (3).

The \(d\)-weights chosen below both real kernel lines remain square summable, and the rough and squarefree lcm projections still cost subpower. Thus the factor \((U/R)^\lambda\) survives the exact ratio/product integral. On each excluded positive short gap with one companion at least \(R\), both companions are at least \(R/2\) for large \(X\). The individual envelopes give a total close-pair cost \(O_\varepsilon(H_0 X^{2\Delta+\varepsilon}R^{-2\Delta})\), smaller than the required saving \(\kappa_1\lambda\), since \(R=Y^{u+\kappa_1}\) and \(2\Delta=4\lambda\). This proves (2) after absorbing small real displacements and the close correction. The atom edits have their separate fixed-gap bound. The argument depends on using the entire signed inverse companion on the high side, so does not give a corresponding tail estimate after selecting only primes or only composites there.

## A strict deletion for a small prime–companion product

In the expansion with both discrete and continuous prime coordinates, one can further remove the exact sector in which either output product is at most \(Z=X^\xi\), for any fixed \(0<\xi<1\). This includes a cut \(p h\le Z\) for a discrete prime atom, and the corresponding cut \(t h\le Z\) for its continuous centering coordinate. On every exact companion ratio/product sector above, including the atom exclusions, the cost is
\[
 O_\varepsilon\bigl(X^{\beta_*-1+\varepsilon} Z^{\beta_*}\bigr)
 =O_\varepsilon\bigl(X^{2\beta_*-1-\beta_*(1-\xi)+\varepsilon}\bigr).
\tag{4}
\]
This is a fixed power saving even at the critical line.

For the cut first leg, \(Z<Y\) for large \(X\), so \(K_B(th/x)=1-e^{-B}\) throughout the exact retained low-product region. The normalized first leg is therefore a sharp prefix of the signed product measure at height \(Z\), times \((1-e^{-B})x^{-1/2}\). Its Mellin series, with the same companion twist \(h^w\) and common-divisor lane \(d\), is
\[
 D_{{\rm sp},>P}(s)
   \sum_{\substack{h\in I,\ d\mid h\\h\ {\rm admissible}}}
                 \beta_U(h)h^{w-s}.
\]
The finite second factor obeys the subpower estimate with \(d^{-\sigma}\), \(\sigma>1/2\), on a fixed line just right of \(\beta_*\). This is the same sharp endpoint argument as for (3), but without smoothing in \(s\). For a prime-only companion it uses the same finite trace prefix and single-term estimate when \(d>1\). The first factor is the exact split-prime tail including its continuous reference, also subpower there.

Truncated Perron can be applied to this signed measure with a polynomial height. For the atomic part, move the cutoff to \(\lfloor Z\rfloor+1/2\), which keeps the integers exactly as prescribed and gives inverse-polynomial distance to every jump. The continuous part has density at most \(O_\varepsilon(X^\varepsilon/d)\), since it is the sum over \(d\mid h\) of \(\beta_U(h)h^{w-1}\) times the fixed reference density with lower endpoint \(Ph\). The half-integer adjustment of its mass is therefore harmless. The truncated Perron remainder for this continuous part is bounded by integrating
\(\min\{1,(T|\log(Z'/t)|)^{-1}\}(Z'/t)^{a_0}\)
against the density, for any fixed \(a_0>1\) and \(Z'=\lfloor Z\rfloor+1/2\). Near \(Z'\) the integral costs \(O(Z'\log T/T)\), and away from \(Z'\) the power factor and the minimum give a polynomial bound divided by \(T\), since the support starts at \(t\ge2\). Thus \(T=X^C\) makes the remainder negligible. Shift to a fixed line just above \(\beta_*\) with \(1/s\) in the Perron denominator. The normalized cut first leg is
\[
 O_\varepsilon\!\left(
 X^{-1/2+\varepsilon} Z^{\beta_*}
 d^{-\sigma}(3+|\Im w|)^\varepsilon
 \right).
\]
For an individual low-product atom \(p\), use the exact companion cutoff \(h\le Z/p\) in the same sharp prefix. It has the additional factor \(p^{-\sigma}\) by the same choice of real line. The \(d>1\) single prime term respects this estimate because it occurs only if \(pd\le Z\), and the arbitrary margin loss absorbs the critical-line difference.

Now pair with the unrestricted opposite leg (3) in the ratio/product projection. The same gcd and atom lcm sums converge absolutely. This proves (4) before the short additive gap correction. On close pairs a nonzero low leg forces \(h\le Z/P\). Its actual normalized centered value is \(O_\varepsilon(X^{-1/2+\varepsilon}(Z/h)^{\beta_*})\) by the exact finite prime prefix on \(P<p\le Z/h\). The opposite leg has its usual individual bound. The sum over close pairs is smaller than (4) by the harmonic or power sum in \(h^{-2\beta_*+\varepsilon}\) and the subpower factor \(H_0\). A close pair with one low divisor mask costs at most \(O_\varepsilon(X^{\beta_*-1+\varepsilon}H_0 (Z/P)^{1-\beta_*+\varepsilon})\), which fits (4) since \(1-\beta_*\le\beta_*\). If the divisor mask is on the other leg, use the same individual low centered bound and the same estimate applies. Two masks cost \(O_\varepsilon(X^{-1+\varepsilon}H_0 Z)\), which fits (4) because \(Z^{1-\beta_*}\le X^{\beta_*}\). Coincident low-product atoms on a close pair cost \(O_\varepsilon(Z X^{-1+\varepsilon}/\max(h,k))\) by Chebyshev, still within (4) after summing. Thus (4) applies to the exact separated covariance. Combine the two low-leg deletions by inclusion–exclusion to keep the original signs.

## Why the same absolute projection does not handle a long additive gap

A Mellin ratio or product projection yields multiplicatively separable twists with the integrable-up-to-logs factor \(1/w\). An exact translation gap \(k-h>D\), \(D>0\), gives a different kernel in the same variables. Scaling \(u=h/D\), \(v=k/D\), its double Mellin transform is
\[
 \int_0^\infty\!\int_0^\infty
    \mathbf1_{v>1+u}\,u^{s-1}v^{t-1}\,dv\,du
 =-\frac{\Gamma(s)\Gamma(-s-t)}{t\,\Gamma(-t)}
\]
for \(\Re s=a>0\) and \(\Re t=-b<-a\). Integrate \(v\) first, then use the beta integral. On \(\Im t\asymp M>0\), \(-\Im s/\Im t\) in a fixed compact subinterval of \((0,1)\), the exponential terms from Stirling cancel exactly. The kernel is then of magnitude \(\asymp M^{-3/2}\) on a region of area \(\asymp M^2\), so its absolute dyadic mass is \(\asymp M^{1/2}\). Thus the separate subpower bounds for multiplicative twists in (3) do not supply a subpower-cost Mellin projection for a long hard additive cutoff. Such a proof would need cancellation in this two-frequency kernel or different additive-twist input. The already removed subpower short gaps use a separate absolute argument. These are hand arguments.
