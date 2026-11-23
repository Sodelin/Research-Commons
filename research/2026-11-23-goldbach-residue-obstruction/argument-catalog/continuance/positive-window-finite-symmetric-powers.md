# A positive window for a finite family of symmetric powers of Delta

For each integer \(M\ge1\), one positive prime-power count gives a conditional critical-line criterion for \(\zeta\) and all unitary symmetric-power \(L\)-functions of Ramanujan's \(\Delta\) through the \(M\)-th. The product has finite conductor \(1\), degree \((M+1)^2\), and a pole of order two at \(1\).

## The product and its analytic data

Write \(L_0=\zeta\) and \(L_j=L(s,\operatorname{Sym}^j\pi_\Delta)\) for \(j\ge1\). Newton–Thorne's Theorem A supplies the level-one cuspidal lifts, with local parameter compatibility as in their definition of the lift. We use their unitary twists. The standard theory gives entire completed cuspidal \(L_j\) of order one and their functional equations. Jacquet–Shalika gives nonvanishing on \(\Re s=1\) for \(j\ge1\). The corresponding facts for \(\zeta\) are classical, with simple poles at \(0,1\) for its completion. Deligne gives \(\alpha_p\beta_p=1\) and \(|\alpha_p|=|\beta_p|=1\) at every finite prime. Each lift is self-dual from the local symmetric-power parameters and strong multiplicity one. [Newton–Thorne, Theorem A and definition of the lift](https://doi.org/10.1007/s10240-021-00127-3) · [Godement–Jacquet](https://doi.org/10.1007/BFb0070263) · [Jacquet–Shalika](https://doi.org/10.1007/BF01390166) · [Deligne, Théorème 8.2](https://doi.org/10.1007/BF02684373)

Define the finite product
\[
 P_M=L_M\prod_{j=0}^{M-1}L_j^2,\qquad D_M=(M+1)^2 .
\]
For \(|z|=1\), put \(\chi_j(z)=\sum_{a=0}^j z^{j-2a}\). The Laurent coefficient at \(z^a\) in \(\chi_M+2\sum_{j<M}\chi_j\) is \(M+1-|a|\) for \(|a|\le M\), and zero elsewhere. These are exactly the coefficients in \(\bigl|\sum_{a=0}^M z^a\bigr|^2\). At \(p^k\), with \(z=\alpha_p^k\), this gives
\[
 \Lambda_{P_M}(p^k)=\left|\sum_{a=0}^{M}\alpha_p^{ka}\right|^2\log p,\qquad
 0\le\Lambda_{P_M}(p^k)\le D_M\log p .
\]
For even \(M=2r\), there is also a Rankin–Selberg realization \(P_M=L(s,V_r\times V_r^\vee)\), with \(V_r=\operatorname{Sym}^r\pi_\Delta\boxplus\operatorname{Sym}^{r-1}\pi_\Delta\). Clebsch–Gordan gives each even power below \(2r\) twice from the self-tensor terms, the top power once, and each odd power twice from the cross terms. The Laurent identity gives positivity for odd \(M\) as well.

The coefficients vanish off prime powers. Absolute convergence gives nonvanishing for \(\Re s>1\). The only pole of \(P_M\) in the right half-plane is the double pole at \(1\).

For the conductor, use the convention \(\Gamma_{\mathbb C}(s)=\Gamma_{\mathbb R}(s)\Gamma_{\mathbb R}(s+1)\). At infinity the parameter of \(\pi_\Delta\) is induced from the angular character of weight \(11\). Pairing opposite weights in the \(j\)-th symmetric power gives \(\Gamma_{\mathbb C}(s+11a)\) for \(a\) running through the positive values of \(j/2,j/2-1,\ldots\). When \(j=2m\), the middle weight contributes \(\Gamma_{\mathbb R}(s+(m\bmod 2))\), since the nontrivial coset representative of \(W_{\mathbb R}/\mathbb C^\times\) acts on the middle monomial by \((-1)^m\). Thus the \(D_M\) real gamma shifts \(\mu\) of the completed \(P_M\) lie in \([0,11M/2+1]\). The analytic conductor convention \(Q_M(t)=\prod_\mu(3+|\mu+it|)\) gives \(Q_M(t)\le(11M/2+4+|t|)^{D_M}\). These gamma factors are holomorphic and nonzero in the open strip.

## Exact window and prime-power deficit

Fix \(B,\kappa>0\) and put \(w_B(v)=2(B-v)/B^2\) on \([0,B]\). For \(F=P_M,\zeta\), write \(a_F\) for its pole order at 1, \(c_F=\operatorname{FP}_{s=1}(F'/F)(s)\), and set
\[
 S_F(x)=\sum_{n}\Lambda_F(n)(x/n-1)_+,\qquad
 G_F(x)=S_F(x)-a_F x\log x+(a_F+c_F)x,\qquad
 T_vH(x)=e^{-v}H(e^v x).
\]
Use the nonnegative count
\[
 A_{M,v}(x)=T_v S_\zeta(x)+\frac{S_{P_M}(x)-T_v S_{P_M}(x)}{D_M}.
\]
Indeed the \(p^k\) contribution partitions its \(\log p\) weight between the kernels \((x/p^k-1)_+\) and \(e^{-v}(e^v x/p^k-1)_+\), in proportions \(\Lambda_{P_M}(p^k)/(D_M\log p)\) and its complement. Let
\[
 C_{M,B}(x)=\int_0^B w_B(v) A_{M,v}(x)\,dv
 -x\Bigl(\log x-1-c_\zeta+(1-2/D_M)B/3\Bigr).
\]
For each fixed \(M\), all the strip zeros of \(L_0,\ldots,L_M\) are on \(\Re s=1/2\) if and only if, for every \(0<\epsilon<1/2\) and \(\eta>0\), there are arbitrarily large \(Y\) with
\[
 \int_Y^{Y^{1+\kappa}} C_{M,B}(x)_+ x^{-1/2-\epsilon}\frac{dx}{x}\le Y^\eta.
 \tag{W_M}
\]
The proof below separates the unconditional implication from its converse.

The quantity needed in \((W_M)\) can also be isolated without \(c_{P_M}\). Put \(\psi_{P_M}(x)=\sum_{n\le x}\Lambda_{P_M}(n)\). The derivative of \(S_{P_M}(x)/x\) with respect to \(\log x\) equals \(\psi_{P_M}(x)/x\) off prime powers. The function itself is continuous. Integrating the derivative and then integrating \(v\) against \(w_B\) gives the exact identity
\[
 C_{M,B}(x)
 =\int_0^B w_B(v) T_v G_\zeta(x)\,dv
  +\frac{x}{D_M}\int_0^B (1-v/B)^2
     \left(2-\frac{\psi_{P_M}(e^v x)}{e^v x}\right)\,dv .
\]
With verified zeta RH, the first summand is \(O_{\epsilon,B}(x^{1/2+\epsilon/2})\). Its contribution to the normalized integral in \((W_M)\) is bounded uniformly in \(Y\) by integrating \(x^{-\epsilon/2}dx/x\). The inequality \((f+g)_+\le f_++|g|\), used in both directions with budget \(Y^{\eta/2}\), permits replacing \(C_{M,B}\) in \((W_M)\) by the second summand. This is a one-sided lower-count target at a fixed multiplicative scale. [Verified zeta RH](https://math.mit.edu/~drew/grh/#what-was-verified)

## Hand proof of the zero implication and its converse

The centered function is the average of \(T_vG_\zeta+(G_{P_M}-T_vG_{P_M})/D_M\). The Laplace transform of \(G_F(e^u)\) for \(\Re s>2\) is
\[
 \frac{-F'(s)/F(s)}{s(s-1)}
  -\frac{a_F}{(s-1)^2}+\frac{a_F+c_F}{s-1}.
\]
The singular terms at \(1\) cancel. A shift \(T_v\) multiplies the transform by \(e^{(s-1)v}\) up to an entire correction from \([0,v]\). At any strip zero \(z\) the resulting residue is
\[
 -\frac{Z_B(z)m_\zeta(z)+(1-Z_B(z))m_{P_M}(z)/D_M}{z(z-1)},\qquad
 Z_B(s)=\int_0^B w_B(v)e^{(s-1)v}\,dv .
\]
The triangular kernel has \(0<\Re Z_B(z)<1\). The multiplicities are nonnegative, and \(m_{P_M}(z)\) is positive at every zero under consideration. The residue survives and is positive at every real strip zero. The log coefficient bounds give continuous counts and \(C_{M,B}(e^u)=O_M(e^{2u})\) for \(u\ge0\). The transform is holomorphic off the discrete strip poles throughout \(\Re s>0\). This checks the generic pole and growth data. Taking \(g(u)=C_{M,B}(e^u)\) and the upper envelope \(g(u)_+\), the pinned Landau theorem sends \((W_M)\) to a zero exclusion for \(\Re z>1/2+\epsilon\). Letting \(\epsilon\downarrow0\) and applying each factor's functional equation proves sufficiency. [Triangular kernel proof](https://github.com/Sodelin/Research-Commons/blob/f84b1a09cc21d468327e65645edbbf64879354a2/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/triangular-average-number-field-windows.md) · [Pinned Lean theorem](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84)

For the converse only, assume the critical-line statements. Smoothed Perron with denominator \(s(s-1)\) shifts to \(\sigma=1/2+\epsilon\). Here is the degree dependence. Let \(H_M(s)=[s(s-1)]^2\Gamma_M(s)P_M(s)\), where \(\Gamma_M\) is its archimedean product. The polynomial removes the two zeta poles at each of 0 and 1. The completed entire function has order at most one and its functional equation is reflection about \(1/2\) up to sign. Pair the zeros \(1/2\pm i\tau\) in its Hadamard product, factoring out a possible central zero. The paired factors are even in \(s-1/2\), so the functional equation removes the linear exponential. Thus the real part of \(H_M'/H_M(2+it)\) equals
\[
 \sum_{z=1/2+i\tau}\frac{3/2}{(3/2)^2+(t-\tau)^2},
\]
where multiplicities are included. By the coefficient cap at \(\Re s=2\) and the gamma shifts this sum is \(O(D_M\log(M+|t|+3))\) with an absolute constant. Subtracting the logarithmic derivatives at \(2+it\) and \(\sigma+it\), the difference of each pair of individual zero fractions is bounded by \(O_\epsilon((1+(t-\tau)^2)^{-1})\). The gamma and pole factors then give \(P_M'/P_M(\sigma+it)=O_\epsilon(D_M\log(M+|t|+3))\). The same bounds hold along the horizontal parts of the contour at large height. The residue at \(1\) gives the center defining \(G_{P_M}\). Hence
\[
 D_M^{-1}|G_{P_M}(x)|\ll_\epsilon x^{1/2+\epsilon}\log(M+3)
\]
uniformly for \(M\ge1\) and \(x\ge2\). For \(\zeta\) the same argument uses one gamma factor and a simple pole at \(1\). Compact averaging therefore yields \(|C_{M,B}(x)|\ll_{\epsilon,B}x^{1/2+\epsilon}\log(M+3)\) under the stated hypotheses, proving \((W_M)\) for each fixed \(M\). This bound is a conditional converse with explicit degree dependence. Sufficiency makes no uniform assertion about the first permissible \(Y\) as \(M\) varies. [Hadamard logarithmic derivative for completed \(L\)-functions, Iwaniec–Kowalski, §5.3](https://doi.org/10.1090/coll/053)

The same residues also give the quantitative late-window result of the pinned number-field argument. For fixed \(M,B\), let \(\beta_*\) be the supremum of the strip-zero real parts. For \(0<\theta<\beta_*\) and \(\kappa>0\),
\[
 \lim_{Y\to\infty}\frac{1}{\log Y}
  \log\left(\int_Y^{Y^{1+\kappa}} C_{M,B}(x)_+x^{-\theta}\frac{dx}{x}\right)
 =(1+\kappa)(\beta_*-\theta).
\] The right-end-subwindow proof uses only the checked generic pole data. For the upper bound, when \(\beta_*<1\), shift Perron to any \(\beta_*<\sigma<1\) using the local zero expansion and the positive distance to the zeros. When \(\beta_*=1\), use the elementary coefficient bound. This rate statement assumes no critical-line result for the symmetric powers. [Pinned rate argument](https://github.com/Sodelin/Research-Commons/blob/25fb33dfbbc5cabe79f039f741636e69ead590f5/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/window-rightmost-zero-rate.md) · [Local logarithmic-derivative estimate, Iwaniec–Kowalski, Proposition 5.7](https://doi.org/10.1090/coll/053)

## Verification and remaining estimate

The product identities, translations, residues and conductor bounds are hand arguments. The generic Landau implication is Lean-verified at the pinned commit. The separate pinned Lean declaration named \(\mathtt{NewtonThorneSym}\) defines a proposition. This memo uses the external Newton–Thorne theorem for the lifts. Neither the arithmetic instantiation nor \((W_M)\) is verified here in Lean. No numerical tests are used. The lower-count estimate in \((W_M)\) remains open in this argument and supplies no additive correlation on a prescribed Goldbach target. [Pinned proposition](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LiteratureResults/NewtonThorneSym.lean#L13-L22)
