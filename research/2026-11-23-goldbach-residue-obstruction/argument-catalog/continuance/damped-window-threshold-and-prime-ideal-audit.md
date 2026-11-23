# Audit of the damped window, its threshold, and prime ideal support

This note checks the damping and exact reference in the positive standard-family count. It gives the pole and the sharp off-line growth rate in the square-root normalization. For degrees at most three, the window can also be stated using prime ideals alone. All the deductions are by hand from the pinned generic Lean theorem and the cited classical inputs. The arithmetic upper window remains open. [Pinned standard-family window](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md)

## Shifted derivative and unchanged kernel

Use the notation of the pinned theorem for a nonempty dual-closed family \(H=\prod_i L_i\) of total degree \(d\). Put \(H_\delta(s)=H(s+\delta)\), where \(0\le\delta<1/2\), \(S(x)=\sum_n\Lambda_H(n)n^{-\delta}(x/n-1)_+\), and \(T_B S(x)=e^{-B}S(e^Bx)\) for \(B>0\). The raw nonnegative count \(A_B\) is built by using \(\zeta_F^dH_\delta\) to split the reference weights between two scales. Linearity gives exactly
\[
 A_B(x)-\tfrac12\bigl(S_{\zeta_F}(x)+T_B S_{\zeta_F}(x)\bigr)
   = C_{\delta,B}(x)=\frac{S(x)-T_B S(x)}{2d}.
\]
This cancels the reference coefficient by coefficient. Positivity of \(A_B\) and the cap only give a general bound \(C_{\delta,B}(x)=O_{F,B}(x)\) by the finite prime-power bound and the bounded difference of the two kernels. The window requires smaller growth.

For \(\Re s>2\) an individual term integrated in \(u=\log x\ge0\) contributes \(n^{-s}/[s(s-1)]\). Thus damping multiplies the Dirichlet coefficient by \(n^{-\delta}\), giving
\[
 \Psi_\delta(s)=\frac{-H'(s+\delta)/H(s+\delta)}{s(s-1)},\qquad
 \widehat C_{\delta,B}(s)=\frac{(1-e^{(s-1)B})\Psi_\delta(s)+
 e^{(s-1)B}\int_0^B S(e^v)e^{-sv}\,dv}{2d}.
\]
The denominator comes from the smoothing in \(x\) and stays \(s(s-1)\). The compact integral is entire. Its sign is positive because the translated transform is taken away from the unshifted transform. \(H(s+\delta)\) is regular and nonzero at \(s=1\), so \(1-e^{(s-1)B}\) removes that simple kernel pole. With the archimedean bounds in the pinned theorem there are no forced gamma-cancellation zeros in \(\Re s>0\) for \(H_\delta\). A completed zero \(\rho\) of the original family therefore gives a pole at \(z=\rho-\delta\) whenever \(\Re z>0\), with residue
\[
  -\frac{(1-e^{(z-1)B})m_H(\rho)}{2d\,z(z-1)}.
\]
Here \(m_H\) includes every multiplicity at a shared zero. The real part of the multiplier \(1-e^{(z-1)B}\) is positive since \(\Re z<1\). This makes the residue nonzero, and the residue at any real \(z\) is positive as required by the pinned theorem. [Pinned pole data](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean#L15-L29) · [Pinned Landau implication](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84)

The threshold for the theorem on \(C_{\delta,B}\) is exactly \(\theta=1/2-\delta>0\). In particular \(\Re z\le\theta\) gives \(\Re\rho\le1/2\). With \(F_{\delta,B}(x)=x^\delta C_{\delta,B}(x)\), the window integrands satisfy the exact identity
\[
 (C_{\delta,B}(x))_+x^{-\theta}=(F_{\delta,B}(x))_+x^{-1/2}.
\]
This identity is used only for the integrals. Directly shifting the transform of \(F_{\delta,B}\) can move a boundary singularity at \(s=0\) into the open right half-plane. The generic theorem is applied to the damped observable \(C_{\delta,B}\).

A smooth reference would fail at the lowered threshold when \(\delta>0\). Indeed replacing the exact reference by the same smooth main terms leaves \((G_F+T_B G_F)/2+C_{\delta,B}\), with \(G_F\) the centered Dedekind sum. At a strip zero write \(W=e^{(z-1)B}\). Its residue numerator, after the common factor \(-1/[z(z-1)]\), is \((1+W)m_{\zeta_F}(z)/2+(1-W)m_H(z+\delta)/(2d)\). Both multipliers have positive real part. Every Dedekind zero survives, including some with real part at least \(1/2\) by the functional equation and existence of nontrivial zeros. Such poles exceed \(1/2-\delta\). Thus the exact subtraction is required for this formulation, even with RH for the Dedekind reference.

## Quantitative off-line obstruction

Write \(\beta_*=\sup_\rho\Re\rho\) for the completed family. For fixed \(B,\kappa>0\), if \(\beta_*>1/2\), then
\[
 \lim_{Y\to\infty}\frac{1}{\log Y}\log
 \int_Y^{Y^{1+\kappa}}(F_{\delta,B}(x))_+x^{-1/2}\frac{dx}{x}
 =(1+\kappa)(\beta_*-1/2).
\]
To get the lower limit use the damped statistic, whose rightmost pole supremum is \(\beta_*-\delta>\theta\). For \(U=\log Y\), choose \(\theta<\theta'<\beta_*-\delta\) and \(0<\kappa'<\kappa\). Apply the contrapositive of the pinned Landau theorem on the rightmost subwindow \([V,(1+\kappa')V]\), with \(V=(1+\kappa)U/(1+\kappa')\). Some positive exponential budget is exceeded on every sufficiently late such subwindow. Comparing the two weights \(e^{-\theta u}\) and \(e^{-\theta'u}\) gives a lower logarithmic rate of at least \((1+\kappa)(\theta'-\theta)/(1+\kappa')\). Let \(\kappa'\downarrow0\) and \(\theta'\uparrow\beta_*-\delta\) after taking the lower limit. [Pinned right-end subwindow argument](https://github.com/Sodelin/Research-Commons/blob/25fb33dfbbc5cabe79f039f741636e69ead590f5/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/window-rightmost-zero-rate.md)

For the upper limit when \(\beta_*-\delta<1\), move smoothed Perron for \(S\) to any fixed \(\beta_*-\delta<\sigma<1\). In the closed vertical region between the new line and the initial line, the shifted zeros are separated by a fixed real gap. The local logarithmic-derivative expansion and zero count give a logarithmic bound at large height. When \(\beta_*=1\) and \(\delta>0\), the new unshifted line has \(\Re(s+\delta)>1\), where absolute Euler convergence also gives the bound. The residue at \(1\) supplies a linear term which the difference \(S-T_BS\) removes, so \(C_{\delta,B}=O(x^\sigma)\). Let \(\sigma\downarrow\beta_*-\delta\). If \(\beta_*-\delta=1\), then \(\delta=0\), and the elementary coefficient cap gives the same upper limit. In particular a bound by \(Y^c\) at arbitrarily late normalized windows for a fixed \(c\ge0\) implies \(\beta_*\le1/2+c/(1+\kappa)\). This rate is independent of \(\delta\) in the square-root normalization. [Local zero-count and log-derivative estimate, Iwaniec–Kowalski, Proposition 5.7](https://doi.org/10.1090/coll/053)

## Prime ideals alone in degrees at most three

The difference kernel is bounded and compactly supported at each fixed \(x\):
\[
 C_{\delta,B}(x)= -\frac1{2d}\sum_n\Lambda_H(n)n^{-\delta}
             \left(\frac{x}{\max(x,n)}-e^{-B}\right)_+ .
\]
Equivalently, if \(A_\delta(t)=\sum_{n\le t}\Lambda_H(n)n^{-\delta}\), then
\(C_{\delta,B}(x)=-(x/(2d))\int_x^{e^B x} A_\delta(t)t^{-2}dt\).
This follows by differentiating \(S(x)/x\) off the prime powers and using its continuity.

Suppose the finite roots of the original family have modulus at most \(q^\tau\), with \(\tau\le\delta\). The absolute contribution of all \(\mathfrak p^k\) with \(k\ge K_0\ge2\) is \(O(x^\theta)\) whenever \(\tau+1/K_0\le1/2\). Indeed \(\sum_{q^k\le X,k\ge K_0}\log q\ll_{F,K_0}X^{1/K_0}\) by the prime-ideal Chebyshev bound. Partial summation with \((q^k)^{\tau-\delta}\) gives at most \(X^{1/K_0+\tau-\delta}\) if this power is positive, \(O(1+\log X)\) at equality, and \(O(1)\) if it is negative. Take \(X=e^Bx\). This proves the claim and removes all higher powers in an everywhere tempered family.

For fixed cuspidal families of degrees two and three, the remaining finitely many powers can also be removed. Write \(\lambda_{\mathfrak p}=\sum_j\alpha_{\mathfrak p,j}\) at an unramified prime and let \(e_j\) be the elementary symmetric functions of the Euler roots. In degree two, \(e_2\) is the unitary central character value. In degree three, \(e_3\) is that value and \(e_2=e_3\overline{\lambda_{\mathfrak p}}\), since the contragredient has inverse roots and its first trace is the conjugate trace. Newton's identities give, for each fixed \(k\),
\[
  \left|\sum_j\alpha_{\mathfrak p,j}^k\right|
  \ll_k 1+|\lambda_{\mathfrak p}|^k .
\]
Indeed each \(e_j\) is bounded by \(1+|\lambda_{\mathfrak p}|\), and the monomials in the \(k\)-th power trace have weighted degree \(k\) when \(e_j\) is assigned weight \(j\).

The self Rankin–Selberg function has a simple pole at \(1\) and nonnegative log coefficients. Its first coefficient at an unramified prime is \(|\lambda_{\mathfrak p}|^2\log q\). Positivity and evaluation of its negative log derivative at \(1+1/\log X\) give
\(\sum_{q\le X}|\lambda_{\mathfrak p}|^2\log q\ll_\pi X\log X\) over unramified primes. With the local bound \(|\lambda_{\mathfrak p}|\ll q^\tau\), for each fixed \(k\ge2\) this gives
\[
 \sum_{q^k\le X}\left|\sum_j\alpha_{\mathfrak p,j}^k\right|\log q
 \ll_{\pi,k} X^{\tau+(1-2\tau)/k}(1+\log X)
 \ll_{\pi,k} \sqrt X(1+\log X)
\]
on unramified primes. Sum this for \(2\le k<K_0\) and use partial summation with \((q^k)^{-\delta}\). Its damped contribution is \(O(x^\theta(1+\log x))\). The finitely many ramified prime ideals contribute at most \(O(1+\log x)\) over all powers by the damped cap. Degree one already has unit-modulus local roots wherever its Euler factor is nontrivial.

Thus restricting both the raw count and its exact reference to prime ideals changes the normalized statistic by \(O(\sqrt x(1+\log x))\) for any fixed family of degrees at most three. The positive-part window integral changes by at most \(O((1+\log Y)^2)\), by \(|a_+-b_+|\le|a-b|\). This preserves both the arbitrarily late \(Y^\eta\) criterion and the strictly positive logarithmic rate above. The Rankin bound is an unconditional coefficient estimate and uses no Rankin critical-line hypothesis. [Blomer–Brumley all-place local bounds](https://annals.math.princeton.edu/2011/174-1/p18) · [Rankin–Selberg log coefficients and pole, Soundararajan–Thorner §2 and Brumley Appendix A](https://arxiv.org/abs/1804.03654)

Here “prime ideals” means \(k=1\) at each ideal, even when its norm is a rational prime power. The arithmetic inputs give a simpler conditional test. They give no upper window estimate for the centered prime-ideal count and no fixed-target Goldbach correlation.
