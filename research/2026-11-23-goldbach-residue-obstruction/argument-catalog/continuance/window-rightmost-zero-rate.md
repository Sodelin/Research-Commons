# Quantitative detection of the rightmost zero by late windows

This is a hand consequence of the pinned generic Landau theorem, applied to the finite positive family of number-field observables. A single sparse window estimate with a nonzero exponential budget still gives an explicit zero exclusion.

Let \(C(x)\) be the centered compact triangular aggregate for a fixed finite family of pairs, with positive weights. Write \(g(u)=C(e^u)\). Let \(\beta_*\) be the supremum of the real parts of all nontrivial zeros of all Dedekind zeta functions in the family. For \(0<\theta<1\) and \(\kappa>0\), define
\[
 I_{\theta,\kappa}(U)=\int_U^{(1+\kappa)U} g(u)_+\,e^{-\theta u}du.
\]
If \(\beta_*>\theta\), then
\[
 \lim_{U\to\infty}U^{-1}\log I_{\theta,\kappa}(U)
 =(1+\kappa)(\beta_*-\theta).
\]
In particular, if \(I_{\theta,\kappa}(U)\le e^{cU}\) for arbitrarily large \(U\) and \(c\ge0\), then \(\beta_*\le\theta+c/(1+\kappa)\). This last assertion is informative when the bound on the right is below one. [Prior noncancellation proof](https://github.com/Sodelin/Research-Commons/blob/f84b1a09cc21d468327e65645edbbf64879354a2/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/triangular-average-number-field-windows.md).

## Lower bound by a right-end subwindow

Fix \(\theta'\) with \(\theta<\theta'<\beta_*\). The transform has a surviving pole to the right of \(\theta'\), because the triangular kernels prevent cancellation at every zero of every field. Choose any fixed \(0<\kappa'<\kappa\). By the contrapositive of the pinned Landau theorem, for some \(\eta>0\) and every sufficiently large \(V\),
\[
 I_{\theta',\kappa'}(V)>e^{\eta V}.
\]
Indeed, if every \(\eta>0\) allowed arbitrarily late such windows at the opposite inequality, \(g_+\) itself would be an admissible nonnegative upper envelope in the theorem, contradicting the pole. All other pole and growth hypotheses have already been checked for this aggregate. [Pinned Landau theorem](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84) · [Pinned upper envelope condition](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean#L25-L29).

Take \(V=(1+\kappa)U/(1+\kappa')\), so \([V,(1+\kappa')V]\) is the rightmost subwindow of the original interval. Nonnegativity gives
\[
 I_{\theta,\kappa}(U)\ge e^{(\theta'-\theta)V} I_{\theta',\kappa'}(V).
\]
Thus the lower limit is at least \((1+\kappa)(\theta'-\theta)/(1+\kappa')\). Let \(\kappa'\downarrow0\) and \(\theta'\uparrow\beta_*\), holding the auxiliary parameters fixed before each \(U\)-limit. This obtains the claimed exponent without needing a value of \(\eta\).

## Upper bound by the ordinary smoothed Perron shift

If \(\beta_*<1\), choose \(\beta_*<\sigma<1\). For each field in the fixed finite family, shift the unnormalized smoothed Perron integral of \(-(\zeta'_F/\zeta_F)(s)x^s/(s(s-1))\) from \(\Re s=2\) to \(\Re s=\sigma\). The pole at \(1\) gives exactly the normalization \(x(\log x-1-c_F)\). On the new line the logarithmic derivative is \(O_{F,\sigma}(\log(|\Im s|+3))\) by the standard local zero expansion and count, since each nearby zero is separated from the line by the fixed gap \(\sigma-\beta_*\). The same estimate on the intervening horizontal segments for large height, and the two denominator factors, justify the shift. Hence \(G_F(x)=O_{F,\sigma}(x^\sigma)\). Finite weighted sums and compact rescaling preserve this bound. [Lagarias–Odlyzko, Lemmas 5.4 and 5.6](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf).

It follows that the upper limit is at most \((1+\kappa)(\sigma-\theta)\); let \(\sigma\downarrow\beta_*\). If \(\beta_*=1\), the elementary coefficient bound gives \(G_F(x)=O_F(x(1+\log x)^2)\) and hence the same upper limit with \(\beta_*=1\). This completes the quantitative statement. It does not give the prime-ideal window bound; it determines the asymptotic obstruction an off-line zero would impose on that bound.
