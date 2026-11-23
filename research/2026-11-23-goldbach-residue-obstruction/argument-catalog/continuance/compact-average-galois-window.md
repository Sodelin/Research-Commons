# One compactly averaged Galois window detects both zeta functions

For any finite Galois extension \(M/k\), the positive ideal-prime observable in the preceding note admits a **single** compactly averaged window criterion. The criterion requires neither a separate hypothesis of RH for the base \(\zeta_k\) nor windows for two distinct rescalings. Establishing its upper bound remains open in the nonabelian examples under study.

Let \(g=[M:k]\) and \(B>0\) be fixed. Use \(G_F(x)\) for the centered smoothed Dedekind observable of a field \(F\), and \(c_k=\operatorname{FP}_{s=1}(\zeta'_k/\zeta_k)\). Let \(A_{M/k,\lambda}\) be the positive identity-versus-complement prime-ideal sum using inertia averages as in the preceding note. Its exact splitting identity, including ramification, is
\[
 A_{M/k,\lambda}(x)-x\bigl(\log x-1-c_k+(1-g^{-1})\log\lambda\bigr)
 =\lambda^{-1}G_k(\lambda x)+g^{-1}\bigl(G_M(x)-\lambda^{-1}G_M(\lambda x)\bigr).
\]
Average over \(v=\log\lambda\) uniformly on \([0,B]\), and set
\[
 C_B(x) = \frac1B\int_0^B A_{M/k,e^v}(x)\,dv
 -x\bigl(\log x-1-c_k+(1-g^{-1})B/2\bigr).
\]
This is a finite prime-power observable, because only norms up to \(e^B x\) enter the integral. The average of the \(M\)-difference is the local deficit
\[
 \frac1B\int_0^B\bigl(G_M(x)-e^{-v}G_M(e^v x)\bigr)dv
 =x\int_x^{e^B x}\left(1-\frac{\log(t/x)}B\right)\frac{t-\psi_M(t)}{t^2}\,dt .
\]
The identity follows by integrating \((G_M(t)/t)'=(\psi_M(t)-t)/t^2\) and applying Fubini on a finite interval.

## Criterion

For any fixed \(\kappa>0\), RH for both Dedekind zeta functions is equivalent to: for all sufficiently small \(\epsilon>0\) and all \(\eta>0\), there are arbitrarily large \(Y\) such that
\[
 \int_Y^{Y^{1+\kappa}} (C_B(x))_+\,x^{-1/2-\epsilon}\,\frac{dx}{x}\le Y^\eta .
\]
An \(O_\epsilon(x^{1/2+\epsilon})\) one-sided pointwise bound on arbitrarily late full windows is a sufficient special case.

To prove this, put
\[
 Z_B(s)=\frac{1}{B}\int_0^B e^{(s-1)v}\,dv.
\]
Averaging a translate \(e^{-v}G_F(e^{u+v})\) in the variable \(u=\log x\) multiplies the Laplace transform of \(G_F(e^u)\) by \(Z_B(s)\), up to an entire function from initial intervals of length at most \(B\). The averaged transform therefore has possible poles at the strip zeros of the two zeta functions, with residue at \(z\) equal to
\[
 -\frac{g^{-1}m_M(z)+Z_B(z)\bigl(m_k(z)-g^{-1}m_M(z)\bigr)}{z(z-1)},
\]
where \(m_F(z)\ge0\) denotes zero multiplicity. There is no pole at \(s=1\) because each \(G_F\) is already centered. The transforms and corrections follow first for \(\Re s>2\) by absolute convergence, and then by meromorphic continuation.

For real \(0<z<1\), \(0<Z_B(z)<1\), so the residue numerator is a positive combination of multiplicities whenever at least one is nonzero. For nonreal \(z=\sigma+i\tau\) in the strip, \(\Im Z_B(z)\) is nonzero. To see this for \(\tau>0\), extend \(w(v)=e^{(\sigma-1)v}\mathbf1_{[0,B]}(v)\) by zero beyond \(B\). Pair each positive half-period of \(\sin(\tau v)\) with the following negative half-period. The integral on each pair is nonnegative since \(w\) is decreasing, and the first pair has strictly positive integral since \(w\) decreases strictly on the positive part of its support. For \(\tau<0\) use conjugation. Therefore an affine expression in \(Z_B(z)\) with the real coefficients above either has nonzero imaginary part or is the positive constant \(g^{-1}m_M(z)\). No poles cancel.

The averaged observable is real, continuous, and \(O(e^{2u})\) on \(u\ge0\) by the same bound for \(G_F\) and compactness of \([0,B]\). Its surviving poles are simple and isolated. The positive-part envelope now meets the exact hypothesis of the pinned generic Landau theorem, with \(\theta=1/2+\epsilon\). Let \(\epsilon\) tend to zero and reflect using each Dedekind functional equation. Conversely, RH for both fields gives the uniform square-root-times-log prime ideal theorem. Partial summation gives \(G_F(x)=-x\int_x^\infty(\psi_F(t)-t)t^{-2}dt\), so each controlled term is \(O_B(\sqrt x[(1+\log x)\log |D_F|+[F:\mathbb Q](1+\log^2 x)])\). This implies the window condition. For a Galois extension, RH for the top zeta function also implies RH for the base by the Heilbronn order argument for the trivial Artin factor. [Pinned pole and envelope hypotheses](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean#L15-L29) · [Pinned Landau theorem](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84) · [Grenié–Molteni, Corollary 1.2](https://doi.org/10.1090/mcom3031).

This is a hand application of the pinned theorem. It isolates one positive count and one smooth main term whose difference would suffice. It does not establish the required window estimate or supply a same-target Goldbach correlation.
