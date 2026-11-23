# A single positive window for a finite family of number-field extensions

The compact log-average criterion extends to arbitrary finite extensions \(E/k\), including non-Galois ones. For a finite family, one positive weighted sum detects both zeta functions of every pair. Triangular log-averaging allows a different width for each pair.

## Exact positive split observable without Galois symmetry

Write \(d=[E:k]\). For a prime ideal \(\mathfrak p\) of \(k\), let \(f_{\mathfrak P}\) be the residue degrees of the primes \(\mathfrak P\mid\mathfrak p\) in \(E\). For \(j\ge1\) define
\[
 u_{\mathfrak p,j}=\frac1d\sum_{\substack{\mathfrak P\mid\mathfrak p\\f_{\mathfrak P}\mid j}} f_{\mathfrak P}.
\]
The local degree formula \(\sum_{\mathfrak P}e_{\mathfrak P} f_{\mathfrak P}=d\) gives \(0\le u_{\mathfrak p,j}\le1\), including at ramified primes. Define \(A_{E/k,\lambda}(x)\) as before with these \(u\)'s: at \(v=N\mathfrak p^j\) use weight
\[
 \log N\mathfrak p\left[u_{\mathfrak p,j}(x/v-1)_+
 +(1-u_{\mathfrak p,j})\lambda^{-1}(\lambda x/v-1)_+\right].
\]
The coefficient \(d\,u_{\mathfrak p,j}\log N\mathfrak p\) is the total Dedekind weight in \(E\) above \(\mathfrak p\) at norm \(v\). Indeed each \(\mathfrak P\) of degree dividing \(j\) contributes its prime power \(\mathfrak P^{j/f_{\mathfrak P}}\). Thus the same splitting identity holds:
\[
 A_{E/k,\lambda}(x)-x\bigl(\log x-1-c_k+(1-d^{-1})\log\lambda\bigr)
 =\lambda^{-1}G_k(\lambda x)+d^{-1}\bigl(G_E(x)-\lambda^{-1}G_E(\lambda x)\bigr).
\]
Here \(c_k=\operatorname{FP}_{s=1}(\zeta'_k/\zeta_k)\) and \(G_F\) is the original centered smoothed Dedekind observable. For the non-Galois cubic \(x^3-x-1\) over \(\mathbb Q\), the unramified \(j=1\) weights are \(1,1/3,0\) on splitting types \(111,12,3\). This gives a direct criterion using discriminant \(23\) of the cubic field, without passing to the degree-six closure. [Prior Galois and compact-average identities](https://github.com/Sodelin/Research-Commons/blob/4ce6b959ed1ad5384a4db13b97fe7c2c39c12252/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/compact-average-galois-window.md).

## Distinct positive averaging kernels

For each pair \((E_i,k_i)\), fix a width \(B_i>0\) and a positive coefficient \(w_i\). Average its identity using \(v=\log\lambda\) with density \(2(B_i-v)/B_i^2\) on \(0\le v\le B_i\). Its expected \(v\) is \(B_i/3\). Sum the centered observables with coefficients \(w_i\) to form \(C(x)\), using smooth centers \(x(\log x-1-c_{k_i}+(1-d_i^{-1})B_i/3)\). The uncentered count is positive and only uses norms up to \(e^{\max_i B_i}x\).

For any fixed \(\kappa>0\), RH for every Dedekind zeta function in this finite family is equivalent to the following one inequality: for every sufficiently small \(\epsilon>0\) and every \(\eta>0\), there are arbitrarily large \(Y\) with
\[
 \int_Y^{Y^{1+\kappa}} C(x)_+\,x^{-1/2-\epsilon}\,\frac{dx}{x}\le Y^\eta.
\]
The converse follows by the conditional prime ideal theorem and partial summation for each \(G_F\), with the same degree and discriminant dependence as in the single-pair proof, summed with the fixed weights. [Grenié–Molteni, Corollary 1.2](https://doi.org/10.1090/mcom3031).

For sufficiency the transform at a strip zero \(z\) of any field has residue \(-1/[z(z-1)]\) times
\[
 \sum_i w_i\left[(1-Z_i(z))\,m_{E_i}(z)/d_i+Z_i(z)\,m_{k_i}(z)\right],
 \qquad Z_i(z)=\frac2{B_i^2}\int_0^{B_i}(B_i-v)e^{(z-1)v}\,dv .
\]
The compact lower-limit corrections are entire and the normalization cancels the poles at one. Crucially, \(0<\Re Z_i(z)<1\) throughout the open strip. The upper inequality follows by replacing the cosine in the integral by one. For \(z=\sigma+i\tau\) with \(\tau>0\), integrate the cosine transform of \(f(v)=(B_i-v)e^{-(1-\sigma)v}\) by parts. The boundary vanishes and the result is \(\tau^{-1}\int_0^{B_i}(-f'(v))\sin(\tau v)dv\). Here \(-f'(v)\) is positive and strictly decreasing. A second integration by parts against the nonnegative running sine integral \((1-\cos(\tau v))/\tau\) proves strict positivity. The case \(\tau<0\) is conjugate and \(\tau=0\) is immediate. Thus the residue numerator has strictly positive real part whenever any multiplicity is nonzero. At real zeros the residue itself is positive. Finiteness gives isolated poles, and compact averaging preserves continuity and the required exponential growth bound. Landau and the functional equations prove the criterion. [Pinned Landau theorem and hypotheses](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84).

This uses hand identities and a hand application of the generic Lean theorem. It does not establish the window estimate for the cubic example or the larger family.
