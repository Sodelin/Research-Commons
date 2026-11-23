# A positive window for standard automorphic families using a local growth bound

Fix a number field \(F\) and a finite dual-closed multiset \(\mathcal F\) of unitary cuspidal representations of \(\mathrm{GL}_{n_i}(\mathbb A_F)\). In degree one exclude pure norm characters, whose standard \(L\)-functions have shifted poles. Write \(L_i\) for the finite standard \(L\)-functions, \(H=\prod_i L_i\), and \(d=\sum_i n_i\). Choose \(0\le\delta<1/2\) so that, for each member of the family,
\[
 |\alpha_{i,\mathfrak p,j}|\le(\mathrm N\mathfrak p)^\delta,\qquad
 \Re\mu_{i,\nu}\ge-\delta.
\]
Here \(\alpha\) are the actual finite Euler roots, including at ramified places, and \(\mu\) are the shifts of the archimedean factors after writing complex gamma factors as pairs of real ones. These conditions follow from a bound \(\delta\) for local Langlands exponents. Such a \(\delta<1/2\) is available in every fixed degree from Luo–Rudnick–Sarnak with the ramified extension by Müller–Speh. For example, all degree-two cuspidal representations over number fields admit \(\delta=7/64\) by Blomer–Brumley. For everywhere tempered representations take \(\delta=0\). The argument uses only the two displayed bounds. [Luo–Rudnick–Sarnak and the all-place statement, Blomer–Brumley introduction and Theorem 1](https://annals.math.princeton.edu/2011/174-1/p18) · [Müller–Speh, Proposition 3.3](https://doi.org/10.1007/s00039-004-0452-0)

The result is an exact positive-count criterion for the completed standard \(L_i\) alone. Dedekind zeta serves as an arithmetic reference. Its zeros need not satisfy RH for either implication.

## Positive count and fixed reference subtraction

Put \(H_\delta(s)=H(s+\delta)\) and let \(\Lambda_A(n)\) denote the logarithmic-derivative coefficients of \(A\), with the negative sign. Unitarity and dual closure make \(\Lambda_{H_\delta}\) real. At a local prime power, summing at most \(d\) roots and then damping by \(q^{-\ell\delta}\) for \(q=\mathrm N\mathfrak p\) gives \(|\Lambda_{H_\delta}(\mathfrak p^\ell)|\le d\log q\). Grouping by norm therefore gives
\[
 |\Lambda_{H_\delta}(n)|\le d\Lambda_F(n)
 \quad\text{and}\quad
 0\le\Lambda_{\zeta_F^d H_\delta}(n)\le2d\Lambda_F(n),
\]
where \(\Lambda_F\) refers to \(\zeta_F\). The cap includes all ramified Euler factors.

For \(x>0\), write \(S_A(x)=\sum_n\Lambda_A(n)(x/n-1)_+\), and fix a dilation \(B>0\) with \(T_B S(x)=e^{-B}S(e^Bx)\). Define
\[
 A_B(x)=T_B S_{\zeta_F}(x)+
 \frac{S_{\zeta_F^d H_\delta}(x)-T_B S_{\zeta_F^d H_\delta}(x)}{2d}.
\]
This is a nonnegative prime-power count. At each norm \(n\) it distributes the weight \(\Lambda_F(n)\) between the two nonnegative kernels in fractions
\(\tfrac12+\Lambda_{H_\delta}(n)/(2d\Lambda_F(n))\) and its complement. Norms with zero reference weight contribute zero. Use the exact arithmetic reference
\[
 C_{\delta,B}(x)=A_B(x)-\tfrac12\bigl(S_{\zeta_F}(x)+T_B S_{\zeta_F}(x)\bigr)
     =\frac{S_{H_\delta}(x)-T_B S_{H_\delta}(x)}{2d}.
\]
In particular no Dedekind zero contributes through the reference. The subtraction only uses the same finite prime powers as the count. It also removes any linear term proportional to \(x\) in \(S_{H_\delta}(x)\).

## Exact window equivalence

Set \(\theta=1/2-\delta>0\). For any fixed \(\kappa>0\), the critical-line statement for the completed \(L_i\) is equivalent to this single condition: for every \(\eta>0\), there are arbitrarily large \(Y\) such that
\[
 \int_Y^{Y^{1+\kappa}} C_{\delta,B}(x)_+x^{-\theta}\,\frac{dx}{x}\le Y^\eta .
\]
Equivalently \(x^\delta C_{\delta,B}(x)\) has the positive-part window at the exact square-root exponent.

For sufficiency, the Laplace transform at \(\Re s>2\) of \(S_{H_\delta}(e^u)\), for \(u\ge0\), is \((-H_\delta'/H_\delta)(s)/[s(s-1)]\). The translation \(T_B\) multiplies this transform by \(e^{(s-1)B}\) and adds an entire initial-interval correction. Standard analytic continuation, functional equations and boundary nonvanishing give holomorphy of \(H_\delta\), and nonvanishing on \(\Re s\ge1\). The gamma factors of the shifted family are regular and nonzero in \(\Re s>0\) by the shift bound. Thus the simple pole of the kernel at \(1\) is removed by \(1-e^{(s-1)B}\), and the only poles in the positive half-plane are at shifted zeros \(z=\rho-\delta\) of completed members, with residue
\[
 -\frac{(1-e^{(z-1)B})m(z)}{2d\,z(z-1)}.
\]
Here \(m(z)\) is the sum of their multiplicities. Since \(0<\Re z<1\), the real part of \(1-e^{(z-1)B}\) is positive, so every such zero survives. Real poles have positive real residue. The cap gives continuity and \(O(e^{2u})\) growth of the count at \(e^u\), and the pole set is discrete. The window with \(u=\log x\) and upper envelope \(C_{\delta,B}(e^u)_+\) is exactly the hypothesis of the pinned generic Landau theorem. It rules out \(\Re z>\theta\), hence \(\Re\rho>1/2\). The completed functional equations exchange each member with its dual and give the other half. [Godement–Jacquet analytic theory](https://doi.org/10.1007/BFb0070263) · [Jacquet–Shalika boundary nonvanishing](https://doi.org/10.1007/BF01390166) · [Tate for degree one](https://sites.math.rutgers.edu/~alexk/2023S572/Tate1950.pdf) · [Pinned Landau theorem](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84)

For the converse alone, assume GRH for the completed family. Write
\[
 A_H=|\operatorname{disc}F|^d\prod_i\mathrm N_F\mathfrak q_i,\qquad
 \mathcal L=\log A_H+\sum_{i,\nu}\log(3+|\mu_{i,\nu}|).
\]
The completed unshifted \(H\) is entire of order at most one and satisfies reflection about \(1/2\) up to sign. Pair the zeros \(1/2\pm it_\rho\) in the Hadamard product. At \(2+it\), the Euler bound and the gamma derivative bound give
\[
 \sum_\rho \frac1{1+(t-t_\rho)^2}
 \ll \mathcal L+[F:\mathbb Q]d\log(3+|t|),
\]
counting multiplicities. Shift smoothed Perron for \(S_{H_\delta}\) to \(\Re s=\theta/2\). The difference of zero fractions from those evaluated in the unshifted logarithmic derivative at \(2+it\) is \(O_\delta((1+(t-t_\rho)^2)^{-1})\) per zero. The vertical kernel \(1/[s(s-1)]\) is integrable against the resulting logarithmic bound. For the horizontal sides use heights in successive high unit intervals separated from the zero ordinates by a small constant times the reciprocal of the local zero-count bound. There the log derivative grows at most quadratically in that bound, which the kernel absorbs. The \(s=1\) residue is the linear term \(-xH_\delta'(1)/H_\delta(1)\). The shifted zeros contribute \(O_\delta(x^\theta\mathcal L)\) in absolute value because their residue denominators have size \(\gg_\delta 1+t_\rho^2\). The normalized dilation cancels the linear term exactly, so
\[
 |C_{\delta,B}(x)|\ll_{\delta,B} \frac{x^\theta}{d}\mathcal L \qquad (x\ge2).
\]
This implies the stated window for each fixed family. The upper estimate is conditional. The forward implication assumes no GRH. [Hadamard and smoothed contour calculation for the earlier family](https://github.com/Sodelin/Research-Commons/blob/b1c130361458779bcd92df222cc62d9fb59d78df/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-finite-central-character.md)

## Why the damping matters

At a fixed prime ideal, an undamped finite multiset of Euler roots has bounded power traces only if all roots have modulus at most one. In fact \(\sum_{k\ge1}(\sum_j\alpha_j^k)t^k=\sum_j\alpha_jt/(1-\alpha_jt)\); a root outside the unit disk creates a genuine pole at its reciprocal because the positive multiplicities of identical roots add. A fixed Dedekind offset cannot restore a two-sided cap in that case. The damped construction uses a known local growth exponent and keeps the reference as an exact arithmetic count. It transfers no additive information to Goldbach.

The coefficient completion, residue argument and uniform conditional estimate are hand proofs. The generic Landau implication is Lean-verified. Its automorphic application and the forward window are unverified in Lean, and the forward estimate remains open. No numerical zero tests are used.
