# A positive automorphic window for Ramanujan's modular form

Fix \(B,\kappa>0\). A single one-sided estimate on a nonnegative-weight prime-power count gives a conditional critical-line criterion for \(\zeta\), the unitary \(L(s,\Delta)\), and \(L(s,\operatorname{Sym}^2\Delta)\). This example has finite conductor \(1\). All three factors appear in the criterion through their zero multiplicities, including any zeros they share.

## Known analytic inputs

Write \(\pi=\pi_\Delta\) for the unitary representation attached to the level-one form of weight \(12\), and \(\alpha_p,\beta_p\) for its normalized Satake parameters. Then \(\alpha_p\beta_p=1\) and \(|\alpha_p|=|\beta_p|=1\). The symmetric-square lift is cuspidal by Gelbart–Jacquet. Indeed, \(\pi\) has no quadratic self-twist, since a nontrivial quadratic character of \(\mathbb Q\) ramifies at some finite prime and twisting destroys unramifiedness there. The two cuspidal factors are entire, have completed functional equations, and are nonzero on \(\Re s=1\). They are self-dual, and their archimedean factors are holomorphic and nonzero in the open strip. [Deligne, Théorème 8.2](https://doi.org/10.1007/BF02684373) · [Gelbart–Jacquet, Theorem 9.3 and Remark 9.9](https://doi.org/10.24033/asens.1355) · [Jacquet–Shalika](https://doi.org/10.1007/BF01390166)

Define
\[
 P(s)=\zeta(s)^2 L(s,\pi)^2 L(s,\operatorname{Sym}^2\pi)
     = L\bigl(s,(1\boxplus\pi)\times(1\boxplus\pi)^\vee\bigr)
\]
as an identity of finite-part \(L\)-functions. For \(a_{p,j}=\alpha_p^j+\beta_p^j\), the symmetric-square trace at \(p^j\) is \(a_{p,j}^2-1\). Hence the coefficients of \(-P'/P\) are supported on prime powers and satisfy
\[
 \Lambda_P(p^j)=(1+a_{p,j})^2\log p,\qquad 0\le \Lambda_P(p^j)\le 9\Lambda(p^j).
\]
The only pole of \(P\) in \(\Re s>0\) is the double pole at \(1\), and there are no zeros on \(\Re s=1\). The Euler products exclude zeros on \(\Re s>1\).

## Count and hypothesis

Put \(u_{p,j}=(1+a_{p,j})^2/9\), write \(h_+=\max(h,0)\), and define
\[
 A_v(x)=\sum_{p^j}\log p\left[
  u_{p,j}(x/p^j-1)_+
 +(1-u_{p,j})e^{-v}(e^v x/p^j-1)_+\right],\qquad 0\le v\le B .
\]
The weights are nonnegative and only prime powers at most \(e^Bx\) enter. With \(w_B(v)=2(B-v)/B^2\) and \(\gamma=\operatorname{FP}_{s=1}(\zeta'/\zeta)(s)\), set
\[
 C_B(x)=\int_0^B w_B(v)A_v(x)\,dv-
         x\left(\log x-1-\gamma+\frac{7B}{27}\right).
\]
For every \(0<\epsilon<1/2\) and \(\eta>0\), suppose there are arbitrarily large \(Y\) with
\[
 \int_Y^{Y^{1+\kappa}} C_B(x)_+\,x^{-1/2-\epsilon}\,\frac{dx}{x}\le Y^\eta .
 \tag{W}
\]
Then all strip zeros of all three factors lie on \(\Re s=1/2\). Conversely, the critical-line statements for the three factors imply (W). In particular, with the verified RH for \(\zeta\), (W) is equivalent to the two automorphic critical-line statements. No conductor-uniform assertion is used. [Verified scope for \(\zeta\)](https://math.mit.edu/~drew/grh/#what-was-verified)

## Hand proof of sufficiency

For \(F=P,\zeta\), let \(r_F\) be its pole order at \(1\), \(c_F=\operatorname{FP}_{s=1}(F'/F)(s)\), and
\[
 S_F(x)=\sum_n\Lambda_F(n)(x/n-1)_+,\qquad
 G_F(x)=S_F(x)-r_F x\log x+(r_F+c_F)x.
\]
Write \(T_v H(x)=e^{-v}H(e^v x)\). Coefficientwise,
\[
 A_v=T_v S_\zeta+\frac{S_P-T_v S_P}{9}.
\]
The smooth part of the right side is \(x(\log x-1-\gamma+7v/9)\). Averaging uses \(\int_0^B vw_B(v)\,dv=B/3\), and gives \(C_B\) as the same average with \(G_F\) substituted for \(S_F\).

For \(\Re s>2\), the Laplace transform of \(G_F(e^u)\) on \(u\ge0\) is
\[
 \Phi_F(s)=\frac{-F'(s)/F(s)}{s(s-1)}
                   -\frac{r_F}{(s-1)^2}+\frac{r_F+c_F}{s-1}.
\]
Both singular terms at \(1\) cancel. The shift \(T_v\) multiplies the transform by \(e^{(s-1)v}\) and adds an entire correction from the interval \([0,v]\). The averaged transform of \(C_B(e^u)\) is therefore
\[
 Z_B(s)\Phi_\zeta(s)+\frac{1-Z_B(s)}9\Phi_P(s)+E_B(s),
 \qquad Z_B(s)=\int_0^B w_B(v)e^{(s-1)v}\,dv,
\]
with \(E_B\) entire by compactness of the integration intervals. At a strip zero \(z\), write \(m_F(z)\) for its multiplicity in \(F\), with multiplicity zero when the factor is nonvanishing. The residue is
\[
 -\frac{1}{z(z-1)}
 \left(Z_B(z)m_\zeta(z)+\frac{1-Z_B(z)}9m_P(z)\right).
\]
For \(0<\Re z<1\), one has \(0<\Re Z_B(z)<1\). For the lower bound at positive frequency \(t=\Im z\), integrate the cosine transform of \((B-v)e^{-(1-\Re z)v}\) by parts. The resulting sine transform has a positive strictly decreasing weight, so integration against the running sine integral \((1-\cos(tv))/t\ge0\) gives strict positivity. Negative frequencies follow by conjugation and zero frequency by direct integration. For the upper bound use \(\cos(tv)\le1\) and \(e^{-(1-\Re z)v}<1\) for \(v>0\). The numerator of the residue has positive real part at every strip zero, even if all factors vanish at the same point. At real zeros the residue itself is real and positive. [Pinned proof for the triangular kernel](https://github.com/Sodelin/Research-Commons/blob/f84b1a09cc21d468327e65645edbbf64879354a2/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/triangular-average-number-field-windows.md)

The coefficients give \(S_F(x)=O(x(1+\log x)^2)\), and the count is continuous. Thus \(g(u)=C_B(e^u)\) is measurable and \(g(u)=O(e^{2u})\) for \(u\ge0\). The transform is holomorphic in \(\Re s>0\) away from the discrete strip zero set, with the local simple poles and real-residue signs just computed. These are the requirements of \(\mathtt{PoleData}\). With \(U=\log Y\), \(R(u)=g(u)_+\), and \(\theta=1/2+\epsilon\), (W) is \(\mathtt{WindowHypU}\) on \([U,(1+\kappa)U]\). The pinned \(\mathtt{Deduction.landau\_window}\) bounds the real part of every pole by \(\theta\). Letting \(\epsilon\downarrow0\) and applying the functional equations gives the critical line for each factor. [Pinned hypotheses](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean#L15-L30) · [Pinned Landau declaration](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84)

## Conditional converse and status

Assume the three critical-line statements for this direction. Smoothed Perron gives \(S_F(x)\) with kernel \(x^s/[s(s-1)]\) and integrand \(-F'/F(s)\). Shift from \(\Re s=2\) to \(1/2+\epsilon\). The standard local zero-count and logarithmic-derivative estimates for these fixed completed \(L\)-functions give \(F'/F(\sigma+it)=O_\epsilon(\log(|t|+3))\) at large height throughout \(1/2+\epsilon\le\sigma\le2\). In the local zero sum each denominator is separated from zero by \(\epsilon\). The horizontal integrals tend to zero and the vertical kernel is integrable. The double pole of the integrand at \(1\) contributes \(r_Fx\log x-(r_F+c_F)x\). This yields \(G_F(x)=O_\epsilon(x^{1/2+\epsilon})\). Compact averaging gives the same bound for \(C_B\), so the left side of (W) is \(O_{\epsilon,B,\kappa}(\log Y)\). [Local logarithmic-derivative estimate, Iwaniec–Kowalski, Proposition 5.7](https://doi.org/10.1090/coll/053)

The unshifted \(G_P\) also gives a window criterion by itself. Its residue at any zero is \(-m_P(z)/[z(z-1)]\), and the same contour argument proves the converse. The count in (W) instead partitions the original \(\log p\) weight between two scales at each \(p^j\). Its center involves only the zeta constant, since the unknown logarithmic-derivative constant \(c_P\) cancels in the smooth part of \(S_P-T_vS_P\).

- **Hand argument.** The positive count, residue calculation and window equivalence.
- **Lean verification.** The pinned generic \(\mathtt{Deduction.landau\_window}\) theorem. Its automorphic instantiation here is a hand argument.
- **Numerical checks.** None.
- **Open estimate.** Prove (W) for this count without assuming either automorphic critical-line statement.
- **Goldbach.** This is a single-variable prime-power count. The argument supplies no bound for a signed pair on \(qh+d\ell=N\) at a fixed target.
