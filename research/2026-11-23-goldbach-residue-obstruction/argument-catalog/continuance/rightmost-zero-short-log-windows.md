# Short logarithmic windows when a rightmost zero is attained

The original upper-sign kernel can detect off-line zeros on much shorter windows if a completed zero attains the rightmost real part. No positive gap to all other zeros is needed. This is a hand result from the smoothed explicit formula. It weakens the window length required under the stated spectral hypothesis and supplies no arithmetic upper estimate at the critical-line scale. [Pinned original kernel](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md)

## Statement

Let \(H\) be a fixed nonempty dual-closed standard family as in the pinned memo. Write \(F(x)=x^\delta C_{\delta,B}(x)\) for its square-root-normalized centered count, with \(B>0\) and \(0\le\delta<1/2\) as there. Let \(\beta=\sup_\rho\Re\rho\) over the completed zeros. Suppose \(\beta>1/2\) and some zero has real part \(\beta\). Then for every fixed \(\xi<\beta\) there are constants \(L_0,U_0,c,C>0\), depending on the fixed data, such that
\[
 c\,e^{(\beta-\xi)V}\ \le\
 \int_U^V F(e^u)_+e^{-\xi u}\,du\
 \le C\,e^{(\beta-\xi)V},
 \qquad U\ge U_0,\quad V-U\ge L_0 .
 \tag{1}
\]
In particular the right end of every sufficiently late interval of log length \(L_0\) carries a positive signal. The window condition at \(\xi=1/2\) cannot hold with subexponential budgets on arbitrarily late windows with log length tending to infinity, even if that length is \(o(U)\). If the completed family satisfies GRH, the pinned converse gives \(O(V-U)\) at \(\xi=1/2\). Thus under the additional hypothesis that an off-line case would have an attained rightmost real part, a tested sequence of growing sublinear log lengths suffices. A fixed length large enough for the particular offending zero spectrum also suffices. [Pinned exact-scale converse](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md)

## The top zero contributions

In smoothed Perron for the damped \(S_{H_\delta}\), the difference multiplier is \(1-e^{(s-1)B}\), where \(H_\delta(s)=H(s+\delta)\). Shift the contour from \(\Re s=2\) to a fixed negative line \(-a\) with \(a>\delta\), chosen to avoid all archimedean pole abscissae of the shifted factors. The functional equation on that line reflects to ordinary absolute convergence, and Stirling's formula bounds the finite logarithmic derivative by \(O_H(1+\log(3+|t|))\). Horizontal lines at heights spaced away from zero ordinates give \(O_H((1+\log|t|)^2)\) for the logarithmic derivative on the finite strip. This is enough for the quadratic smoothing denominator. A choice of such heights follows from the local zero count. The \(s=1\) singularity cancels. The \(s=0\) term has order at most two, and the finitely many crossed trivial zeros lie in \(\Re s\le0\). Their total contribution is \(O_{H,\delta,B}(x^\delta(1+\log x))\) after normalization, including the case of a completed zero shifted exactly to zero. The shifted line contributes \(O_{H,\delta,B}(x^{\delta-a})\). Therefore
\[
 F(e^u)=\sum_{\rho\colon\,\rho-\delta\ne0} b_\rho e^{\rho u}
       +O_{H,\delta,B}((1+u)e^{\delta u}),\qquad
 b_\rho=-\frac{m_H(\rho)\bigl(1-e^{(\rho-\delta-1)B}\bigr)}
                    {2d(\rho-\delta)(\rho-\delta-1)} .
\]
Here the sum uses distinct completed zeros, and \(m_H\) is the total multiplicity in the family. It is absolutely convergent for every fixed \(u\). In fact \(\sum_\rho |b_\rho|<\infty\), and the tail at heights \(T\ge2\) is bounded by
\(O_{H,\delta,B}((\mathcal L+D\log(T+3))/T)\) from the fixed-family local zero count. Here \(\mathcal L\) is the log conductor quantity of the pinned memo and \(D=[F:\mathbb Q]d\). [Pinned finite-height contour calculation](https://github.com/Sodelin/Research-Commons/blob/fc73be153974ee9ada2e73013a7997465ba211de/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/dilation-window-boundary-and-prime-mean-obstruction.md) · [Local log derivative and counts, Iwaniec–Kowalski Proposition 5.7](https://doi.org/10.1090/coll/053)

Every coefficient on the top line survives because \(|e^{(\rho-\delta-1)B}|<1\). The top contribution
\[
 P(u)=\sum_{\Re\rho=\beta} b_\rho e^{i\Im\rho\,u}
\]
is real by the conjugation symmetry of \(H\), and its constant coefficient is nonnegative. If present, it is the coefficient of a real top zero, whose residue is positive because \(0<\beta-\delta<1\). Dividing the full formula by \(e^{\beta u}\) gives \(P(u)+o(1)\), uniformly for \(u\) past a sufficiently large value. For each zero strictly below the top, its term is bounded by \(|b_\rho|e^{-(\beta-\Re\rho)U}\) on \(u\ge U\). Absolute summability gives convergence of this whole bound to zero even if the lower real parts approach \(\beta\).

## Uniform positive averages over fixed lengths

Choose a nonzero top coefficient, write its ordinate as \(\gamma_0\), and put \(b_*=|b_{\beta+i\gamma_0}|>0\). Truncate the top series to a finite frequency set \(E\) containing that ordinate and the constant frequency if present, so the omitted absolute mass is at most \(b_*/8\). For any interval of length \(L_0\) and any nonzero frequency \(t\), the mean of \(e^{itu}\) in absolute value is at most \(2/(L_0|t|)\). Apply this on \(E\) first at frequencies \(\gamma\ne0\) and then at \(\gamma-\gamma_0\ne0\). For example choose \(L_0\ge1\) and
\[
 L_0 \ge \frac{16}{b_*}
 \max\!\left\{
  \sum_{\gamma\in E,\ \gamma\ne0}\frac{|b_{\beta+i\gamma}|}{|\gamma|},
  \sum_{\gamma\in E,\ \gamma\ne\gamma_0}
               \frac{|b_{\beta+i\gamma}|}{|\gamma-\gamma_0|}
 \right\}.
\]
After adding the top tail back, the average of \(P\) is at least \(-b_*/4\), and the magnitude of its average against \(e^{-i\gamma_0 u}\) is at least \(3b_*/4\). Since \(\operatorname{avg}|P|\) is at least this magnitude and \(P_+=(|P|+P)/2\), the positive-part average is at least \(b_*/4\). The uniform remainder eventually has magnitude at most \(b_*/8\). This gives positive-part average at least \(b_*/8\) for \(e^{-\beta u}F(e^u)\) on every such interval. Its uniform boundedness also follows from the absolute series. Integrating over the final \(L_0\) of \([U,V]\) gives the lower bound in (1), and integrating \(O(e^{(\beta-\xi)u})\) gives the upper bound.

The same proof gives an onset estimate from finite zero data when \(\beta\) is known to be the top line. Select a height \(T\) so the absolute tail over all zeros above \(T\) is at most \(b_*/32\). Below \(T\), the finitely many zeros strictly left of \(\beta\) have a positive minimum gap \(\gamma_{\rm gap}\) to \(\beta\), unless that set is empty. Make their total absolute residue mass times \(e^{-\gamma_{\rm gap}U_0}\) at most \(b_*/32\), and likewise make the normalized elementary remainder at most \(b_*/16\) beyond \(U_0\). This uses a finite gap only. If a finite computed top \(\beta_T\) is available without knowing the global top, replace the high-zero bound by
\[
 O_{H,\delta,B}\!\left(
  \frac{\mathcal L+D\log(T+3)}{T}\,
        e^{(\overline\beta-\beta_T)V}
 \right)
\]
on \([U,V]\), where \(\overline\beta\) bounds all unchecked real parts. The same positive-mean argument applies on a bounded \(U,V\) range where this term and the lower-zero remainder meet the stated tolerances. It gives no arbitrarily late claim from a single finite cutoff.

## What this changes about the arithmetic question

The new sufficient input under attainment can be a square-root-scale negative-part average of the damped prime prefix on arbitrarily late shorter intervals \([U,U+L(U)+B]\), with \(L(U)\to\infty\) as slowly as needed and \(L(U)=o(U)\). Positivity of the original compact kernel and Fubini transfer that input to the two-scale count without boundary reversal. For degrees at most four, the prime-ideal-only replacement preserves (1), since its normalized pointwise error is \(O(\sqrt x)\) and \(\beta>1/2\). This is a gain in the length of the interval on which an arithmetic estimate would need to hold. The required square-root order is unchanged. The earlier checked prime estimates still fall short of that order. [Original prefix-to-window implication](https://github.com/Sodelin/Research-Commons/blob/fc73be153974ee9ada2e73013a7997465ba211de/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/dilation-window-boundary-and-prime-mean-obstruction.md) · [Prime-ideal reduction through degree four](https://github.com/Sodelin/Research-Commons/blob/e6df498fa097a5569f6260825b50ac7e41179aae/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/prime-ideal-windows-exterior-traces.md)

A prescribed fixed log length with no spectral dependence cannot be justified just by generic pole data. For \(g(u)=e^{bu}\cos(\gamma u)\), \(\theta<b<1\), its two nonreal simple Laplace poles have real part \(b\). It has zero positive-part integral on arbitrarily late intervals of any fixed length below \(\pi/|\gamma|\). This is an analytic model and does not assert occurrence of such a zero pattern in an automorphic family. Standard zero-free regions and zero-density upper bounds also do not furnish attainment of \(\beta\). For example, they permit a rightmost supremum \(1\) approached only at unbounded height, while boundary nonvanishing excludes any zero there. No claim about unbounded-height nonattainment is inferred from the fixed-height argument.

The explicit formula, finite-frequency means, and shortened-window implication are hand arguments. The general proportional-log-window implication remains the pinned Lean theorem. This shortened statement is not formalized here. No zero verification was performed, and no additive Goldbach estimate follows.
