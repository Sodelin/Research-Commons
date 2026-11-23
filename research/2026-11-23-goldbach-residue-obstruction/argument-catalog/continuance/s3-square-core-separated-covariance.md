# A squarefree-core range of the retained prime–inverse covariance

Work with the standard \(S_3\) Artin factor \(L(s)\), with inverse coefficients \(\mu_L\), standard coefficients \(a(n)\), and \(\Lambda_L\) from \(-L'/L\). The original balanced covariance has cutoffs \(P=x^\lambda\), \(U=\lfloor x^\lambda\rfloor\), \(1/3<\lambda<1/2\), and retains the sign and kernel
\[
 -\frac14 \Lambda_L(p)\mu_L(m)a(n)K_B(pmn/x),
 \quad p>P,\quad m>U,\quad n\ge1,\quad pmn\le e^Bx .
\tag{1}
\]
We give a bound on an actual subset of this signed sum. It uses the quadratic character in the square part of \(m\), while keeping the original lower cuts and product boundary. We write \(\beta_*\) for the actual supremum of the real parts of the completed Artin zeros. No Artin zero exclusion is assumed. [Exact polynomial cutoffs](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd)

Every nonzero \(\mu_L(m)\) can be written with \(m=ab^2\), where \(a,b\) are squarefree and coprime, and then
\[
 \mu_L(ab^2)=\mu(a)a(a)\eta(b).
\tag{2}
\]
Here \(\eta\) is the nonprincipal quadratic character of the resolvent, with the factors at all ramified rational primes omitted. Indeed the local inverse at an unramified prime has linear coefficient \(-a(p)\) and quadratic coefficient \(\eta(p)\). At a ramified prime its degree is at most one, since \(\rho\) is faithful and the inertia invariants are a proper subspace. This justifies (2) on all local support. [Pinned squarefree-core factorization](https://github.com/Sodelin/Research-Commons/commit/ee0116a4311b3556c361afdacf16d622024c246a)

Let \(R_{\le C}(x)\) be the part of (1) with \(a\le C\le U\) in (2), without further restriction on \(n\). For any \(\epsilon>0\),
\[
 |R_{\le C}(x)|
 \ll_{\epsilon,L,B,\lambda}
 x^{\beta_*+\epsilon}U^{q-\beta_*} C^{1-q},
 \qquad
 q=\begin{cases}
       1/4 & \text{without a Dirichlet zero hypothesis},\\
       1/5 & \text{using the verified Riemann zeta RH}.
    \end{cases}
\tag{3}
\]
In this range the terms are already separated, meaning \((p,m)=1\): \(a\le U<p\) excludes \(p\mid a\), and \(p\mid b\) would imply \(p^3\le e^Bx\), impossible for large \(x\). When \(C=U^\kappa\), the saving relative to \(x^{\beta_*+\epsilon}\) is \(U^{\beta_*-q-\kappa(1-q)}\). This is a fixed power for \(\kappa<1/3\) in the first case and \(\kappa<3/8\) in the second, even when \(\beta_*=1/2\). Under the same Dirichlet input used for the centered split covariance, the proof gives the same bound for its exact centered counterpart. [Centered \(p\)-tail](https://github.com/Sodelin/Research-Commons/commit/4bfc76b31db848316d834a98b0b468381feee86a)

## The second Perron integral

For fixed \(a\), write
\[
 D_a(w)=\sum_{\substack{b\ge1\\(b,a)=1}}
 \mu^2(b)\eta(b)b^{-w}
 =\frac{L(w,\eta)}{L(2w,\eta^2)}
          \prod_{p\mid a}(1+\eta(p)p^{-w})^{-1}.
\tag{4}
\]
On every fixed half-plane \(\Re w\ge r>0\), the finite product is \(O_{r,\epsilon}(a^\epsilon)\). The reciprocal denominator is uniformly bounded for \(r>1/2\) by absolute convergence, or has subpower vertical growth for \(r>1/4\) under the verified Riemann zeta RH. Here \(\eta^2\) is principal, with only finitely many omitted Euler factors. The numerator is entire because \(\eta\) is nonprincipal. Thus on each such permitted line and the strip to its right,
\[
 |D_a(r'+iy)|\ll_{L,r,\epsilon}
 a^\epsilon (3+|y|)^{(1-r')_+/2+\epsilon}.
\tag{5}
\]
On the line \(r\), its numerator has dyadic first moment
\[
 \int_{|y|\le V}|L(r+iy,\eta)|\,dy
       \ll_{L,r,\epsilon} V^{1+(1/2-r)_++\epsilon}\quad(V\ge2).
\tag{6}
\]
For \(r>1/2\), use the standard fixed-Dirichlet mean square and Cauchy–Schwarz. For \(r<1/2\), apply the functional equation and Stirling, then the mean square on \(1-r>1/2\) on dyadic bands. Finitely many imprimitive Euler factors on the fixed lines are bounded. [Dirichlet mean-square method and local factors](https://github.com/Sodelin/Research-Commons/commit/304b341ad0a4a99eb16055613bfafceb7c476850) · [Verified zeta RH](https://math.mit.edu/~drew/grh/#what-was-verified)

On the outer Mellin line \(s=\sigma+it\), with \(\sigma>\beta_*\) fixed and close to \(\beta_*\), the exact \(b\)-factor is the tail
\[
 T_a(2s)=\sum_{\substack{b>\sqrt{U/a}\\(b,a)=1}}\mu^2(b)\eta(b)b^{-2s}.
\]
Let \(z=\lfloor\sqrt{U/a}\rfloor+1/2\), so the integer cutoff is unchanged, and use a truncated negative-line Perron integral on \(\Re w=1+\delta-2\sigma<0\), with \(0<\delta<2\sigma-1\) and height \(T\). The integrand for the tail is \(-D_a(2s+w)z^w/w\). The overall minus sign follows because the vertical step at a negative abscissa is \(-1\) for \(z/b<1\) and \(0\) for \(z/b>1\). The truncation error is
\[
 O_\epsilon(z^{1+\delta-2\sigma+\epsilon}/T).
\tag{7}
\]
Indeed for \(b\asymp z\) the usual kernel error is bounded by \(z^{-2\sigma}\min(1,z/(T|b-z|))\), and outside this range use absolute convergence on \(2\sigma+\Re w=1+\delta\). This estimate is uniform in the outer ordinate \(t\). Shift the negative line left to \(\Re w=r-2\sigma\). The \(w=0\) pole stays to the right and (4) is holomorphic throughout the shift.

## The joint vertical estimate

The outer Mellin transform of (1) at fixed \(a\), apart from its scalar coefficient \(-\mu(a)a(a)/4\), is
\[
 x^s H_B(s)[D_p(s)-B_P(s)]\,L(s)a^{-s} T_a(2s),
 \qquad
 D_p(s)=\sum_p\Lambda_L(p)p^{-s},\quad
 B_P(s)=\sum_{p\le P}\Lambda_L(p)p^{-s}.
\]
It starts in absolute convergence. Shift to \(\sigma>\beta_*\) before opening the second Perron, so the two first prime factors combine into \(D_p(s)-B_P(s)\ll_\epsilon P^\epsilon(3+|t|)^\epsilon\) by the twisted prime prefix argument. There are no crossed poles. The \(b\)-tail is itself absolutely convergent throughout this outer shift, since \(2\sigma>1\). The fixed \(L\) convexity bound and \(|H_B(\sigma+it)|\ll_B(3+|t|)^{-2}\) dominate the outer absolute weight by
\[
 g(t)\ll_\epsilon P^\epsilon(3+|t|)^{-1-\min(\sigma,1)+\epsilon}.
\tag{8}
\]
The same bound holds with the centered split prime transform under the verified Dirichlet input.

For the inner Perron vertical segment \(w=r-2\sigma+iv\), integrate (8) jointly with \(D_a(r+i(2t+v))/(1+|v|)\). In the range \(|v|\ge4|t|\), one has \(|2t+v|\asymp |v|\) away from a bounded interval, so on dyadic \(v\) bands (6) gives an average gain over pointwise convexity. The total \(v\)-integral here is \(O_\epsilon(a^\epsilon T^{(1/2-r)_++\epsilon})\), uniformly in \(t\). In the other range \(|v|<4|t|\), apply (5) and use that \(\min(\sigma,1)>(1-r)/2\) in the integrable outer weight. Thus, suppressing \(P^\epsilon\), the contribution of the inner vertical segment is
\[
 \ll a^\epsilon z^{r-2\sigma}T^{(1/2-r)_++\epsilon}.
\tag{9}
\]
For the inner horizontal segments use (5) at \(r'\in[r,1+\delta]\) and \(y=2t\pm T\). The outer integral is \(O(P^\epsilon a^\epsilon T^{(1-r')_+/2+\epsilon})\). With \(T=z^\theta\), \(0<\theta<1\), the function \(r'\mapsto r'+\tfrac{\theta}2(1-r')_+\) is increasing. Therefore the horizontal contribution and (7) are both \(O(P^\epsilon a^\epsilon z^{1+\delta-2\sigma+\epsilon}/T^{1-\epsilon})\).

Choose \(r>1/2\) very close to \(1/2\) and \(T=z^{1/2}\) unconditionally. The resulting inner cost is \(O(P^\epsilon a^\epsilon z^{1/2-2\sigma+\epsilon})\). Under verified zeta RH, choose \(r>1/4\) very close to \(1/4\) and \(T=z^{3/5}\). The exponent in (9) tends to \(1/4+(3/5)(1/4)-2\sigma=2/5-2\sigma\), and the horizontal and truncation exponent tends to \(1-3/5-2\sigma=2/5-2\sigma\). Hence the latter cost is \(O(P^\epsilon a^\epsilon z^{2/5-2\sigma+\epsilon})\). Restoring \(x^\sigma a^{-\sigma}\), using \(z\asymp\sqrt{U/a}\) and \(|a(a)|\le d_2(a)\), then summing over \(a\le C\) gives
\[
 O_\epsilon(x^\sigma P^\epsilon U^{q-\sigma+\epsilon} C^{1-q+\epsilon})
\]
with the \(q\) in (3). Take \(\sigma>\beta_*\) sufficiently close and absorb the auxiliary epsilons to obtain (3).

## Compatibility with the shortened \(n\)-support

The same proof works for the conductor-23 example with the additional exact restriction \(n\le N\), uniformly in \(N\) in the original arithmetic support. Replace \(L(s)\) in the outer weight by \(F_N(s)=\sum_{n\le N}a(n)n^{-s}\). For \(d=1/3\) in \(\sum_{n\le t}a(n)=O(t^d)\) one has
\[
 |F_N(\sigma+it)|\ll |L(\sigma+it)|+N^{d-\sigma}(1+|t|),
 \qquad
 |F_N(\sigma+it)|\ll_\epsilon N^{(1-\sigma)_++\epsilon}.
\tag{10}
\]
Use the first bound for \(|t|\le N^{1-d}\) and the second above it. For all \(q_0\le1/4\), the \(L\)-part of (10) stays integrable after multiplying by \((3+|t|)^{q_0+\epsilon}|H_B(s)|\). The other part summed on dyadic \(t\) bands is \(O(1)\) uniformly in \(N\), since for \(\sigma\le1\) its maximal exponent in \(N\) is \(d-\sigma+(1-d)q_0\le1/2-\sigma<0\). The case \(\sigma>1\) follows by absolute convergence on the outer line.

For the vertical estimate, in the region \(|v|\ge4|t|\), keep the previous dyadic average in \(v\) and use the uniform unweighted \(t\)-integral just proved. In the complementary region, on a dyadic \(t\) band of size \(V\), first integrate \(t\) for each \(|v|\le8V\). The shift \(2t+v\) is \(O(V)\), so (6) gives cost \(O(V^{1+q_0+\epsilon})\), with \(q_0=(1/2-r)_+\). Now integrate \(dv/(1+|v|)\) at logarithmic cost and use (10) with the convergent dyadic envelope. For the horizontal sides, when \(|t|\le T\), use (5) at height \(O(T)\) and the uniform unweighted \(t\)-integral. When \(|t|>T\), use the same mean bound in \(t\), with \(q_0=(1/2-r')_+\), on every dyadic band. Thus (9) and the horizontal estimates are unchanged. The conductor-23 \(n\)-truncation has no additional factor of \(N\). The unconditioned \(r>1/2\) version also works with \(d=1/2\) for any fixed \(S_3\) factor, since then \(q_0=0\). [Conductor-23 lattice discrepancy](https://github.com/Sodelin/Research-Commons/commit/ccb83b63ae2ac2afafd6465ef614c63a9c102c1f)

This hand estimate bounds the exact signed linear sum with a sufficiently small squarefree inverse core. In the exact centered version with locked cutoffs and a mesoscopic window, let \(S(v)\) be the full normalized linear sum and \(S_{\le C}(v)\) its small-core part. The full pointwise envelope is \(O_\varepsilon(X^{\beta_*-1/2+\varepsilon})\). With \(C=U^\kappa\) in either stated range, (3) bounds \(S_{\le C}\) by that envelope times a fixed power saving. Therefore the integrated difference \(S^2-(S-S_{\le C})^2\) also has a fixed power saving from the off-line covariance exponent \(2\beta_*-1\). To compare the actual separated pair covariance, subtract the diagonal and neighboring terms from this difference by the original near-pair estimate. This applies because each subseries groups at \(h=mn>U\) and its coefficients are bounded by \(d_4(h)\). The surviving large-core covariance still needs a signed bound. This comparison concerns the full companion range. [Exact separated covariance](https://github.com/Sodelin/Research-Commons/commit/db66db1688943b76a404d6db5dc5a9477cbe2ed3)
