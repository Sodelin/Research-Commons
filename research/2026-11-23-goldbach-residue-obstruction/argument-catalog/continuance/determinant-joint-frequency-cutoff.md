# Joint Poisson frequencies give the \(20/19\) determinant cutoff

This is an independent hand derivation of the cutoff reported at the other Codex thread's 20:38 checkpoint. Keep the original fixed even \(N\), square-root block, sharp short cutoff \(d>D\), exact middle-count mask and rough endpoint. Put \(H=\sqrt N\) and \(L=\log N\). The signed long-divisor sum is \(O_A(N/L^A)\) for every fixed \(A\) on \(d\le H^a\) for each fixed \(1\le a<20/19\). The new step is to keep the Poisson frequency as the third variable in Bettin–Chandee's Theorem 1. [Reported checkpoint](https://github.com/Sodelin/Research-Commons/blob/9ff7ef0b3/communications/2026-11-23-codex-number-theory-progress.md) · [Bettin–Chandee, Theorem 1, equation (1.2)](https://arxiv.org/pdf/1502.00769).

## Exact masks and the zero mode

Use the dyadic boxes \(d\asymp U,\ \ell\asymp V\) of the pinned unequal-box proof. The absolute endpoint trim lets us take \(UV\gg N/L^B\) with fixed \(B\) large in terms of \(A\), and the actual support always has \(UV\ll N\). Smooth the \(q\) and \(\ell\) edges at inverse-logarithmic relative width. The pinned divisor-moment argument makes the edge changes negligible. Use the same five mask expansions, each truncated at \(H^\rho\) for sufficiently small fixed \(\rho>0\). Their tails have arbitrary log savings for every such \(\rho\), as checked in the previous note. Write \(q=E q'\), \(\ell=F\ell'\), \(g=(E,F)\), \(E'=E/g,\ F'=F/g\), and retain \(g\mid N\). The mask sizes satisfy \(E\le H^{5\rho}\), \(F\le H^\rho\); the number of mask tuples and the individual middle-count coefficient contribute at most \(H^{6\rho}\) together. [Pinned masks and endpoint treatment](https://github.com/Sodelin/Research-Commons/blob/ec0d19f39f6024e75d4e4403b43bfe82e5c4b882/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-asymmetric-range.md).

Any surviving solution has \((E'h,F'd)=1\), after keeping the separated coprimality conditions as in the pinned proof. Poisson in \(q'\) on its one residue class gives phases \(e(\nu (N/g)\overline{E'h}/(F'd))\), up to an immaterial simultaneous sign convention. Here \(e(t)=e^{2\pi i t}\). Put \(x=h/H,\ y=d/U\),
\[
 T_0=\frac{EF'U}{H},\qquad
 {\cal A}_\nu(x,y)=\frac1{T_0 y}\int f(u)\,G\!\left(\frac{N-H^2ux}{UVy}\right)e\!\left(-\frac{\nu u}{T_0y}\right)du ,
\]
where \(u=q/H\), \(f\) is the smooth \(q\) weight and \(G\) the smooth positive-support \(\ell\) weight, with all derivatives fixed log powers. This follows by the change of variables \(q'=Hu/E\) in the Poisson integral. In particular the plus equation stays exact. At \(\nu=0\) the reciprocal factor is \(1/\operatorname{lcm}(E,F)\) times \(H/U\); the smooth integral has polylogarithmic size and variation in \(h/H\) because \(H^2/(UV)\ll L^B\). The original masked \(h\)-prefix estimate and reciprocal Euler sum give the same zero-mode bound as in the pinned proof. The dyadic cases \(U\le H\) already obey the previous determinant bound on the nonzero modes. [Pinned fixed-box Poisson amplitude](https://github.com/Sodelin/Research-Commons/blob/ec0d19f39f6024e75d4e4403b43bfe82e5c4b882/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-fixed-box.md).

## Nonzero modes on \(U\ge H\)

For each fixed \(h,d\), integrate by parts in \(u\) to discard \(|\nu|>T_0H^\rho\). Summing the resulting powers \((1+|\nu|/T_0)^{-j}\) cancels the amplitude factor \(T_0^{-1}\) and leaves a factor \(O_j(L^{C_j}H^{-\rho(j-1)})\) per \(h,d\). Take \(j\) large in terms of fixed \(\rho\) so the sum over \(O(HU)\) coefficient positions and all masks saves a power of \(H\).

For a dyadic range \(|\nu|\asymp T\le T_0H^\rho\), use the normalized variables \((x,y,\nu/T)\). The amplitude and every mixed derivative with at most one derivative per variable are \(O(L^C T_0^{-1}H^{3\rho})\). Indeed \(x,y\) lie at fixed scales, \(H^2/(UV)\ll L^B\), and derivatives of the oscillatory factor cost at most \(1+T/T_0\ll H^\rho\) each. Three-variable partial summation therefore reduces to prefix boxes in the three variables with that amplitude cost. The prefixes can be implemented with zeros in the coefficient arrays of Theorem 1.

Apply that theorem with lengths \(M\asymp E'H\), \(N_0\asymp F'U\), \(A_0\asymp T\) and phase parameter \(\vartheta=N/g\), handling the two frequency signs separately. The three coefficient norms multiply to \(O(L^C\sqrt{HUT})\), using the sparse \(h,d\) positions rather than their rescaled interval lengths. Since \((N/g)T_0/((E'H)(F'U))=1\), the phase factor of Theorem 1 is \(O(H^{\rho/2})\). Use
\[
 T\le H^{7\rho}U/H,\quad MN_0\ll H^{6\rho}HU,\quad M+N_0\ll H^{5\rho}U .
\]
The two terms of the theorem, before the common power \(H^{O(\rho+\epsilon)}\), become
\[
 H(U^2)^{7/20}U^{1/4}=HU^{19/20},
 \qquad
 H(U^2)^{3/8}(U^2/H)^{1/8}=H^{7/8}U .
\]
Here the leading factor \(H\) comes from \(T_0^{-1}\sqrt{HUT}\ll HH^{\rho/2}\). The second term is at most the first for \(U\ll H^{5/2}\), which contains this range. The mask sum, derivatives and Mellin or Fourier harmless exponents cost \(H^{O(\rho+\epsilon)}\), with an absolute constant in the new power budget. For fixed \(a<20/19\), choose \(\rho,\epsilon>0\) so \(1+(19/20)a+O(\rho+\epsilon)<2\). This gives a power saving uniformly in every retained high-\(U\) box. Summing the logarithmically many boxes, frequency ranges and count extractions proves the cutoff.

This also upgrades the four parity-mode bounds to \(P=H^a\) for each fixed \(a<20/19\). The parity relabelings move only the log weights and independent sharp edges, which the amplitude and sparse coefficient estimates above allow. Beyond the cutoff the endpoint-parity difference is still controlled, while the original sum remains open. [Parity-mode transfer](https://github.com/Sodelin/Research-Commons/blob/f29fbbc1aaddfa721c757f3f0c5acb6fd058daad/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-four-parity-components.md).
