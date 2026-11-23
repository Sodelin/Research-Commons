# Polynomial inverse cutoffs for the original degree-two upper window

Let \(L(s)\) be a fixed entire tempered standard degree-two factor over \(\mathbb Q\), with real coefficients and the usual completed functional equation, including the conductor-23 \(S_3\) factor. Write \(a(n)\), \(\mu_L(n)\), and \(\Lambda_L(n)\) for the coefficients of \(L\), \(1/L\), and \(-L'/L\). Denote by \(\beta_*=\sup\Re\rho\in[1/2,1]\) the actual supremum over completed zeros. No zero exclusion for \(L\) is assumed.

At fixed \(B>0\) write
\[
 K_B(t)=e^{-B}(e^B/t-1)_+-(1/t-1)_+,\qquad
 \mathscr K_x(c)=\sum_n c(n)K_B(n/x),\qquad
 H_B(s)=\frac{e^{(s-1)B}-1}{s(s-1)}.
\]
Then \(H_B\) is the Mellin transform of \(K_B\) on \(\Re s>0\), regular at \(1\) and \(O_B((1+|\Im s|)^{-2})\) on fixed bounded strips at large height. The original count is \(C_{0,B}(x)=-\mathscr K_x(\Lambda_L)/4\). [Pinned original kernel and normalization](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md)

For fixed \(u,\alpha>0\) with \(u+\alpha<1\), put \(U=\lfloor x^u\rfloor\), \(P=x^\alpha\) and \(\beta_U=\mu_{L,>U}*a\). The following comparison holds for every \(\epsilon>0\) and \(x\ge2\):
\[
 \begin{split}
 C_{0,B}(x)
 &=-\frac14\sum_{\substack{p>P,\ h>U\\ph\le e^Bx}}
       \Lambda_L(p)\beta_U(h)K_B(ph/x)
       +O_{L,B,u,\alpha,\epsilon}(x^{\gamma+\epsilon}),\\
 \gamma&=\max\left\{\beta_*(u+\alpha),\ \frac12+u\left(\beta_*-\frac12\right)\right\}.
 \end{split}
\tag{1}
\]
One can hold \(U=\lfloor Y^u\rfloor\) and \(P=Y^\alpha\) fixed on a window beginning at \(Y\), with the same error bound at every \(x\ge Y\). Thus (1) has square-root subpower cost if \(\beta_*=1/2\), and has a strict fixed power gap from the off-line growth rate if \(\beta_*>1/2\). It yields an equivalent upper-window test wherever the original rightmost-zero rate is available.

## Twisted sharp prefixes

For \(\sigma>0\) fixed and \(s=\sigma+it\), define the finite sums
\[
 M_U(s)=\sum_{m\le U}\mu_L(m)m^{-s},\qquad
 B_P(s)=\sum_{p\le P}\Lambda_L(p)p^{-s}.
\]
For each \(\epsilon>0\),
\[
 |M_U(s)|\ll_{L,\sigma,\epsilon}
     U^{(\beta_*-\sigma)_++\epsilon}(3+|t|)^\epsilon,\qquad
 |B_P(s)|\ll_{L,\sigma,\epsilon}
     P^{(\beta_*-\sigma)_++\epsilon}(3+|t|)^\epsilon
 \quad (U,P\ge2).
\tag{2}
\]
The same proof at \(\sigma=0,t=0\) gives the prime prefix estimate \(B_P(0)\ll_{L,\epsilon}P^{\beta_*+\epsilon}\).

To prove (2), the relevant complete Dirichlet series are
\[
 F_1(s)=1/L(s),\qquad
 F_2(s)=-\frac{L'}{L}(s)-Z(s),\qquad
 Z(s)=\sum_{p,k\ge2}\Lambda_L(p^k)p^{-ks}.
\tag{3}
\]
All are holomorphic on \(\Re s>\beta_*\), since the power series \(Z\) converges absolutely on \(\Re s>1/2\). On \(\Re s\ge\beta_*+\delta\), the complete logarithmic derivative is \(O_{L,\delta}(\log(3+|\Im s|))\) by horizontal separation in the local completed-zero formula and absolute convergence far to the right. In this region \(1/L(s)\ll_{L,\delta,\nu}(3+|\Im s|)^\nu\) for every \(\nu>0\). Indeed, choose the holomorphic logarithm agreeing with the Euler log to the right of one. Borel–Carathéodory on disks centered at \(2+iT\), inside the zero-free half-plane and using the polynomial growth of \(L\), bounds its modulus by \(O_{L,\delta}(\log(3+|\Im s|))\) on \(\Re s=\beta_*+\delta/2\). For an arbitrary ordinate \(t_0\), apply three-lines on the strip from there to \(2\) to \(\log L(s)e^{(s-it_0)^2}\). The left bound is \(O_{L,\delta}(\log(3+|t_0|))\) and the right bound is constant. At \(\Re s\ge\beta_*+\delta\) this gives \(\log L(s)=O_{L,\delta}((\log(3+|\Im s|))^{1-c_\delta})\) in the strip for some \(c_\delta>0\), and absolute convergence covers the rest. It suffices to take small \(\delta\), and the argument also works when \(\beta_*=1\) (where absolute convergence alone suffices). [Local logarithmic derivative, Iwaniec–Kowalski, Proposition 5.7](https://doi.org/10.1090/coll/053)

For either series \(F\), Perron for the twisted coefficients at the half-integer \(z=\lfloor U\rfloor+1/2\), initial line \(\Re w=2\) and height \(T=z^3\), uses the integral of \(F(s+w)z^w/w\). Use \(|\mu_L(n)|\le d_2(n)\) and \(|\Lambda_L(p^k)|\le2\log p\), including ramified parameters. The truncation error is \(O_{L,\sigma,\nu}(z^{-1}+z^{1-\sigma+\nu}\log z/T)\), uniformly in \(t\): away from \(n\asymp z\) it is \(O(z^2/T)\), and in that range use \(|n-z|\ge1/2\) and sum \(1/|n-z|\). Shift to \(\Re w=(\beta_*-\sigma)_++\delta>0\), staying in \(\Re(s+w)\ge\beta_*+\delta\), so the \(w=0\) pole is untouched. The vertical integral is bounded by
\[
 \ll z^{(\beta_*-\sigma)_++\delta}(3+|t|+T)^\nu\log(3+T),
\]
and horizontal sides cost \(O(z^2(3+|t|+T)^\nu/T)\). Choose \(\delta,\nu\) sufficiently smaller than \(\epsilon\). The same computation with \(P\) in place of \(U\) proves (2) for primes, and with \(\sigma=t=0\) proves the unweighted prefix bound. [Truncated Perron, Montgomery–Vaughan, Multiplicative Number Theory I, Theorem 5.2](https://doi.org/10.1017/CBO9780511618314)

## Exact convolution and removal estimates

Set \(D(n)=a(n)\log n\), so \(D=a*\Lambda_L\). The two-term convolution identity
\[
 \Lambda_L=\mu_{L,\le U}*D+(\mathbf1_{\{1\}}-\mu_{L,\le U}*a)*\Lambda_L
\tag{4}
\]
follows from \(\mu_L*a=\mathbf1_{\{1\}}\). The second term is \(\beta_U*\Lambda_L\). The exact remainder in (1) comes from it after removing the primes \(p\le P\) and all powers \(p^k\), \(k\ge2\).

For \(\mu_{L,\le U}*D\), the Mellin integrand is \(M_U(s)(-L'(s))x^sH_B(s)\). For the \(-\mu_{L,\le U}*a\) part of the small-prime contribution it is \(-M_U(s)L(s)B_P(s)x^sH_B(s)\). Both integrals shift from \(2\) to any fixed \(0<\sigma<1/2\). At that line, degree-two convexity and Cauchy's formula give \(L(s),L'(s)\ll_{L,\sigma,\nu}(3+|t|)^{1-\sigma+\nu}\), with arbitrary \(\nu>0\). Use (2) with vertical exponents small enough compared with \(\sigma\), so the product with \(H_B\) is absolutely integrable. On the horizontal parts the two polynomials, for fixed \(U,P\), are bounded with respect to height on the fixed strip. The same convexity estimate on the strip suffices to let their height tend to infinity. The two vertical bounds are
\[
 O\!\left(x^\sigma U^{\beta_*-\sigma+\nu}\right),\qquad
 O\!\left(x^\sigma (UP)^{\beta_*-\sigma+\nu}\right).
\tag{5}
\]
The \(\mathbf1_{\{1\}}\) part of the small-prime sector is \((1-e^{-B})B_P(0)\), since \(P\le x\). This costs \(O(P^{\beta_*+\epsilon})\). Taking \(\sigma,\nu\) sufficiently small bounds the whole removed part so far by \(O(x^{\beta_*(u+\alpha)+\epsilon})\). [Pinned Type I bound and contour](https://github.com/Sodelin/Research-Commons/commit/ee0116a4311b3556c361afdacf16d622024c246a)

The \(\mathbf1_{\{1\}}\) higher-power part costs \(O_B(\sqrt x)\) by Chebyshev. The \(-\mu_{L,\le U}*a\) power integrand is \(-M_U(s)L(s)Z(s)x^sH_B(s)\). Here shift only to \(\sigma=1/2+\eta<1\), where \(Z(s)\) is uniformly bounded by its absolute series. By (2) and convexity it costs
\[
 O_{L,B,\eta,\nu}\!\left(x^{1/2+\eta}U^{(\beta_*-1/2-\eta)_++\nu}\right)
 \ll_\epsilon x^{1/2+u(\beta_*-1/2)+\epsilon}
\tag{6}
\]
with small \(\eta,\nu\). The contour shift is justified by the same bounds, with the integrability supplied by the original \(H_B\). This proves (1).

If \(\beta_*>1/2\), then \(\gamma<\beta_*\) because \(u+\alpha<1\). On any log window ending at \(X\), (1) changes the integral of the positive part against \(x^{-1/2}dx/x\) by at most \(O(X^{\gamma-1/2+\epsilon}\log X)\). Hence the positive-part rate \((\beta_*-1/2)\log X+o(\log X)\) transfers to the new remainder on the windows where the original rate is available. If \(\beta_*=1/2\), the original square-root upper envelope and (1) give the required subpower budget for the remainder. At \(u+\alpha=1\) the small-prime Mellin bound has the same exponent as an off-line signal. For \(u+\alpha>1\) the proposed supporting domain is eventually empty with moving power cutoffs. This explains why a power gap requires a genuinely nonempty factor range. [Pinned rightmost-rate method](https://github.com/Sodelin/Research-Commons/blob/25fb33dfbbc5cabe79f039f741636e69ead590f5/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/window-rightmost-zero-rate.md)

## Exact support when the complementary factor is below \(U^2\)

Take \(u>(1-\alpha)/2\) in addition to \(u+\alpha<1\). Then \(h\le e^B x/P<U^2\) for large \(x\). This also holds with fixed \(U=\lfloor Y^u\rfloor\), \(P=Y^\alpha\) throughout \(Y\le x\le Y^{1+o(1)}\). Define
\[
 E_U(h)=\prod_{q\le U,\ q\mid h}q^{\min(2,v_q(h))}.
\]
For \(h>U\), the coefficient is \(\beta_U(h)=-(\mu_{L,\le U}*a)(h)\). If \(1<E_U(h)\le U\), the truncated sum includes all nonzero inverse divisors of \(E_U(h)\) and factors completely over them, with a vanishing local factor \((\mu_L*a)(q^{v_q(h)})=0\) at any \(q\le U\) dividing \(h\). Thus \(\beta_U(h)=0\). In particular, if \(h<U^2\) has a prime \(q>U\), that prime occurs once and \(h=qr\) with \(r<U\). If \(r>1\) then \(1<E_U(h)\le r<U\), so the coefficient vanishes. If \(r=1\) then \(\beta_U(q)=-a(q)\). The only surviving \(h\) are primes above \(U\) and \(U\)-smooth integers with \(E_U(h)>U\). On squarefree smooth \(h\) the exact coefficient is
\[
 \beta_U(h)=a(h)\mu(h)\!\sum_{\substack{d\mid h\\d<h/U}}\mu(d).
\tag{7}
\]
Indeed for squarefree \(m\mid h\), \(\mu_L(m)=\mu(m)a(m)\) and \(a(m)a(h/m)=a(h)\). Substitute \(d=h/m\) in the defining large-inverse sum.

In particular choose \(u=\alpha=1/2-\eta\) with \(0<\eta<1/6\), so one may use the same exact real threshold \(P=x^{1/2-\eta}\) in both factors, with \(U=\lfloor P\rfloor\). Both \(p,h\) lie between \(x^{1/2-\eta}\) and \(e^Bx^{1/2+\eta}\). The \(h=q\) prime part of (1), after removing the diagonal \(p=q\) at the unconditional cost \(O_B(\sqrt x)\), is exactly
\[
 \frac14\sum_{\substack{x^{1/2-\eta}<p<q\\pq\le e^Bx}}
 a(p)a(q)\log(pq)K_B(pq/x).
\tag{8}
\]
The sign follows from \(\beta_U(q)=-a(q)\), and pairing the two orderings replaces \(\log p\) by \(\log(pq)\). The remaining terms have \(h\) smooth with coefficient (7) when squarefree. Without this classification the exact convolution can also be viewed as a sum over \(p>P\), \(m>U\) and \(n\le e^Bx/(PU)\), with coefficient \(-\Lambda_L(p)\mu_L(m)a(n)/4\) and kernel \(K_B(pmn/x)\). Both formulations keep the original signed kernel.

These are hand arguments. They do not give the upper-window bound for the surviving prime and smooth sectors, and use no numerical checks or new Lean verification.
