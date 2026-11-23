# A short-complement split-prime window for the original \(S_3\) dilation

For every fixed \(S_3\) standard Artin factor, the original upper-window test can use just primes \(p>x^\alpha\), for any fixed \(1/2<\alpha<1\). The companion integer in the exact Vaughan sum is at most \(e^B x^{1-\alpha}\). In an off-line case the discarded part has a strictly smaller exponential growth rate than the positive window signal. With the verified Dirichlet GRH, the abelian components on the shortened support can also be subtracted at square-root cost. The resulting target is one exact centered sum over completely split primes. The new implication leaves the upper estimate for that sum open. [Pinned original prime-only Vaughan reduction](https://github.com/Sodelin/Research-Commons/commit/67193280a4865df1e309eacae5424701e1ad1f6d) · [Pinned fixed-length Artin window detection](https://github.com/Sodelin/Research-Commons/commit/304b341ad0a4a99eb16055613bfafceb7c476850)

## A variation bound from the quadratic resolvent

Let \(\rho\) be the standard representation, \(L(s)=L(s,\rho)\), \(a(n)\) its coefficients, \(\mu_L(m)\) the inverse coefficients and \(\Lambda_L(n)\) the coefficients of \(-L'/L\). Write \(K_B(t)=e^{-B}(e^B/t-1)_+-(1/t-1)_+\) as in the original undamped window. Fix a starting value \(Y\) and an integer \(U=U(Y)=Y^{o(1)}\), \(U\ge1\). With \(\beta_U=\mu_{L,>U}*a\), define the actual inner weight for \(t>0\) by
\[
 W(x,t)=\sum_{h>U}\beta_U(h)K_B(ht/x)
 =K_B(t/x)-\sum_{m\le U}\mu_L(m)\mathscr K_{x/(mt)}(a),
 \qquad \mathscr K_y(a)=\sum_{n\ge1}a(n)K_B(n/y).
 \tag{1}
\]
Both expressions are exact since \(\mu_L*a=\mathbf1_{\{1\}}\). The support on the first side is \(h>U\), \(ht\le e^B x\). By the pinned Vaughan reduction, for some \(Q=Y^{1/2+o(1)}\) chosen as there, the original count is
\[
 C_{0,B}(x)=-\tfrac14\sum_{p>Q}\Lambda_L(p) W(x,p)
             +O_{L,B,\epsilon}(x^{1/2+\epsilon}),
 \qquad x\ge Y.
 \tag{2}
\]

For this Artin factor there is a fixed-field estimate
\[
 A(z)=\sum_{n\le z}a(n)=O_L(\sqrt z+1).
 \tag{3}
\]
Here is a ray-class counting proof that covers both signs of the quadratic resolvent discriminant. Let \(F\) be that quadratic field and \(\vartheta\) the nonprincipal cubic Hecke character with \(L(s)=L_F(s,\vartheta)\). For each ray class choose an integral ideal \(\mathfrak c\) prime to the finite conductor \(\mathfrak f\), in the inverse class. For real \(F\), include both real places in the ray modulus, inflating the character if necessary. Ideals \(\mathfrak a\) in the chosen class and coprime to \(\mathfrak f\) have \(\mathfrak a\mathfrak c=(\eta)\) with \(\eta\in\mathfrak c\), \(\eta\equiv1\bmod\mathfrak f\), with the prescribed positivity in the real case. Their norms are \(|N\eta|/N\mathfrak c\). The congruence condition selects a single coset of the lattice \(\mathfrak f\mathfrak c\). In the imaginary case count its points in the disk \(|\eta|^2\le zN\mathfrak c\), excluding zero, and divide by the number of ray units. In the real case use the two positive embeddings and choose \(1\le\eta_1/\eta_2<\varepsilon_0^2\), where \(\varepsilon_0>1\) is the first embedding of a generator of the positive ray units. Every unit orbit has one representative in this sector. Intersect it with \(\eta_1\eta_2\le zN\mathfrak c\). This is a dilation by \((zN\mathfrak c)^{1/2}\) of a fixed bounded sector with piecewise smooth boundary. In both cases the lattice count is area divided by covolume with error \(O_{F,\mathfrak f,\mathfrak c}(\sqrt z+1)\), by covering the boundary with fixed fundamental cells. The area is proportional to \(zN\mathfrak c\), and the covolume is proportional to \(N\mathfrak c\,N\mathfrak f\). Thus the linear term is common to all ray classes and cancels against \(\vartheta\). This proves (3), including the grouping of ideals at the same rational norm. [Artin induction](https://doi.org/10.1007/BF02941010) · [Pinned Hecke and conductor identification](https://github.com/Sodelin/Research-Commons/commit/304b341ad0a4a99eb16055613bfafceb7c476850)

Partial summation with (3) and the bounded piecewise monotone \(K_B\) gives \(|\mathscr K_y(a)|\ll_{L,B}\sqrt y\) for all \(y>0\), using its vanishing below \(e^{-B}\). This function is locally absolutely continuous in \(\log y\), and almost everywhere
\[
 \frac{d}{d\log y}\mathscr K_y(a)
       =y\sum_{y<n<e^B y}\frac{a(n)}n
       =O_{L,B}(\sqrt y)
 \tag{4}
\]
by the same partial summation. On every dyadic interval \([T,2T]\) meeting \(t\le e^Bx\), (1), (4) and \(|\mu_L(m)|\le d_2(m)\) give
\[
 \sup_{t\in[T,2T]}|W(x,t)|+
       \operatorname{Var}_{[T,2T]}W(x,t)
 \ll_{L,B} U^{1/2}\log(2U)\sqrt{x/T}.
 \tag{5}
\]
Indeed the terms at \(m\) contribute \(O(\sqrt{x/(mT)})\), while the \(K_B(t/x)\) term has bounded size and variation. The bound still holds on clipped intervals.

## Prime support can start at any fixed power below one

Put \(\beta_*=\sup_\rho\Re\rho\) for the actual completed zeros of \(L\). For every fixed \(\epsilon>0\), the prime-supported prefix obeys
\[
 \sum_{p\le z}\Lambda_L(p)=O_{L,\epsilon}(z^{\beta_*+\epsilon}).
 \tag{6}
\]
For \(\beta_*<1\) this follows from truncated Perron at a half-integer and a shift to any fixed \(\beta_*<\sigma<1\). The local logarithmic derivative estimate on that strip is \(O_{L,\sigma}(\log(3+|t|))\). Chebyshev and \(|\Lambda_L(p^k)|\le2\log p\) bound the higher powers by \(O(\sqrt z)\). When \(\beta_*=1\), use Chebyshev directly. The same prefix envelope is proved in the pinned exception-set memo. This statement uses the actual zero supremum. GRH for this factor corresponds to the case \(\beta_*=1/2\). [Pinned prefix envelope](https://github.com/Sodelin/Research-Commons/commit/a511a288e37ae183f9769249395e088797d021c3)

Fix \(1/2<\alpha<1\), let \(P=x^\alpha\), and apply partial summation to (6) with weight (5) on each dyadic block between \(Q\) and \(P\). The factor from any fixed power of \(U=Y^{o(1)}\) can be absorbed into the \(\epsilon\) exponent. Summing at most \(O_B(\log x)\) blocks gives
\[
 \left|\sum_{Q<p\le P}\Lambda_L(p)W(x,p)\right|
 \ll_{L,B,\alpha,\epsilon}
        x^{1/2+\alpha(\beta_*-1/2)+\epsilon}.
 \tag{7}
\]
In the off-line case \(\beta_*>1/2\), the exponent in (7) is strictly less than \(\beta_*\) for sufficiently small \(\epsilon\). In the critical-line case it is \(1/2+\epsilon\). Write
\[
 R_\alpha(x)=-\tfrac14\sum_{p>x^\alpha}\Lambda_L(p)W(x,p).
\]
From (2), (7) and \(|v_+-w_+|\le|v-w|\), replacing \(C_{0,B}\) by \(R_\alpha\) preserves the exact off-line rate \((\beta_*-1/2)V+o(V)\) of the logarithm of the positive-part integral on windows \([u_0,V]\) with \(u_0=\log Y\), \(V\to\infty\), \(V-u_0\to\infty\). Indeed integrate the error with weight \(e^{-u/2}du\) and choose \(\epsilon\) below a fixed fraction of \((1-\alpha)(\beta_*-1/2)\). The resulting bound is exponentially smaller than the pinned off-line lower rate. In the critical-line case, the original square-root envelope and (7) give arbitrarily small power budgets on these windows. The surviving \(h\) in (1) satisfy \(U<h\le e^B x^{1-\alpha}\). This step uses the off-line detection signal to remove a signed range whose unconditional pointwise square-root charge is unavailable.

## Isolating the nonabelian primes at Dirichlet square-root cost

Let \(\chi\) be the quadratic Dirichlet character of the resolvent. For an unramified prime the \(S_3\) values of the standard trace give exactly
\[
 \Lambda_L(p)
 =\left(3\mathbf1_{\{p\text{ splits completely in the closure}\}}
                  -\tfrac12(1+\chi(p))\right)\log p .
 \tag{8}
\]
For large \(Y\) all primes under consideration are unramified. The verified Dirichlet GRH for \(1\) and \(\chi\) implies the usual fixed-character bounds
\[
 \sum_{p\le t}\xi(p)\log p
 =\mathbf1_{\xi=1}\,t+O_\chi(\sqrt t\,\log^2(2t)),
 \qquad \xi\in\{1,\chi\}.
\]
For clarity, (6) with \(\beta_*=1/2\) and Perron applied to the Dirichlet logarithmic derivative also suffices with \(O_{\chi,\epsilon}(t^{1/2+\epsilon})\), and the principal pole produces \(t\). Applying partial summation with (5) to the errors gives on the **same** shortened prime support
\[
 \sum_{p>P}\xi(p)\log p\,W(x,p)
 =\mathbf1_{\xi=1}\int_P^{e^B x}W(x,t)\,dt
       +O_{L,B,\epsilon}(x^{1/2+\epsilon}).
 \tag{9}
\]
Endpoint terms at \(P\) are included using the prefix convention \(\le P\). The main term is explicit, with the finite integral
\[
 \int_P^{e^B x}W(x,t)\,dt
 =x\sum_{U<h\le e^Bx/P}\frac{\beta_U(h)}h
             \int_{hP/x}^{e^B}K_B(v)\,dv .
\]
The sum and integral both have finite support. [Verified Dirichlet theorem statements](https://math.mit.edu/~drew/grh/#what-was-verified)

Substituting (9) into (8) proves the final square-root comparison
\[
 R_\alpha(x)
 =-\frac34\left(
   \sum_{\substack{p>x^\alpha\\p\text{ splits completely}}}
        (\log p)W(x,p)
  -\frac16\int_{x^\alpha}^{e^Bx}W(x,t)\,dt\right)
    +O_{L,B,\epsilon}(x^{1/2+\epsilon}).
 \tag{10}
\]
Thus the explicit one-sided window for the negative centered bracket in (10) is equivalent to the original criterion under the verified abelian input. Its support uses a companion of length \(O(x^{1-\alpha})\) for any fixed \(\alpha<1\). Equations (7) and (10) are hand arguments. No new Lean verification, numerical checks, Artin zero exclusion, or fixed-target Goldbach pair estimate is supplied by them. The new arithmetic upper bound required in (10) remains open.


## The same prime localization for fixed tempered degree two

The reduction (7) also follows for every fixed tempered standard cuspidal degree-two factor over \(\mathbb Q\), with an arbitrary \(\epsilon\) in its error exponent. The only replacement necessary in (3) is the bound \(A(z)\ll_{L,\epsilon}z^{1/2+\epsilon}\). To prove it, use truncated Perron for the entire standard \(L\)-function at a half-integer \(y=\lfloor z\rfloor+1/2\), with \(c=1+1/\log y\) and height \(T=y^{1/2}\). The local parameter bound gives \(|a(n)|\le d_2(n)\ll_\epsilon n^\epsilon\). The terms \(n\asymp y\) in the Perron error are bounded by \(O_\epsilon(y^{1+\epsilon}\log y/T)\) on using \(|n-y|\ge1/2\) and the truncation factor \(\min(1,y/(T|n-y|))\). The remaining terms cost \(O(y(\log y)^2/T)\) by absolute convergence on \(c\). The degree-two convexity bound on a fixed line \(\sigma_0>0\) is \(O_{L,\varepsilon}((3+|t|)^{1-\sigma_0+\varepsilon})\). Shifting from \(c\) to \(\sigma_0\) produces vertical cost \(O(y^{\sigma_0}T^{1-\sigma_0+\varepsilon})\). The same convexity bound on the horizontal segments gives at most \(O_\varepsilon(y^{1/2+\varepsilon})\) there, since \(y/T=\sqrt y\) and \(c=1+O(1/\log y)\). Choose \(\sigma_0,\varepsilon\) sufficiently small to obtain the asserted exponent. Partial summation gives (5) with an additional factor \(x^\epsilon\), and the rest of (7) is unchanged. Thus a fixed dual-closed tempered cuspidal degree-two family also allows only the primes \(p>x^\alpha\), with an error smaller than its off-line positive-window growth rate. The character identity in (8) is the \(S_3\)-specific step. [Pinned degree-two convexity contour](https://github.com/Sodelin/Research-Commons/commit/ee0116a4311b3556c361afdacf16d622024c246a) · [Fixed-length detection for cuspidal degree two](https://github.com/Sodelin/Research-Commons/commit/c26f3c7b129acbb1101df51e08a885647ea74ac4)
