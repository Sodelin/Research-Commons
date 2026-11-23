# Sign mass and an off-line obstruction in the balanced \(n=1\) Artin band

Fix the standard \(S_3\) factor \(L(s)=\sum_n a(n)n^{-s}\), its reciprocal coefficients \(\mu_L\), and \(\Lambda_L\) from \(-L'/L\). Let \(B>0\), \(0<\eta<1/6\), \(\lambda=1/2-\eta\) and \(A=x^\lambda\). Use the exact \(K_B\) in the original polynomial-cutoff remainder with \(U=\lfloor A\rfloor\) and \(P=A\). Its \(n=1\) band is the actual signed sum
\[
 T_1(x)=-\frac14\sum_{\substack{p>A,\ m>A\\pm\le e^Bx}}
       \Lambda_L(p)\mu_L(m)K_B(pm/x).
\tag{1}
\]
Both variables are originally bounded by \(e^Bx^{1-\lambda}\). This is one part of the exact expansion with \(h=mn\), \(a(n)\), and \(K_B(pmn/x)\), since \(a(1)=1\). [Original Mellin normalization](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md)

There is unconditional order-\(x(\log x)^{2/3}\) mass of both signs in the full \(n=1\) band, with order-\(x\) mass already on the prime \(m\) subband. A finite isolated off-line top line gives a further conditional obstruction for the signed band, of larger logarithmic order than the original window itself.

## Exact sign masses on the prime subband

Let \(C,D\) be Frobenius classes and let \(\delta_C,\delta_D\) be the corresponding Chebotarev densities. With \(c_\lambda=\log((1-\lambda)/\lambda)>0\), one has, pointwise as \(x\to\infty\),
\[
 \sum_{\substack{p>A,\ q>A\\ \operatorname{Frob}_p\in C,\ \operatorname{Frob}_q\in D}}
      (\log p)K_B(pq/x)
   \sim \delta_C\delta_D Bc_\lambda x .
\tag{2}
\]
All primes are rational, and primes with \(pq>e^Bx\) have weight zero. To prove (2), write \(\theta_C(t)=\delta_Ct+o(t)\) and \(\pi_D(t)=\delta_D\operatorname{Li}(t)+o(t/\log t)\), uniformly in relative error for all \(t\ge A\) as \(A\to\infty\). For fixed \(q\), partial summation in \(p\) replaces the inner sum by \(\delta_C\int_A^\infty K_B(tq/x)\,dt\), with error \(o_A(1)x/q\). The cutoff term at \(A\) and the derivative term each have this bound, since the weight is bounded, monotone, and supported in \(t\le e^Bx/q\). Summing over \(q\) costs \(O(x)\) before the \(o_A(1)\) factor, by \(\sum_{A<q\le e^Bx/A}1/q\ll_{\lambda,B}1\) from Chebyshev.

For the remaining \(q\) partial summation, set \(J(v)=\int_A^\infty K_B(tv/x)\,dt\). It is monotone nonincreasing, supported in \(v\le e^Bx/A\) and satisfies \(0\le J(v)\le Bx/v\). Consequently the error from the \(o(t/\log t)\) in \(\pi_D(t)\) is \(o(x)\). Indeed its variation integral is bounded by \(o_A(1)\) times
\[
 \frac A{\log A}J(A)+\int_A^{e^Bx/A} J(v)\,d(v/\log v)
 \ll_{\lambda,B}x .
\]
Replacing both sums by their integrals and then setting \(r=tv/x\) gives the main term
\[
 \delta_C\delta_D x
 \int_{x^{2\lambda-1}}^{e^B}
 K_B(r)\log\!\left(\frac{\log(xr/A)}{\log A}\right)\,dr.
\]
The log factor is nonnegative and bounded on this moving support. It tends to \(c_\lambda\) at each fixed \(r>0\). Dominated convergence and \(\int_0^{e^B}K_B(r)\,dr=H_B(1)=B\) prove (2). If \(p\) is replaced by Lebesgue measure on \((A,\infty)\), the same computation gives \(\delta_D Bc_\lambda x+o(x)\). These statements use fixed-field Chebotarev, including all classes and both endpoint conventions exactly. [Lagarias–Odlyzko, Theorem 1.3](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf)

If \(m=q\) is prime then \(\mu_L(q)=-a(q)\). Its contribution in (1) is therefore \(+\tfrac14 a(p)a(q)(\log p)K_B(pq/x)\). The trace is \(2,0,-1\) on identity, transposition and 3-cycle, of densities \(1/6,1/2,1/3\). Let \(T_{1,\rm pp}^+(x)\) and \(T_{1,\rm pp}^-(x)\) denote the sums of the positive and of the magnitudes of the negative individual summands on this ordered prime subband. Formula (2) gives
\[
 T_{1,\rm pp}^+(x)\sim \frac{Bc_\lambda}{18}x,\qquad
 T_{1,\rm pp}^-(x)\sim \frac{Bc_\lambda}{18}x.
\tag{3}
\]
The density-weighted mass in each case, before the factor \(1/4\), is \(2/9\): the positive strata give \(4(1/6)^2+(1/3)^2\), and the mixed strata give \(4(1/6)(1/3)\). The diagonal \(p=q\) costs \(O_B(\sqrt x)\) by Chebyshev and does not affect either asymptotic. If desired, fixed-field effective Chebotarev improves the trivial signed difference to \(O_{L,B,\lambda}(x e^{-c_L\sqrt{\log x}})\): the trace mean is zero, and the exceptional-zero term in Theorem 1.3, if present, is eventually smaller than this error at fixed field. Apply this trace estimate in the \(p\) partial summation before summing absolute values over \(q\). These arguments do not establish a square-root bound for the signed difference.

The same sign issue is visible in the centered completely split version of the \(n=1\) band. Set \(e\) for the identity class. Its prime subband is
\[
 \frac34\left[
 \sum_{\substack{p>A,\ \operatorname{Frob}_p=e\\q>A}}
      a(q)(\log p)K_B(pq/x)
 -\frac16\int_A^\infty\sum_{q>A}a(q)K_B(qt/x)\,dt\right].
\tag{4}
\]
The four measures from discrete/continuous first coordinates and identity/3-cycle \(q\) are mutually singular on the product of the real first coordinate and the discrete second coordinate. Each has absolute mass \((Bc_\lambda/24)x+o(x)\) by (2) and its continuous variant. The discrete identity and continuous 3-cycle strata are positive. The discrete 3-cycle and continuous identity strata are negative. Thus the positive and negative variations of (4) are each \((Bc_\lambda/12)x+o(x)\). These are statements about the actual sign mass before cross-stratum cancellation. The centered sign masses do not require a zero hypothesis.

## Unconditional sign mass on the full \(n=1\) band

Let \(f(m)=|\mu_L(m)|\). It is nonnegative and multiplicative. The local inverse roots give \(f(p)\le2\), \(f(p^2)\le1\) and \(f(p^j)=0\) for \(j>2\), including the ramified factors. At an unramified prime the values of \(f(p)\) are \((2,0,1)\) on the three classes above, so fixed-field Chebotarev gives
\[
 \sum_{p\le t}f(p)\log p=\frac23t+O_L(t e^{-c_L\sqrt{\log t}}).
\]
Wirsing's nonnegative mean-value theorem therefore gives
\[
 \sum_{m\le t}f(m)\sim C_L t(\log t)^{-1/3},\qquad
 C_L=\frac1{\Gamma(2/3)}
     \prod_p(1-p^{-1})^{2/3}
         \big(1+f(p)p^{-1}+f(p^2)p^{-2}\big)>0 .
\tag{4a}
\]
The theorem applies with bounded prime powers and average prime coefficient \(2/3\). In its finite Euler-product formula, Mertens' product cancels the Euler-constant factor. The remaining displayed product converges to a positive limit, since the effective prime asymptotic makes \(\sum_p(f(p)-2/3)/p\) convergent and all higher terms are absolutely summable. [Wirsing, Math. Ann. 143 (1961), 75–102](https://doi.org/10.1007/BF01351892)

For the total variation in (1), replace \(a(p)\) by \(|a(p)|=f(p)\) and \(\mu_L(m)\) by \(f(m)\). The inner \(p\)-partial summation replaces the sum by \((2/3)J(m)\) with error \(O(xe^{-c\sqrt{\log x}}/m)\), with \(J\) as above. Its sum over \(m\) against \(f(m)\) is negligible since \(f(m)\le d_2(m)\) and \(\sum_{m\le e^Bx}d_2(m)/m\ll_B(\log x)^2\). For the outer variable use (4a), whose main term is also asymptotic to \(C_L\int_2^t(\log v)^{-1/3}dv\). Its residual relative error is \(o_A(1)\) for \(v\ge A\). Partial summation costs at most \(o_A(1)\) times
\[
 \frac{A}{(\log A)^{1/3}}J(A)
 +\int_A^{e^Bx/A}J(v)\,d\!\left(\frac{v}{(\log v)^{1/3}}\right)
 \ll x(\log x)^{2/3}.
\]
The continuous integral has the asymptotic
\[
 \int_A^\infty J(v)\frac{dv}{(\log v)^{1/3}}
  \sim \frac32 B\big((1-\lambda)^{2/3}-\lambda^{2/3}\big)
       x(\log x)^{2/3}.
\]
Indeed after \(r=tv/x\), the inner integral is
\(\frac32[(\log(xr/A))^{2/3}-(\log A)^{2/3}]\) for \(r\ge x^{2\lambda-1}\), so dominated convergence applies as in (2).

In the actual signed sum (1), use instead the zero mean of \(a(p)\) and the same effective prime error. This bounds the signed result by \(O_{L,B,\lambda}(x e^{-c\sqrt{\log x}})\) after decreasing \(c\) to absorb \((\log x)^2\). Thus the positive and negative masses of the full band are each asymptotic to
\[
 \frac{C_L B}{8}\big((1-\lambda)^{2/3}-\lambda^{2/3}\big)
       x(\log x)^{2/3}.
\tag{4b}
\]
For the centered band in (4) extended to all \(m>A\), use the signed measure
\(-\tfrac34(d\theta_e-\tfrac16\,dt)\otimes\mu_L\) with the same cutoffs and kernel. Its first-coordinate total variation is \(\tfrac34(d\theta_e+\tfrac16\,dt)\), since atomic and Lebesgue measures are mutually singular. Repeating the calculation gives the same asymptotic with \(3C_L B/16\) in place of \(C_L B/8\). The signed centered band has the same \(O(x e^{-c\sqrt{\log x}})\) upper bound from the centered Chebotarev error. All these masses retain the actual two-coordinate support and the original \(K_B\).

## Prefix estimates and dyadic mixed variation for the full band

Write \(A_L(t)=\sum_{p\le t}\Lambda_L(p)\) and \(M_L(t)=\sum_{m\le t}\mu_L(m)\). The two sharp-prefix arguments from the polynomial cutoff give \(A_L(t),M_L(t)\ll_\epsilon t^{\beta_*+\epsilon}\), where \(\beta_*\) is the actual completed zero supremum. On a clipped dyadic rectangle \([T,2T]\times[S,2S]\), the supremum, both edge variations, and the mixed Stieltjes variation of \(K_B(p m/x)\) are \(O_B(1)\). Use log coordinates and \(f(v)=K_B(e^v)\). The function \(f\) is continuous, and \(f'\) has bounded variation, with its only jumps at \(0,B\). The mixed distributional derivative on the log rectangle is the signed measure \(d f'(v+w-\log x)\,dv\), whose total variation is at most \((\log 2)\operatorname{Var}(f')\). Smoothing \(f\) in the log variable gives ordinary double integration by parts and the same uniform variation bounds before passing to the limit. Applying it with clipped prefixes bounds each rectangle by the product of the two corresponding prefix bounds times \(O_B(1)\). Only rectangles with \(TS\le e^Bx\) contribute. Thus
\[
 T_1(x)=O_{L,B,\lambda,\epsilon}(x^{\beta_*+\epsilon}).
\tag{5}
\]
The stated prefix proof uses truncated Perron, the zero-free half-plane to the right of \(\beta_*\), and subpower growth of \(1/L\) there from a holomorphic log and three-lines. This is not an input of Artin GRH.

Under the verified Dirichlet GRH, the same dyadic argument compares (1) to its centered version, with (4) extended to all \(m>A\) and with weight \(-\mu_L(m)\) in place of \(a(q)\). For \(\xi=1,\chi\), the centered Dirichlet measure on the \(p\) coordinate has prefix
\(\sum_{p\le t}\xi(p)\log p-\mathbf 1_{\xi=1}t=O_{\xi,\epsilon}(t^{1/2+\epsilon})\).
On any retained rectangle, \(T\ge A/2\), so the corresponding mixed bound is
\[
 O_\epsilon(T^{1/2+\epsilon}S^{\beta_*+\epsilon})
 \ll_\epsilon x^{\beta_*+\epsilon}A^{-(\beta_*-1/2)}.
\]
Summing the rectangles and using \(a(p)=3\mathbf1_{\operatorname{Frob}_p=e}-(1+\chi(p))/2\) gives an overall comparison of size \(O_\epsilon(x^{\beta_*-\lambda(\beta_*-1/2)+\epsilon})\). This is strictly below the off-line growth exponent if \(\beta_*>1/2\). [Verified Dirichlet scope](https://math.mit.edu/~drew/grh/#what-was-verified)

The collision \(p\mid m\) can also be excluded from (1) at a strict lower off-line exponent. On its support \(p^3>e^Bx\) for large \(x\), because \(\lambda>1/3\). Thus \(m=pr\) with \(r<p\), and its contribution is exactly
\[
 \frac14\sum_{p>A}a(p)^2\log p\sum_{r\ge1}\mu_L(r)K_B(p^2r/x).
\]
The reciprocal prefix bound and one-variable partial summation bound this by
\[
 O_\epsilon\!\left(x^{\beta_*+\epsilon}
  \sum_{p>A}(\log p)p^{-2\beta_*-2\epsilon}\right)
  \ll_\epsilon x^{1/2+(1-2\lambda)(\beta_*-1/2)+\epsilon}.
\]
Hence the coprime part of (1) has the same conditional leading term below. In the full \(p,m,n\) expansion the collision simplifies further. Now \(rn<p\) on the support and the cutoff \(m>A\) is automatic. The sum over \(r,n\) collapses by \(\mu_L*a=\mathbf1_{\{1\}}\), so the full colliding sector is exactly the positive prime diagonal
\(\tfrac14\sum_{p>A}a(p)^2\log p\,K_B(p^2/x)=O_B(\sqrt x)\).

## Conditional signed obstruction from a finite isolated top line

Assume \(\beta=\beta_*>1/2\), that the top line consists of a finite nonempty set \(\mathcal Z\) of zeros, and that all other completed zeros have real part at most \(\beta-\Delta\) for a fixed \(\Delta>0\). This hypothesis concerns the actual zeros of \(L\). For \(\rho\in\mathcal Z\), write \(k_\rho\) for its multiplicity and \(c_\rho=\lim_{s\to\rho}L(s)/(s-\rho)^{k_\rho}\ne0\). Let \(k=\max_{\rho\in\mathcal Z}k_\rho\).

Truncated Perron at half-integers, into the zero-free gap after taking the finitely many residues, gives for some \(\delta>0\)
\[
 A_L(t)=-\sum_{\rho\in\mathcal Z}\frac{k_\rho}{\rho}t^\rho+
            O(t^{\beta-\delta}),\qquad
 M_L(t)=\sum_{\rho\in\mathcal Z} t^\rho Q_\rho(\log t)+O(t^{\beta-\delta}).
\tag{6}
\]
Here \(Q_\rho\) has degree \(k_\rho-1\) with leading coefficient
\(1/[c_\rho\rho(k_\rho-1)!]\). For the reciprocal estimate, remove the zeros of the finite top set by multiplying \(L(s)\) by \(\prod_{\rho\in\mathcal Z}[(s+1)/(s-\rho)]^{k_\rho}\). The resulting holomorphic nonvanishing function has polynomial growth and bounded log on a sufficiently right vertical line. The same holomorphic-log argument as for the sharp twisted prefix gives reciprocal growth \(O((3+|t|)^\nu)\) in any fixed closed sub-half-plane of the gap. The rational factors preserve this bound on the shifted contour away from their poles, whose exact residues yield \(Q_\rho\). Take the shifted line above \(1/2\), so that removing the higher prime powers in \(A_L\) costs \(O(\sqrt t)\), absorbed by (6). The usual half-integer truncation error with height \(t^3\) and the horizontal terms are absorbed as well.

Insert (6) by the mixed-variation calculation. An error in either prefix gains \(A^{-\delta}\) relative to \(x^\beta\), up to fixed log powers. For the main terms, set \(r=pm/x\) and \(v=\log m\). The prime density from \(\rho_1\) is \(-k_{\rho_1}p^{\rho_1-1}\,dp\), and the leading reciprocal density from \(\rho_2\) is \(m^{\rho_2-1}(\log m)^{k_{\rho_2}-1}\,dm/[c_{\rho_2}(k_{\rho_2}-1)!]\). The exact inner integral in \(v\) is over
\[
 \lambda\log x<v<(1-\lambda)\log x+\log r,\qquad r>x^{2\lambda-1}.
\]
If \(\rho_1\ne\rho_2\), it contains the oscillation \(e^{i(\Im\rho_2-\Im\rho_1)v}\), so integration by parts bounds it by \(O((\log x)^{k_{\rho_2}-1})\). If the two zeros coincide, this integral is a difference of powers divided by \(k_\rho\). The lower limit in \(r\) can be replaced by zero in its leading coefficient, and fixed powers of \(|\log r|\) are integrable against \(r^{\beta-1}K_B(r)\). Accounting for \(-1/4\) in (1) therefore gives the asymptotic
\[
 T_1(x)=x^\beta(\log x)^k
 \sum_{\substack{\rho\in\mathcal Z\\k_\rho=k}}
 \frac{H_B(\rho)\big((1-\lambda)^k-\lambda^k\big)}
      {4c_\rho(k-1)!}\,e^{i\Im\rho\,\log x}
 +O\!\left(x^\beta(\log x)^{k-1}\right).
\tag{7}
\]
This calculation retains the exact product boundary and kernel. Under the verified Dirichlet input, the centered \(n=1\) expression has the same leading term by the strict power gap following (5).

If the sole top zero is the real zero \(\beta\), its leading coefficient in (7) is positive. Indeed \(L(s)>0\) for real \(s>\beta\) by the Euler product to the right of one and nonvanishing on the intervening real interval, so \(c_\beta>0\); also \(H_B(\beta)>0\). For general finite \(\mathcal Z\), the leading real trigonometric polynomial in (7) is nonzero, with constant coefficient nonnegative, by the same sign argument when the real frequency is present. Its positive part has integral bounded below uniformly on intervals of sufficiently large fixed log length. The average square on such intervals is bounded below by the sum of squared coefficients up to \(O(1/\text{length})\), and the average itself is its nonnegative constant coefficient up to the same error. Dividing the square-integral bound by the supremum and using \(T_+=(|T|+T)/2\) gives the claim.

Under this top-line hypothesis the original \(C_{0,B}(x)\) is \(O(x^\beta)\). Shifting its Mellin contour into the same gap crosses only finitely many simple logarithmic-derivative poles and gives that bound directly. Its whole polynomial prime remainder differs by a strict power lower than \(x^\beta\). Consequently the \(n\ge2\) sector must cancel the \(x^\beta(\log x)^k\) leading term in (7), including the positive mass on long fixed log windows. In the fixed-interval integral with square-root weight the positive lower bound for \(n=1\) is \(\gg X^{\beta-1/2}(\log X)^k\) when the interval ends at \(X\). This is a conditional obstruction to discarding the \(n=1\) band or bounding every \(n\) component separately. It does not establish that a top-line zero exists or that the total signed remainder is square-root size.

The sign masses in (3), (4) and (4b) and the upper bound (5) are hand proofs. Equation (7) is conditional on the stated finite isolated top-line hypothesis. The full signed upper-window estimate remains open. No new Lean verification or numerical checks were performed.
