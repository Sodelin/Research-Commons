# The coprime companion range in the separated Artin covariance

Fix the standard \(S_3\) Artin factor and use exactly the balanced retained covariance with its locked prime and inverse cutoffs. On \(Y\le x\le X=Y^{1+o(1)}\), write \(U=\lfloor Y^u\rfloor\), \(P=Y^\alpha\), \(u,\alpha>0\), \(u+\alpha<1\). Put \(E_P\), \(g_P\), \(b_h=\beta_U(h)/\sqrt h\), and \(S(v)\) as in the original covariance, where \(v=\log x\). Let \(\beta_*=\sup\Re\rho\) for the actual completed zeros. For a fixed cutoff \(H=Y^{u+\kappa}\), the final restriction is \(U<h<k\le H\), \(k-h>H_0\), \((h,k)=1\). The logarithmic roughness restriction \(P^-(h),P^-(k)>(\log X)^2\) may also be imposed. The signed sum of the removed terms has a fixed power saving below the off-line covariance exponent whenever \(\beta_*>1/2\). The Dirichlet inputs here concern only the trivial character and the resolvent quadratic character. [Exact covariance and retained arithmetic weights](https://github.com/Sodelin/Research-Commons/commit/db66db1688943b76a404d6db5dc5a9477cbe2ed3)

For each fixed \(\kappa>0\) with \(u+\kappa<1-\alpha\), set \(H=Y^{u+\kappa}\). Then in an off-line case \(\beta_*>1/2\) there is \(\lambda>0\), for example \(\lambda=(\beta_*-1/2)/2\), such that
\[
 S_{>H}(v):=\sum_{h>H}b_hg_P(v-\log h)
 \ll_\varepsilon X^{\beta_*-1/2+\varepsilon}(U/H)^\lambda.
\tag{1}
\]
At \(\beta_*=1/2\), the same sharp sum is \(O_\varepsilon(X^\varepsilon)\) for every \(\varepsilon>0\). The estimate holds pointwise in the original window and uses the unchanged coefficient and kernel. In particular, it confines the necessary companion signs to \(U<h\le Y^{u+\kappa}\), for arbitrarily small fixed \(\kappa>0\). In the exact expansion \(h=mn\), \(m>U\), this confines the surviving \(n\) to \(n\le H/U\).

## A sharp auxiliary Perron cutoff

Write \(G_U(s)=1-L(s)M_U(s)\), \(M_U(s)=\sum_{m\le U}\mu_L(m)m^{-s}\). The center \(E_P(t)\) uses the measure \(dM_{\mathrm{sp}}=\sum_{p\ {\rm split}}\log p\,\delta_p(dt)-dt/6\), restricted to \(t>P\). Write \(D_{{\rm sp},>P}(s)\) for the Mellin transform \(\int_{(P,\infty)} t^{-s}\,dM_{\mathrm{sp}}(t)\), initially on \(\Re s>1\). It is holomorphic strictly to the right of \(\beta_*\), with
\[
 D_{{\rm sp},>P}(a+it)\ll_{\varepsilon,a}P^\varepsilon(3+|t|)^\varepsilon
 \quad(a>\beta_*).
\]
Indeed it is one third of the Artin prime-log tail plus the abelian Dirichlet centering tails. The local log derivative and the twisted truncated prime prefix bound control the former strictly to the right of \(\beta_*\). The centered abelian tails continue strictly to the right of \(1/2\) with the exact principal reference subtracted. [Tail centering and twisted prefixes](https://github.com/Sodelin/Research-Commons/commit/4bfc76b31db848316d834a98b0b468381feee86a) · [Verified Dirichlet scope](https://math.mit.edu/~drew/grh/#what-was-verified)

Take the half-integer \(H'=\lfloor H\rfloor+1/2\), so \(h>H'\) is precisely \(h>H\) at integer \(h\). For \(\lambda>0\), truncated Perron writes
\[
 \mathbf1_{h>H}
 =-\frac1{2\pi i}\int_{-\lambda-iT}^{-\lambda+iT}
            \left(\frac{h}{H'}\right)^{-w}\frac{dw}{w}
 +O_\lambda\left[
  (h/H')^\lambda\min\left\{1,\frac1{T|\log(h/H')|}\right\}\right].
\tag{2}
\]
Take \(T=X^{10}\). The error contributes a negligible power to the original sharp sum. In fact the active support has \(h\le e^BX/P\ll_B X\), and \(|\log(h/H')|\gg_B X^{-1}\) there by half-integer separation. The coefficient is at most \(d_4(h)\), and the individual prime weight satisfies \(E_P(x/h)\ll_\varepsilon (x/h)^{\beta_*+\varepsilon}\) if active. Bounding the resulting finite error sum absolutely gives \(O(X^{3+\lambda+O(\varepsilon)}/T)\) before normalization. If \(H\) exceeds the active upper support the desired high sum is zero. The chosen \(\lambda\) may always be taken at most \(1/4\).

Insert (2) and the original kernel Mellin inversion. Before dividing by \(\sqrt x\), the resulting double integral, up to its sign, is
\[
 \frac1{(2\pi i)^2}\int_{(a_0)}\int_{-\lambda-iT}^{-\lambda+iT}
      x^sH_B(s)D_{{\rm sp},>P}(s)(H')^w
             G_U(s+w)\,\frac{dw}{w}\,ds,\qquad a_0>1+\lambda.
\tag{3}
\]
This starts in absolute convergence. Shift \(s\) to \(a=\beta_*+\delta\), with \(\delta>0\) small. For each \(w\), \(G_U\) is entire and the prime transform is holomorphic on the swept region. Horizontal integrals tend to zero for the finite \(w\) range by the quadratic decay of \(H_B\), ordinary degree-two convexity, and the subpower prime transform. For an off-line case choose \(\lambda=(\beta_*-1/2)/2\) and then \(\delta\) small, so \(\sigma=a-\lambda\) is strictly greater than \(1/2\). At \(\beta_*=1/2\), choose \(\lambda=\delta/2\), also putting \(\sigma>1/2\).

At the shifted arguments the twisted inverse bound gives
\[
 |M_U(\sigma+i(t+\tau))|
 \ll_\varepsilon U^{\lambda+\varepsilon}
                  (3+|t+\tau|)^\varepsilon .
\]
The fixed degree-two second moment on \(\sigma>1/2\) gives
\(\int_A^{2A}|L(\sigma+it)|^2dt\ll_\varepsilon A^{1+\varepsilon}\)
for \(A\ge2\), and the same bound for negative heights. This follows from the short-polynomial approximation in the degree-two density proof and the square summability of the polynomial on that fixed line. [Degree-two mean square](https://github.com/Sodelin/Research-Commons/commit/304b341ad0a4a99eb16055613bfafceb7c476850)

Use this to bound the truncated critical integral
\[
 \int_{-T}^T
 \frac{|L(\sigma+i(t+\tau))|(3+|t+\tau|)^\varepsilon}{1+|\tau|}\,d\tau
 \ll_\varepsilon
       (3+|t|)^{1/2+O(\varepsilon)}+T^{O(\varepsilon)}.
\tag{4}
\]
For dyadic \(|\tau|\le 2(3+|t|)\) of size \(A\), Cauchy–Schwarz and the mean square in a whole height block cost
\(O((3+|t|)^{1/2+O(\varepsilon)}A^{-1/2})\).
The same estimate covers \(|\tau|\le1\) with \(A=1\). For \(|\tau|\) larger than that boundary, the dyadic integral costs \(O(A^{O(\varepsilon)})\), since \(|t+\tau|\asymp A\). Sum the dyadic terms to get (4).

The factor \(|w|^{-1}\) is \(O_\lambda((1+|\tau|)^{-1})\), and \(|(H')^w|=(H')^{-\lambda}\). The constant \(1\) inside \(G_U\) only costs \(O_\lambda(\log T)\) on the \(w\) integral. The other term is bounded by (4) and the twisted inverse estimate. The outer \(t\) integral is absolutely convergent thanks to \(H_B(a+it)\ll (1+|t|)^{-2}\) and the prime transform, because the largest power from (4) is strictly below one as \(\varepsilon\) decreases. Absorb the arbitrary small powers of \(T,U,P\) and the choice of \(\delta\) into \(X^\varepsilon\). This gives (1). The same proof with \(H=U\) gives the total pointwise budget \(S(v)=O_\varepsilon(X^{\beta_*-1/2+\varepsilon})\).

## Consequence for the exact separated pairs

Keep the original subpower separation threshold \(H_0\), so \(\log H_0=o(\log X)\), and sum over exactly \(k-h>H_0\). Define \(\mathcal C_{\le H,>H_0}\) by additionally restricting both companions to \(h,k\le H\), without changing their coefficients or kernel arguments. The difference from full separated covariance is the integral of \(S^2-(S-S_{>H})^2\) minus the terms with \(\max(h,k)>H\) and \(|h-k|\le H_0\), including the diagonal. The first part is \(O(X^{2\beta_*-1-\kappa\lambda+o(1)+O(\varepsilon)})\) in an off-line case by (1). In the small-gap correction \(h,k\) are comparable and at least \(H/2\) for sufficiently large \(Y\). The individual prime envelope and divisor bound give the absolute estimate
\[
 O_\varepsilon\bigl(H_0 X^{2\beta_*-1+\varepsilon}
                 H^{1-2\beta_*+\varepsilon}\bigr)
\]
when \(\beta_*>1/2\), with the harmonic subpower variant when \(\beta_*=1/2\). This is also strictly below the necessary off-line exponent in the former case. The original covariance lower rate and its critical-line subpower converse therefore hold with \(\mathcal C_{\le H,>H_0}\) itself. No signed neighboring contribution has been allocated to a different support.

More generally, to test a zero-free threshold \(b>1/2\), one may use the polynomial separation \(H_0=X^\tau\) for any \(0<\tau\le u(2b-1)\) and the budget \(X^{2b-1+\varepsilon}\). The small-gap removal then still has a strict gap from \(2\beta_*-1\) whenever \(\beta_*>b\), and fits the threshold budget whenever \(\beta_*\le b\). The proof uses the same near-pair bound with the lower limit \(U\) when including all pairs, or \(H/2\) in the high-companion correction. It also uses the known positive window lower rate at the actual supremum. This yields an equivalent threshold criterion on the sharp band \(U<h,k\le H\) and separated exact pairs.

The remaining arithmetic input is the signed covariance bound on these pairs. The argument has removed the larger companions and left their original kernel and signs intact on the smaller band. These are hand arguments.

## The actual separated pairs may also be restricted to small gcd

Fix any \(\xi>0\) and set \(D_0=X^\xi\), with \(D_0>H_0\). The covariance of the sharp localized band may further be restricted to the exact pairs with \((h,k)\le D_0\). When \(\beta_*>1/2\), the discarded large-gcd covariance is smaller than \(X^{2\beta_*-1}\) by a fixed exponent. When \(\beta_*=1/2\) it is \(O_\varepsilon(X^\varepsilon)\). The restriction includes large gcd built from small primes, and does not require squarefree companions.

For each positive integer \(d\), define the actual one-divisor subseries
\[
 S_d(v)=\sum_{\substack{U<h\le H\\d\mid h}}b_hg_P(v-\log h).
\]
The sharp companion argument is uniform enough to give
\[
 |S_d(v)|\ll_\varepsilon X^{\beta_*-1/2+\varepsilon}d^{-\beta_*+\varepsilon}.
\tag{5}
\]
To prove this, for \(d\mid h\) separate the primes dividing \(d\) by writing
\[
 h=\ell r,\qquad
 \ell=\prod_{p\mid d}p^{v_p(h)},\qquad (r,d)=1,\qquad d\mid\ell .
\]
The exact convolution separation is
\[
 \beta_U(\ell r)
 =\sum_{m\mid\ell}\mu_L(m)a(\ell/m)\beta_{U/m}(r).
\]
Each term is already zero at \(r\le U/\ell\), since \(m\le\ell\) and \(\beta_{U/m}(r)=0\) for \(r\le U/m\). The remaining upper cutoff is \(r\le H/\ell\). If \(U/m\ge H/\ell\) the inner sum is zero. If \(U/m<1\), then \(\beta_{U/m}=\mathbf 1_{\{1\}}\) and the individual prime bound applies to that one norm.

In the other cases use the sharp companion argument for the output \(x/\ell\), cutoff \(U/m\), upper limit \(H/\ell\), and the coprimality restriction \((r,d)=1\). This last restriction changes the inner Dirichlet series to \(1-L^{(d)}(s)M^{(d)}_{U/m}(s)\), with the Euler factors of primes dividing \(d\) omitted both from \(L\) and from the inverse coefficients. On all the contour lines used in the sharp argument their products and inverses are \(O_{\sigma,\varepsilon}(d^\varepsilon)\). Indeed for real parts at least a fixed \(\sigma>1/2\), they are bounded by \(\prod_{p\mid d}(1-p^{-\sigma})^{-2}\), which is \(O_{\sigma,\varepsilon}(d^\varepsilon)\). This preserves both the zero-free reciprocal prefix estimate and the degree-two mean square, with at most an arbitrary small power of \(d\). The parameters \(x/\ell,P,U/m,H/\ell\) are all at most \(O_B(X)\), and \(x/\ell\) is still a fixed positive power of \(X\) or larger. Thus the same Perron height \(X^{10}\) controls all endpoints.

Apply the bound at the lower cutoff \(U/m\) to obtain the total budget, subtract the tail above \(H/\ell\), and use \(H/\ell>U/m\). The bound on the inner normalized sum is \(O_\varepsilon(X^\varepsilon(x/\ell)^{\beta_*-1/2}d^\varepsilon)\). Including \(\ell^{-1/2}\) from the outer companion normalization changes this to \(O_\varepsilon(X^{\beta_*-1/2+\varepsilon}\ell^{-\beta_*}d^\varepsilon)\). Summing the factors from \(m\mid\ell\) costs at most \(d_4(\ell)\ll_\varepsilon\ell^\varepsilon\), and
\[
 \sum_{\substack{d\mid\ell\\p\mid\ell\ \Rightarrow\ p\mid d}}
           \ell^{-\beta_*+\varepsilon}
 \le d^{-\beta_*+\varepsilon}
       \prod_{p\mid d}(1-p^{-\beta_*+\varepsilon})^{-1}
 \ll_\varepsilon d^{-\beta_*+O(\varepsilon)}.
\]
This proves (5) after rescaling \(\varepsilon\).

Möbius-invert the exact large-gcd predicate using
\[
 \lambda(d)=\sum_{\substack{e\mid d\\e>D_0}}\mu(d/e),\qquad
 \sum_{d\mid g}\lambda(d)=\mathbf1_{g>D_0}.
\]
The weight is supported on \(d>D_0\), with \(|\lambda(d)|\le d_2(d)\). Thus the signed covariance over all ordered pairs with \((h,k)>D_0\), including the diagonal, is exactly
\[
 \sum_{d>D_0}\lambda(d)\int_{v_0}^V S_d(v)^2\,dv.
\]
By (5) its absolute value is
\[
 O_\varepsilon\left(
 X^{2\beta_*-1+\varepsilon}D_0^{1-2\beta_*+\varepsilon}
 \right)\qquad(\beta_*>1/2),
\]
and is subpower at \(\beta_*=1/2\) by the finite harmonic sum. The log-window length is absorbed in \(X^\varepsilon\). Because two distinct multiples of \(g>D_0\) differ by at least \(g>H_0\), the large-gcd contribution to the actual separated covariance differs from this formula only by its diagonal. The diagonal is already below the necessary off-line exponent, and subpower at the critical line. This proves the deletion of the large-gcd pairs on the precisely stated support.

## Exact removal of every noncoprime pair

The large-gcd cutoff can be replaced by \((h,k)=1\). The multiple-of-\(d\) projection loses the constant coefficient of \(G_U\) for every \(d>1\), leaving a full factor \(L^{(d)}\) that cancels the Artin poles of the prime logarithmic derivative.

Define the full divisibility lane
\[
 S^{\rm full}_d(v)
   =x^{-1/2}\sum_{\substack{h\ge1\\d\mid h}}\beta_U(h)E_P(x/h),
 \qquad x=e^v.
\]
Its active support is \(h\le e^Bx/P\). For \(d>1\), the generating series is
\[
 G_{U,d}(s)=\sum_{d\mid h}\beta_U(h)h^{-s}=-L^{(d)}(s)J_{U,d}(s),
\tag{6}
\]
where \(L^{(d)}=L\prod_{p\mid d}L_p^{-1}\) and
\[
 J_{U,d}(s)=
 \sum_{\substack{\ell\le U\\p\mid\ell\Rightarrow p\mid d}}
     \mu_L(\ell)\ell^{-s} M_{U/\ell}^{(d)}(s)
     \prod_{p\mid d}\sum_{j\ge (v_p(d)-v_p(\ell))_+}a(p^j)p^{-js}.
\tag{7}
\]
Use \(\beta_U=\mathbf1_{\{1\}}-\mu_{L,\le U}*a\). The condition \(d\mid h\) excludes the first term. Factor the inverse variable as \(m=\ell r\), with \(\ell\) supported on the primes dividing \(d\) and \(r\) coprime to \(d\). Factor the \(a\)-variable the same way. The conditions \(d\mid h\) apply only to the two parts supported on primes dividing \(d\), giving exactly the lower bounds in the local factors in (7). The complementary \(a\)-variable supplies \(L^{(d)}(s)\). These identities start on \(\Re s>1\), and the factors in (7) are holomorphic on every fixed positive real sub-half-plane.

On a fixed line \(\sigma=\Re s>1/2\), the twisted inverse prefix on \((r,d)=1\) satisfies
\[
 |M_W^{(d)}(\sigma+it)|
 \ll_{L,\sigma,\varepsilon}
 d^\varepsilon W^{(\beta_*-\sigma)_++\varepsilon}
 (3+|t|)^\varepsilon,\qquad W\ge1 .
\]
This follows by the original twisted Perron shift for \(1/L^{(d)}(z)=L(z)^{-1}\prod_{p\mid d}L_p(z)\), strictly to the right of \(\beta_*\). The extra Euler product is \(O(d^\varepsilon)\) uniformly there and the coefficients remain divisor-bounded. For \(N\ge0\) each local tail in (7) is bounded by \((N+1)p^{-N\sigma}(1-p^{-\sigma})^{-2}\), since \(|a(p^j)|\le j+1\). After multiplying by \(\ell^{-\sigma}\), the local power factors together equal \(\operatorname{lcm}(d,\ell)^{-\sigma}\le d^{-\sigma}\). Their remaining \(N+1\) factors cost at most \(d_2(d)\), and the Euler corrections cost \(d^\varepsilon\). Since the local inverse degree is at most two, there are at most \(3^{\omega(d)}\) choices of \(\ell\) with \(\mu_L(\ell)\ne0\), each with \(|\mu_L(\ell)|\le2^{\omega(d)}\). These losses are subpower in \(d\). Taking the auxiliary exponents sufficiently small gives
\[
 |J_{U,d}(\sigma+it)|\ll_{L,\sigma,\varepsilon}
 d^{-\sigma+\varepsilon}
 U^{(\beta_*-\sigma)_++\varepsilon}(3+|t|)^\varepsilon .
\tag{8}
\]

For \(P\) beyond the ramified primes, write
\[
 3D_{{\rm sp},>P}(s)=D^p_{>P}(s)+E_{{\rm ab},>P}(s)
\]
where \(E_{{\rm ab},>P}\) is the Mellin transform of the signed measure on \(t>P\) given by
\[
 \tfrac12\left(\sum_p(1+\chi(p))(\log p)\delta_p(dt)-dt\right).
\]
It is holomorphic on \(\Re s>1/2\), with
\(|E_{{\rm ab},>P}(\sigma+it)|\ll_{\sigma,\varepsilon}P^\varepsilon(3+|t|)^\varepsilon\)
on each fixed line there, by the twisted Dirichlet prime-tail estimate with the exact \(P\) reference. The principal residue is absent because its matching continuous tail has already been subtracted. In absolute convergence,
\[
 L(s)D^p_{>P}(s)=-L'(s)-L(s)Z(s)-L(s)B_P(s),
 \qquad B_P(s)=\sum_{p\le P}\Lambda_L(p)p^{-s},
\]
where the higher-prime-power series \(Z\) is absolutely convergent to the right of \(1/2\). Thus \(D_{{\rm sp},>P}L^{(d)}\) continues to \(\Re s>1/2\), including across every Artin prime-series pole there. The finite cutoff costs
\(|B_P(\sigma+it)|\ll_{\sigma,\varepsilon}P^{(\beta_*-\sigma)_++\varepsilon}(3+|t|)^\varepsilon\)
by the twisted Artin prefix. No prime range is changed. [Twisted Artin prefix](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd) · [Exact abelian tail](https://github.com/Sodelin/Research-Commons/commit/4bfc76b31db848316d834a98b0b468381feee86a)

Invert \(x^sH_B(s)D_{{\rm sp},>P}(s)G_{U,d}(s)\) and divide by \(\sqrt{x}\). Shift to a fixed \(\sigma=1/2+\delta\), \(\delta>0\). The cancellation, ordinary degree-two convexity for \(L,L'\), and (8) make the integral absolutely convergent against the quadratic decay of \(H_B\). The horizontal contours have the same decay, and the local inverse factors cost \(d^\varepsilon\). In particular this gives
\[
 O\!\left(x^{\sigma-1/2}d^{-\sigma+\varepsilon}
                (UP)^{(\beta_*-\sigma)_++\varepsilon}\right).
\]
Take \(\delta\) and the auxiliary exponents sufficiently small in terms of the final tolerance, using \(U,P\le X\). The result is
\[
 |S^{\rm full}_d(v)|
 \ll_\varepsilon X^{(u+\alpha)(\beta_*-1/2)+\varepsilon}
                 d^{-1/2+\varepsilon}\qquad(d>1).
\tag{9}
\]

For the sharp upper cutoff \(H\), the tail in the \(d\)-lane also has the uniform estimate
\[
 |S_{d,>H}(v)|\ll_\varepsilon
 X^{\beta_*-1/2+\varepsilon}(U/H)^\lambda
              d^{-\beta_*+\lambda+\varepsilon},
\tag{10}
\]
with \(\lambda=(\beta_*-1/2)/2\) for \(\beta_*>1/2\), and arbitrarily small fixed \(\lambda>0\) at \(\beta_*=1/2\). Use the exact factorization \(h=\ell r\) from (5), retaining \(r>H/\ell\). If \(H/\ell\ge U/m\ge1\), the sharp auxiliary cutoff with Euler primes omitted gives gain \((U\ell/(Hm))^\lambda\le(U\ell/H)^\lambda\). If \(H/\ell<U/m\), use the total bound since \(U\ell/H>1\). If \(U/m<1\), the inner sequence is supported at \(r=1\) and contributes only for \(\ell>H\), again with \(U\ell/H>1\). The output \(x/\ell\) is at least \(Pe^{-B}\) on active support. Include its \(\ell^{-1/2}\) normalization and sum \(\ell^{-\beta_*+\lambda+\varepsilon}\) over \(\ell\) supported on primes dividing \(d\) and divisible by \(d\). The local geometric sums give \(O(d^{-\beta_*+\lambda+O(\varepsilon)})\), since \(\beta_*-\lambda>0\). This proves (10).

The localized \(S_d\) of (5) is \(S_d^{\rm full}-S_{d,>H}\). In an off-line case, choose the auxiliary losses so that \(2(\beta_*-\lambda)-2\varepsilon>1\). Squaring (9) and (10), summing \(2\le d\le H\), and absorbing the window length into \(X^\varepsilon\) gives
\[
 \sum_{2\le d\le H}\int_{v_0}^V |S_d(v)|^2\,dv
 \ll_\varepsilon X^{(u+\alpha)(2\beta_*-1)+\varepsilon}
             +X^{2\beta_*-1-2\kappa\lambda+o(1)+\varepsilon}.
\tag{11}
\]
The factor \(\sum_{d\le H}d^{-1+2\varepsilon}\) from (9) is absorbed by rescaling the arbitrary final tolerance. At \(\beta_*=1/2\), first choose \(\lambda\) small relative to that tolerance. The corresponding square sum from (10) costs at most \(X^{2\lambda+O(\varepsilon)}\), and the entire expression is subpower.

Exactly \(\mathbf1_{(h,k)>1}=-\sum_{d\mid h,\,d\mid k,\,d>1}\mu(d)\). Thus the localized signed covariance of all ordered noncoprime pairs, including the diagonal, is \(-\sum_{d>1}\mu(d)\int S_d(v)^2\,dv\), bounded absolutely by (11). To recover the exact separated covariance, remove the terms with \(|h-k|\le H_0\) by the original absolute short-gap estimate, including the diagonal. They are below the off-line exponent by a fixed power for subpower \(H_0\), and subpower in the critical-line case. The threshold-\(b\) variant with \(H_0=X^\tau\), \(\tau\le u(2b-1)\), follows by the same comparison. The equivalent covariance criterion may therefore retain exactly
\[
 U<h<k\le H,\qquad k-h>H_0,\qquad (h,k)=1 .
\]
The kernel arguments, inverse coefficients, and strict endpoints all remain as in the original covariance. The required square-root estimate on this coprime separated band remains open.

## Removing logarithmically small prime divisors

The same covariance criterion may also impose \(P^-(h),P^-(k)>z\) for \(z=(\log X)^2\). The useful extra observation is that the two divisibility-lane bounds can retain a fixed power of \(d\) greater than \(1/2\).

For full \(S_d\) simply retain \(d^{-\sigma+\varepsilon}\) with the original fixed \(\sigma>1/2\) in the shifted integral preceding (9). For the sharp high-companion tail, use (3) with \(G_{U,d}(s+w)\) from (6) instead of \(G_U(s+w)\). Its factor \(L^{(d)}(s+w)\) obeys the same degree-two mean square as \(L\), up to the \(d^\varepsilon\) bound for the omitted local factors. The remaining \(J_{U,d}\) has bound (8) at \(\sigma=a-\lambda>1/2\), where \(a=\Re s>\beta_*\) and \(\Re w=-\lambda\). The integral bound (4) then gives, after rescaling the auxiliary errors,
\[
 |S_{d,>H}(v)|\ll_\varepsilon
 x^{a-1/2}H^{-\lambda}
 U^{(\beta_*-\sigma)_+} X^\varepsilon d^{-\sigma+\varepsilon}
 \qquad(d>1).
\]
Truncation errors are negligible uniformly for \(d\le H\) by the same height \(X^{10}\). In the off-line case choose \(a=\beta_*+\delta\) and \(\lambda=(\beta_*-1/2)/2\), then \(\delta\) small compared with \(\kappa\lambda\). For the full lane choose its fixed line just above \(1/2\), within the fixed exponent gap in (9). After decreasing the auxiliary errors there are \(\sigma_*>1/2\) and \(c>0\) such that the localized \(S_d\) is bounded by \(O(X^{\beta_*-1/2-c}d^{-\sigma_*})\) for every \(d>1\). At the critical line choose \(a=1/2+2\delta,\lambda=\delta\) and a similar small \(\delta\) for the full lane. For any final tolerance this gives \(O_\varepsilon(X^\varepsilon d^{-\sigma_\varepsilon})\) with some \(\sigma_\varepsilon>1/2\).

Put \(\mathfrak p_z=\prod_{p\le z}p\), and let \(\widetilde S_d\) be the localized \(d\)-lane restricted to \((h,\mathfrak p_z)=1\). Exact inclusion–exclusion gives
\[
 \widetilde S_1-S_1=\sum_{\substack{e\mid\mathfrak p_z\\e>1}}\mu(e)S_e .
\]
For \(d>1\), \(\widetilde S_d=0\) if \((d,\mathfrak p_z)>1\), and otherwise \(\widetilde S_d=\sum_{e\mid\mathfrak p_z}\mu(e)S_{de}\). For any fixed \(\sigma>1/2\),
\[
 \sum_{e\mid\mathfrak p_z}e^{-\sigma}
 =\prod_{p\le z}(1+p^{-\sigma})
 =X^{o(1)} ,
\]
since even the sum over all integers up to \(z\) costs \(O_\sigma(1+z^{\max(1-\sigma,0)}\log z)=o(\log X)\) in the logarithm of that product. Thus \(\widetilde S_1-S_1\) is smaller by a fixed exponent in an off-line case and subpower at the critical line, and each \(\widetilde S_d\) for \(d>1\) retains the \(d^{-\sigma}\) square summability after absorption of \(X^{o(1)}\). Applying the same noncoprime-pair identity to these new lanes and the existing absolute short-gap estimate proves the reduction. Both companion restrictions are exact and preserve the original signed weights. No additional assertion on the covariance of the remaining rough, coprime, separated pairs follows.
