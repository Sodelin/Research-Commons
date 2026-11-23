# Dirichlet centering when the Artin inverse cutoff is polynomial

For a fixed standard \(S_3\) Artin factor, the Dirichlet part of its centered split-prime criterion can be removed on the **same** prime and inverse-variable support even when the inverse cutoff is a fixed power of the window start. The error is controlled by the actual rightmost-zero supremum of this factor. In an off-line case it grows strictly more slowly than the signal of the original upper window. With no off-line zero it is at square-root scale. [Original split-prime normalization](https://github.com/Sodelin/Research-Commons/commit/1dcdd242401023541592d0126a999ae6cb43c8c5) · [Verified Dirichlet scope](https://math.mit.edu/~drew/grh/#what-was-verified)

Let \(L\) be the degree-two Artin factor, \(U=\lfloor Y^u\rfloor\) with \(0<u<1\) on windows starting at \(Y\), and \(P=x^\alpha\) with \(0<\alpha<1-u\). Use the original undamped kernel \(K_B\), weight
\[
 W(x,t)=\sum_{h>U}\beta_U(h)K_B(ht/x),\qquad
 \beta_U=\mu_{L,>U}*a,
\]
and \(M_U(s)=\sum_{m\le U}\mu_L(m)m^{-s}\). Then \(\sum_h\beta_U(h)h^{-s}=1-L(s)M_U(s)\) in absolute convergence. The polynomial-cutoff reduction gives the equivalent upper-window test with
\[
 R_{u,\alpha}(x)=-\tfrac14\sum_{p>P}\Lambda_L(p)W(x,p).
\]
In this reduction all discarded terms have a fixed smaller power than \(x^{\beta_*}\) if the actual zero supremum satisfies \(\beta_*>1/2\). When \(\beta_*=1/2\) they cost \(O_\epsilon(x^{1/2+\epsilon})\). [Polynomial-cutoff proof](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd)

## A twisted abelian prefix estimate

Use \(\xi=1\) (principal of modulus one) or the quadratic character \(\chi\) of the resolvent. Let \(\delta_\xi=1\) for the first and \(0\) for the second. Let \(D_\xi(s)=\sum_p\xi(p)(\log p)p^{-s}\) in \(\Re s>1\). Under the verified Dirichlet GRH, subtract the absolutely convergent higher powers from the Dirichlet logarithmic derivative. This continues \(D_\xi\) meromorphically to \(\Re s>1/2\), with only \(\delta_\xi/(s-1)\) as its polar part. On a fixed strip strictly to the right of \(1/2\), away from the pole, it is \(O_\xi(\log(3+|\Im s|))\) by the local zero expansion.

Fix \(1/2<\sigma<1\). For any \(\varepsilon>0\), uniformly in \(P\ge2\) and \(t\in\mathbb R\), the exact finite prefix at \(s=\sigma+it\) obeys
\[
 \sum_{p\le P}\xi(p)(\log p)p^{-s}
     =\delta_\xi\frac{P^{1-s}}{1-s}
          +O_{\xi,\sigma,\varepsilon}\bigl(P^\varepsilon(3+|t|)^\varepsilon\bigr).
 \tag{1}
\]
To see this, first use the half-integer \(P'=\lfloor P\rfloor+1/2\). In the Perron integral for the prefix, start with \(\Re w=1-\sigma+1/\log P'\) and take height \((P')^2(3+|t|)\). The coefficients in the shifted Dirichlet series have absolute size at most \(n^{-\sigma}\log n\). The usual Perron error, using \(|n-P'|\ge1/2\) and dyadic shells, is \(O_\sigma((P')^{1-\sigma}(\log(3P'))^C/((P')^2(3+|t|)))\). Shift to any fixed \(0<\omega<\min(\varepsilon/4,1-\sigma)\). The only possible residue is at \(w=1-s\), inside the height range. Its contribution is \(\delta_\xi(P')^{1-s}/(1-s)\). The new line costs \(O((P')^\omega(\log(3P'|t|+3P'))^C)\), and the horizontal pieces are smaller. Replacing \(P'\) by \(P\) affects the principal main term by \(O_\sigma(P^{-\sigma})\) by its antiderivative formula, uniformly in \(t\). This proves (1). [Local logarithmic derivative estimate, Iwaniec–Kowalski, Proposition 5.7](https://doi.org/10.1090/coll/053)

## Centering on the unchanged retained support

Set
\[
 E_{\xi,P}(s)=D_\xi(s)-\sum_{p\le P}\xi(p)(\log p)p^{-s}
                  -\delta_\xi \frac{P^{1-s}}{s-1}.
\]
The subtraction removes the pole, so \(E_{\xi,P}\) is holomorphic to the right of \(1/2\). At each fixed \(\sigma\) in \((1/2,1)\), (1) bounds it by \(O_{\xi,\sigma,\varepsilon}(P^\varepsilon(3+|t|)^\varepsilon)\). The second and third terms cancel each other's pole-shaped expression from (1) on that line. The weighted difference
\[
 \sum_{p>P}\xi(p)(\log p)W(x,p)
             -\delta_\xi\int_P^{e^Bx}W(x,t)\,dt
\]
is the inverse Mellin integral of
\[
 x^s H_B(s)(1-L(s)M_U(s))E_{\xi,P}(s),\qquad
 H_B(s)=\frac{e^{(s-1)B}-1}{s(s-1)}.
\]
Indeed on \(\Re s>1\) the prime terms can be opened absolutely, and the integral of \(t^{-s}\) over \([P,\infty)\) is \(P^{1-s}/(s-1)\). The weight on the arithmetic side vanishes past \(e^Bx\), so this is its exact reference integral.

The polynomial inverse argument gives \(M_U(\sigma+it)\ll_\varepsilon U^{(\beta_*-\sigma)_++\varepsilon}(3+|t|)^\varepsilon\). It uses \(1/L\) only in its actual zero-free half-plane. Fixed degree-two convexity gives \(L(\sigma+it)\ll_\varepsilon(3+|t|)^{1-\sigma+\varepsilon}\). Shift to a fixed \(\sigma\in(1/2,1)\) and use the \(t^{-2}\) decay of \(H_B\). The integral is absolutely convergent. The horizontal pieces vanish by the same convexity bound, the local log derivative, and fixed finite Dirichlet polynomials at each \(x,U,P\). Consequently the difference is
\[
 O_{L,B,\epsilon}\!\left(x^{1/2+\epsilon}U^{(\beta_*-1/2)_+}\right).
 \tag{2}
\]
Here take \(\sigma\) just above \(1/2\) and absorb the arbitrary powers of \(U\) and \(P\) using \(U,P\le x\). The \(\chi\) term has no reference main term.

For all sufficiently late windows, the primes \(p>P\) are unramified. Their exact standard trace is \(3\mathbf1_{\rm split}-(1+\chi)/2\). Therefore the conditioned comparison with the original signed sum is
\[
 R_{u,\alpha}(x)=
 -\frac34\left[
 \sum_{\substack{p>P\\p\ {\rm splits\ completely}}}(\log p)W(x,p)
       -\frac16\int_P^{e^Bx}W(x,t)\,dt\right]
 +O_{L,B,\epsilon}\!\left(x^{1/2+\epsilon}U^{(\beta_*-1/2)_+}\right).
 \tag{3}
\]
If \(\beta_*>1/2\) and \(U\le x^u\), the error has exponent at most \(1/2+u(\beta_*-1/2)+\epsilon<\beta_*\) for small enough \(\epsilon\). This preserves the off-line lower rate on the original late log windows. The critical-line case gives square-root scale. Thus (3) transfers the one-sided split-prime criterion to the new polynomially truncated inverse support with its exact reference. The arithmetic upper estimate for the retained split-prime sum remains open. These are hand arguments, with the verified Dirichlet critical-line theorem as input and no new Lean verification.
