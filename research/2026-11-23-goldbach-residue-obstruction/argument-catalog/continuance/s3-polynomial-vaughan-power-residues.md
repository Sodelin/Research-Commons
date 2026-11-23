# Exact square and cube references in the polynomial Artin window

Let \(\rho\) be the standard representation of a fixed \(S_3\) closure, let \(L(s)=L(s,\rho)\), and let \(\chi\) be the quadratic Dirichlet character of the resolvent. Denote by \(\beta_*=\sup\Re\rho_0\in[1/2,1]\) the actual zero supremum of the completed \(L\). We use the verified Dirichlet critical-line theorem for \(\zeta\) and \(L(s,\chi)\). There is no assumption on the zeros of \(L\) beyond its analytic continuation, functional equation and the definition of \(\beta_*\). [Verified Dirichlet scope](https://math.mit.edu/~drew/grh/#what-was-verified)

Use the original \(K_B(t)=e^{-B}(e^B/t-1)_+-(1/t-1)_+\) at \(B>0\), write \(\mathscr K_x(c)=\sum_n c(n)K_B(n/x)\), and put
\[
 H_B(s)=\frac{e^{(s-1)B}-1}{s(s-1)},\qquad
 M_U(s)=\sum_{m\le U}\mu_L(m)m^{-s},\qquad G_U(s)=1-L(s)M_U(s).
\]
The convolution coefficients of \(G_U\) are \(\beta_U=\mu_{L,>U}*a\), where \(a(n)\) and \(\mu_L(n)\) are the coefficients of \(L\) and \(1/L\). The original observable is \(C_{0,B}(x)=-\mathscr K_x(\Lambda_L)/4\), where \(\Lambda_L\) are the coefficients of \(-L'/L\). [Original normalization and Mellin kernel](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md)

The two explicit reference terms are
\[
 \mathcal R_2(x,U)=-\frac{x^{1/2}H_B(1/2)G_U(1/2)}8,\qquad
 \mathcal R_3(x,U)=-\frac{x^{1/3}H_B(1/3)G_U(1/3)}{12}.
\tag{1}
\]
Equivalently their scalar factors are \(-\tfrac12(1-e^{-B/2})x^{1/2}\) and \(-\tfrac38(1-e^{-2B/3})x^{1/3}\) multiplying \(G_U(1/2)\) and \(G_U(1/3)\), respectively. These terms use only fixed real \(L\)-values and finite reciprocal sums.

## The higher-power series and its local poles

For a virtual \(S_3\) character \(V\), write \(D_V(s)=-L'(s,V)/L(s,V)\) by linearity in \(V\), and \(D_V^{\rm ur}\) for the same derivative with the finitely many ramified rational factors removed. At an unramified prime with Frobenius \(g\), the \(j\)-th power coefficient of \(D^{\rm ur}_V(s)\), divided by \(\log p\), is \(V(g^j)\). Put \((\psi^k V)(g)=V(g^k)\). With the conjugacy classes in order identity, transposition, 3-cycle, \(\rho\) has values \((2,0,-1)\). Therefore
\[
 \psi^2\rho=\mathbf 1-\chi+\rho,\qquad
 \psi^3\rho=\mathbf 1+\chi.
\]
Here \(\chi\) also denotes the sign character of the group. For \(\Re s>1\), the prime-only series has the exact inversion
\[
 \sum_{p\ {\rm ur}}\rho(g_p)\log p\,p^{-s}
   =\sum_{k\ge1}\mu(k)D^{\rm ur}_{\psi^k\rho}(ks).
\tag{2}
\]
At each \(p^n\) the coefficient on the right is \(\rho(g_p^n)\log p\sum_{k\mid n}\mu(k)\); the inner sum is \(1\) at \(n=1\) and \(0\) otherwise. All sums converge absolutely in that half-plane. [Artin local factors and induction](https://doi.org/10.1007/BF02941010)

Set \(Z(s)=\sum_{p,k\ge2}\Lambda_L(p^k)p^{-ks}\). Since \(\mu(2)=\mu(3)=-1\) and \(\mu(4)=0\), (2) gives the continuation
\[
 Z(s)=D_{\mathbf 1}(2s)-D_\chi(2s)+D_\rho(2s)
       +D_{\mathbf 1}(3s)+D_\chi(3s)+E(s),
\tag{3}
\]
where \(D_{\mathbf 1}=-\zeta'/\zeta\). The remaining terms from \(k\ge5\) converge absolutely and are uniformly bounded on every closed half-plane \(\Re s\ge\sigma>1/5\). Indeed unramified \(|\rho(g_p^{kj})|\le2\), and the majorant is \(2\sum_p\sum_{k\ge5}\sum_{j\ge1}(\log p)p^{-kj\sigma}\). The finite changes from ramification remain holomorphic and bounded for \(\Re s\ge\sigma>0\), by the unit-disc root bounds at those primes. Thus \(E\) is analytic on \(\Re s>1/5\).

By the Dirichlet input, the only singularities of (3) on \(\Re s>\beta_*/2\) are the principal poles at \(1/2\) and \(1/3\) when they lie in that region. Their residues are respectively \(1/2\) and \(1/3\), by the changes of variable in \(D_{\mathbf 1}(2s)\) and \(D_{\mathbf 1}(3s)\). The scaled nontrivial Artin poles are at \(s=\rho_0/2\), to the left of the open region, and the scaled Dirichlet zeros have real part \(1/4\) or \(1/6\). In particular if \(L\) has a real zero at \(2/3\), the local residue of the *full* series at \(1/3\) is \(1/3-m/2\) with \(m\) its multiplicity. Formula (1) retains the two principal zeta contributions, and makes no assertion that \(1/3\) is a pole in the contour region when \(\beta_*/2\ge1/3\).

## Power contribution with two explicit references

Write \(\Lambda_{\rm pow}\) for \(\Lambda_L\) restricted to \(p^k\) with \(k\ge2\). Let \(0\le u<1\) and \(1\le U\le x^u\). The Mellin integrand of \(\mathscr K_x(\beta_U*\Lambda_{\rm pow})\) is \(x^sH_B(s)G_U(s)Z(s)\). It starts in absolute convergence at \(2\). Choose a fixed \(\sigma>\beta_*/2\) sufficiently close to \(\beta_*/2\) and distinct from \(1/3,1/2\). The local zero expansion and (3) bound the logarithmic derivatives on this line by \(O_{L,\sigma}(\log(3+|t|))\), since all scaled zeros are horizontally separated from it. The same bounds apply along high horizontal pieces, which avoid the two fixed real poles. The original \(H_B\) decays as \(O_B((1+|t|)^{-2})\); fixed degree-two convexity gives \(|L(\sigma+it)|\ll_\nu(3+|t|)^{1-\sigma+\nu}\). The twisted sharp-prefix bound in the polynomial Vaughan argument gives
\[
 |M_U(\sigma+it)|\ll_{L,\sigma,\nu}
 U^{(\beta_*-\sigma)_++\nu}(3+|t|)^\nu.
\]
Together these bounds make the new vertical integral absolutely convergent, at cost \(O_\epsilon(x^{\beta_*(1+u)/2+\epsilon})\) by taking \(\sigma-\beta_*/2\) and \(\nu\) sufficiently small. The horizontal integrals vanish by the same decay and the height-independent bound for a fixed finite \(M_U\) on bounded real strips. [Local zero expansion, Iwaniec–Kowalski, Proposition 5.7](https://doi.org/10.1090/coll/053)

For each \(r=1/2,1/3\) crossed, the arithmetic Mellin sum gains the residue \(r x^r H_B(r)G_U(r)\). For a reference with \(r\le\sigma\), its absolute value is at most \(O_\nu(x^r U^{\beta_*-r+\nu})\), by the same bound for \(M_U\) at that real argument. This is within the vertical error because \(r+u(\beta_*-r)\) is increasing in \(r\) and \(\sigma\) is chosen just above \(\beta_*/2\). In particular the comparison also holds at \(\beta_*=1\), where the contour stays above \(1/2\). Multiplying by \(-1/4\) gives the uniform formula
\[
 -\frac14\mathscr K_x(\beta_U*\Lambda_{\rm pow})
 =\mathcal R_2(x,U)+\mathcal R_3(x,U)
    +O_{L,B,u,\epsilon}(x^{\beta_*(1+u)/2+\epsilon}).
\tag{4}
\]
If only the square reference is desired, stop instead at \(r_2=\max\{1/3,\beta_*/2\}\) from the right, and get
\[
 -\frac14\mathscr K_x(\beta_U*\Lambda_{\rm pow})
 =\mathcal R_2(x,U)
    +O_{L,B,u,\epsilon}(x^{r_2+u(\beta_*-r_2)+\epsilon}).
\tag{5}
\]

The square reference has a sharp pointwise exponent when \(\beta_*>1/2\) and \(L(1/2)\ne0\). For \(\Re s>1/2\), integrate the sharp reciprocal prefix term by term to get
\[
 \int_1^\infty G_U(1/2)U^{-s-1}\,dU
   =\frac{1-L(1/2)/L(s+1/2)}s .
\tag{5a}
\]
Each reciprocal coefficient on the left is included exactly for \(U\ge m\). A bound \(G_U(1/2)=O(U^{\beta_*-1/2-\epsilon})\) for any \(\epsilon>0\) would make the integral holomorphic on a half-plane containing a pole at \(s=\rho_0-1/2\), from a zero with \(\Re\rho_0>\max\{1/2,\beta_*-\epsilon\}\). Its pole cannot cancel because \(L(1/2)\ne0\) and \(s\ne0\). This contradicts (5a). The upper bound with \(+\epsilon\) in place of \(-\epsilon\) follows from the twisted reciprocal prefix estimate at \(s=1/2\). Thus the infimum of all absolute upper exponents for \(\mathcal R_2(x,\lfloor x^u\rfloor)\), for \(0<u<1\), is \(1/2+u(\beta_*-1/2)\). The cube term has a strictly smaller exponent, by \((1-u)/6\), and cannot remove this obstruction. If \(L(1/2)=0\), then \(G_U(1/2)=1\) exactly, so the square reference has order \(\sqrt{x}\). In particular, when \(\beta_*<1\), improving the pointwise power-component exponent from the old bound to (4) generally requires retaining the square reference.

## Effect on the original remainder

For \(0<\alpha<1-u\), take \(P=x^\alpha\) and define the exact retained prime sum
\[
 R_{u,\alpha}(x)=-\frac14\!\sum_{\substack{p>P,\ h>U\\ph\le e^Bx}}
 \Lambda_L(p)\beta_U(h)K_B(ph/x).
\]
The argument using \(L(s)M_U(s)\) and the finite prime prefix shows that the other discarded terms, namely \(\mu_{L,\le U}*(a\log)\) and the primes \(p\le P\) in \(\beta_U*\Lambda_L\), cost \(O_\epsilon(x^{\beta_*(u+\alpha)+\epsilon})\). Combining that polynomial argument with (4) yields
\[
 C_{0,B}(x)-\mathcal R_2(x,U)-\mathcal R_3(x,U)
 =R_{u,\alpha}(x)
 +O_{L,B,u,\alpha,\epsilon}
 \!\left(x^{\beta_*\max\{u+\alpha,(1+u)/2\}+\epsilon}\right).
\tag{6}
\]
The same result holds with \(U=\lfloor Y^u\rfloor\) and \(P=Y^\alpha\) fixed on windows starting at \(Y\). When \(\beta_*=1/2\), the residual in (6) has a fixed power saving over square-root order. Without retaining the references, the square term alone can cost \(O_\epsilon(x^{1/2+u(\beta_*-1/2)+\epsilon})\). Both references are within the critical-line budget, and are strictly below the off-line growth rate if \(\beta_*>1/2\).

When the exact complementary-factor support \(h<U^2\) is also imposed, \(2u+\alpha>1\). Among \(u+\alpha<1\) and \(2u+\alpha>1\), the infimum of \(\max\{u+\alpha,(1+u)/2\}\) is \(2/3\), approached with \(u,\alpha\) tending to \(1/3\) from the admissible side. Indeed for \(u\le1/3\), \(u+\alpha>1-u\ge2/3\); for \(u>1/3\), \((1+u)/2>2/3\). In the tighter balanced regime \(u=\alpha=1/2-\eta\), \(0<\eta<1/6\), the finite small-prime exponent \(u+\alpha=1-2\eta\) already dominates the improved power exponent \(3/4-\eta/2\).

Equation (6) applies to the raw signed prime remainder. An additional comparison to a completely split prime count using Dirichlet centering has its own error budget. The residues and comparisons here are hand arguments. The surviving signed upper-window estimate remains open, with no new Lean verification or numerical check.
