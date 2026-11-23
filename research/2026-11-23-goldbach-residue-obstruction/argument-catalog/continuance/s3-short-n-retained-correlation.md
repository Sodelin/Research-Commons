# Short-coefficient localization of the retained Artin correlation

Fix a standard \(S_3\) factor \(L(s)=\sum_n a(n)n^{-s}\), with reciprocal coefficients \(\mu_L\) and logarithmic derivative coefficients \(\Lambda_L\) for \(-L'/L\). Write \(\beta_*=\sup_\rho\Re\rho\in[1/2,1]\) for its actual completed zero supremum. Let \(d\) be a proved exponent for
\[
 \mathcal A(t)=\sum_{n\le t}a(n)=O_L(t^d),\qquad t\ge1.
\tag{1}
\]
One can use \(d=1/2\) by the quadratic ray-class count for every fixed \(S_3\) test here, or \(d=1/3\) for the conductor-23 example by smoothing its ideal-class lattice disks. [Quadratic ray-class count](https://github.com/Sodelin/Research-Commons/commit/1dcdd242401023541592d0126a999ae6cb43c8c5)

Use \(K_B(t)=e^{-B}(e^B/t-1)_+-(1/t-1)_+\) and \(H_B(s)=(e^{(s-1)B}-1)/(s(s-1))\) with fixed \(B>0\). The retained polynomial-cutoff correlation is
\[
 R_{U,P}(x)=-\frac14\sum_{\substack{p>P,\ m>U,\ n\ge1\\pmn\le e^Bx}}
    \Lambda_L(p)\mu_L(m)a(n)K_B(pmn/x).
\tag{2}
\]
Here \(P=x^\alpha,\ U=\lfloor x^u\rfloor\) with \(u,\alpha>0,\ u+\alpha<1\), or these cutoffs can be kept fixed at \(Y^\alpha,\lfloor Y^u\rfloor\) on a window starting at \(Y\le x\). We denote restriction to \(n>N\) or \(n\le N\) by \(R_{U,P}^{>N}\) or \(R_{U,P}^{\le N}\). [Polynomial cutoff and exact signed kernel](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd)

## A power-saving comparison without a top-line assumption

For every fixed \(0<\nu<1-u-\alpha\), the exact tail on the same support obeys
\[
 R_{U,P}^{>x^\nu}(x)
 \ll_{L,B,u,\alpha,\nu,\epsilon}
 x^{\beta_*-\nu(\beta_*-d)+\epsilon}.
\tag{3}
\]
In an off-line case this exponent is strictly below \(\beta_*\) when \(\epsilon\) is small. In the critical-line case it is at most square-root subpower cost. In the conductor-23 example \(d=1/3\) gives a fixed power saving even in the critical-line case. Thus just \(n\le x^\nu\), for any chosen fixed positive \(\nu\), already preserves the one-sided upper-window test on the prior detectable log windows. The bound is expressed in terms of the actual zero supremum and assumes neither its attainment nor a gap.

To prove (3), put
\[
 F_N(s)=\sum_{n\le N}a(n)n^{-s},\quad
 M_U(s)=\sum_{m\le U}\mu_L(m)m^{-s},\quad
 B_P(s)=\sum_{p\le P}\Lambda_L(p)p^{-s},\quad
 D_p(s)=\sum_p\Lambda_L(p)p^{-s}.
\]
On \(\Re s>1\) the Mellin integrand of the exact sum \(R_{U,P}^{>N}\), before the factor \(-1/4\), is
\[
 x^sH_B(s)
    [D_p(s)-B_P(s)] [L(s)^{-1}-M_U(s)] [L(s)-F_N(s)] .
\tag{4}
\]
The two first brackets are analytic on \(\Re s>\beta_*\). For \(D_p\), subtract the absolutely convergent prime-power series on \(\Re s>1/2\) from \(-L'/L\). On a fixed line \(\sigma>\beta_*\), take \(\sigma<1+d\) and use the polynomial-cutoff twisted Perron estimates to bound these brackets by
\[
 O_{\sigma,\epsilon}\!\left(P^\epsilon(3+|t|)^\epsilon\right),
 \qquad
 O_{\sigma,\epsilon}\!\left(U^\epsilon(3+|t|)^\epsilon\right),
\]
respectively. The estimates for the complete series use the local zero expansion for \(L'/L\) and subpower growth of \(1/L\) in its zero-free half-plane. The same bounds or bounds for fixed finite polynomials hold uniformly along the horizontal parts of the contour shift from \(2\). Since \(H_B\) decays quadratically and fixed degree-two convexity has exponent strictly less than \(1\) on this strip, those parts vanish. No pole is crossed. [Twisted Perron estimates](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd)

On this line the last bracket has two independent estimates. Abel summation of (1) gives
\[
 |L(s)-F_N(s)|\ll_{L,\sigma} N^{d-\sigma}(1+|t|),
\tag{5}
\]
because this Dirichlet tail converges on \(\Re s>d\). The degree-two convexity bound and \(|a(n)|\le d_2(n)\) also give
\[
 |L(s)-F_N(s)|\ll_\epsilon
       (3+|t|)^{(1-\sigma)_++\epsilon}
        +N^{(1-\sigma)_++\epsilon}.
\tag{6}
\]
Split the vertical integral (4) at \(|t|=N\). Below \(N\), (5) and the \(H_B\) decay cost \(O_\epsilon(N^{d-\sigma+O(\epsilon)})\), since the remaining integral is at most a small power times a logarithm. Above \(N\), (6) gives \(O_\epsilon(N^{-\min(\sigma,1)+O(\epsilon)})\), which is within the same bound since \(\sigma<1+d\). Restoring the \(x^s\) and prefix factors proves
\[
 R_{U,P}^{>N}(x)
 \ll_{\sigma,\epsilon} x^\sigma (PU)^\epsilon N^{d-\sigma+O(\epsilon)} .
\]
For \(N=\lfloor x^\nu\rfloor\), choose \(\sigma>\beta_*\) sufficiently close to \(\beta_*\) and then take the internal epsilons small. This proves (3), also when \(\beta_*=1\) by taking \(\sigma>1\).

The same comparison holds for the exact centered split-prime variant under the verified Dirichlet input. On the retained \(p\)-support, the centered split-prime transform is
\[
 \frac13[D_p(s)-B_P(s)]+\frac16 E_{1,P}(s)+\frac16 E_{\chi,P}(s),
\]
where \(E_{\xi,P}\) are the centered prime-tail transforms of the two Dirichlet characters. On \(\sigma>\beta_*\) they have the same \(P^\epsilon(3+|t|)^\epsilon\) bound and have no poles. The inverse and \(n\)-tail factors in (4) remain exactly the same. This comparison uses the continuous Dirichlet reference on \(t>P\) and does not change the kernel. [Centered Dirichlet-tail transforms](https://github.com/Sodelin/Research-Commons/commit/4bfc76b31db848316d834a98b0b468381feee86a)

In the balanced case \(P=x^\lambda,\ U=\lfloor x^\lambda\rfloor\), \(1/3<\lambda<1/2\), the coprime restriction \((p,m)=1\) can be kept after the \(n\)-truncation. All collisions of the full sum collapse to its \(O(\sqrt x)\) diagonal by \(m=pr\) and \(\mu_L*a=\mathbf1_{\{1\}}\). For the removed \(n>N\) part of a collision, the same Mellin proof applies with prime-plus-inverse brackets replaced by \(\sum_{p>P}a(p)^2(\log p)p^{-2s}\) and \(1/L(s)\). On \(\sigma>\beta_*\) the first factor is absolutely bounded by \(O(P^{1-2\sigma})\). Thus the truncated collision differs from the diagonal by this additional tail, of order
\[
 O_\epsilon\!\left(x^{\beta_*+\lambda(1-2\beta_*)-\nu(\beta_*-d)+\epsilon}\right)
\]
for \(N=x^\nu\). [Exact collision collapse](https://github.com/Sodelin/Research-Commons/commit/ac3b84bf9f56e275a3fd7b8de3ffabdd6cbc65ee)

## The exact cancellation mechanism if a finite top line is isolated

This subsection assumes a finite nonempty set \(\mathcal Z\) of zeros on \(\Re s=\beta=\beta_*>1/2\), with all remaining zeros strictly below it by a fixed gap. Normalize \(A=x^\lambda\), \(P=A\), \(U=\lfloor A\rfloor\) with \(1/3<\lambda<1/2\). Write \(k_\rho\) for the multiplicity of \(\rho\in\mathcal Z\),
\(c_\rho=\lim_{s\to\rho}L(s)/(s-\rho)^{k_\rho}\), and \(k=\max k_\rho\). The prime and reciprocal prefix formulas from the isolated top-line calculation are, for some fixed \(\delta>0\),
\[
 \sum_{p\le t}\Lambda_L(p)=-\sum_{\rho\in\mathcal Z}\frac{k_\rho}{\rho}t^\rho+
              O(t^{\beta-\delta}),\qquad
 \sum_{m\le t}\mu_L(m)=\sum_{\rho\in\mathcal Z}t^\rho Q_\rho(\log t)
                 +O(t^{\beta-\delta}),
\tag{7}
\]
where \(Q_\rho\) has degree \(k_\rho-1\) and leading coefficient \(1/(c_\rho\rho(k_\rho-1)!)\). The power \(\delta\) may be chosen smaller than both the zero gap and \(\beta-1/2\). Define \(V_\rho(v)=\rho Q_\rho(v)+Q_\rho'(v)\), the differentiated reciprocal density polynomial. [Isolated top-line prefix proof](https://github.com/Sodelin/Research-Commons/commit/ac3b84bf9f56e275a3fd7b8de3ffabdd6cbc65ee)

For \(1\le N\le x/A^2\), apply the two-dimensional mixed-variation estimate on each clipped dyadic \(p,m\) rectangle for each \(n\le N\). In (7), replacing either prefix error by its bound gains \(A^{-\delta}\) since both variables exceed \(A\); the rectangles satisfy \(pm\ll_B x/n\). Summing over \(n\le N\) gives total error
\[
 O_\epsilon\!\left(x^\beta A^{-\delta}N^{1-\beta+\epsilon}(\log x)^{k+2}\right).
\tag{8}
\]
Indeed before the \(n\)-sum the error is \(O((x/n)^\beta A^{-\delta}(\log x)^{k+2})\), and \(|a(n)|\le d_2(n)\). The estimate uses bounded mixed variation of \(K_B(e^{v+w-\log(x/n)})\), so no extra smoothing of the original kernel is needed.

In the main term with prime zero \(\rho_i\) and reciprocal zero \(\rho_j\), set \(r=pmn/x\), \(v=\log m\), and \(V_0=\lambda\log x\). The exact integration is
\[
 \frac{k_{\rho_i}}4 x^{\rho_i}
  \sum_{n\le N} a(n)n^{-\rho_i}
   \int_{A^2 n/x}^{e^B} K_B(r)r^{\rho_i-1}
    \int_{V_0}^{(1-\lambda)\log x+\log r-\log n}
        e^{(\rho_j-\rho_i)v} V_{\rho_j}(v)\,dv\,dr .
\tag{9}
\]
The sign comes from the negative prime density in (7) and the \(-1/4\) in (2). Extend the lower \(r\)-limit to zero. In the inserted part \(K_B\) is constant, since \(A^2n/x\le1\). With \(r=(A^2n/x)w,\ v=V_0+z\), this inserted integral is a factor independent of \(n\), of size \(O(A^{2\beta}(\log x)^k)\), times \(a(n)\). The factor contains an integral over \(0<w<1,\ 0>z>\log w\), whose fixed log moments converge. Therefore (1) bounds the signed extension by
\[
 O(A^{2\beta}N^d(\log x)^k).
\tag{10}
\]

For \(\rho_i=\rho_j=\rho\), let \(S_\rho\) be an antiderivative of \(V_\rho\), of degree \(k_\rho\) and leading coefficient \(1/(c_\rho k_\rho!)\). The \(n\)-dependence after the extension in (9) is the exact polynomial in the truncated Dirichlet moments
\[
 \sum_{j=0}^{k_\rho}\frac{S_\rho^{(j)}(W)}{j!}F_N^{(j)}(\rho)
             -S_\rho(V_0)F_N(\rho),
 \qquad W=(1-\lambda)\log x+\log r .
\tag{11}
\]
For \(\rho_i\ne\rho_j\), integrate the inner exponential in (9) exactly. There is a polynomial \(S_{ij}\) of degree \(k_{\rho_j}-1\) solving
\(S_{ij}'+(\rho_j-\rho_i)S_{ij}=V_{\rho_j}\).
The upper endpoint has moments \(F_N^{(j)}(\rho_j)\) for \(j\le k_{\rho_j}-1\) and factor \(x^{\lambda\rho_i+(1-\lambda)\rho_j}r^{\rho_j-1}\). The lower endpoint has only \(F_N(\rho_i)\) and factor \(x^{(1-\lambda)\rho_i+\lambda\rho_j}r^{\rho_i-1}\). Both have modulus \(x^\beta r^{\beta-1}\), apart from the finite polynomials in the displayed log variables.

Now (1) gives, for each relevant moment,
\[
 F_N^{(j)}(\rho)=L^{(j)}(\rho)
                    +O(N^{d-\beta}(1+\log N)^j).
\]
After integration in \(r\) the combined replacement error is \(O(x^\beta N^{d-\beta}(\log x)^k)\), since \(\log N\ll\log x\) and fixed log moments of \(r^{\beta-1}K_B(r)\) are integrable. All off-diagonal terms vanish under this replacement because they involve only derivatives below the relevant multiplicity. In (11) the same is true for every term except \(j=k_\rho\). Its coefficient is \(1/(c_\rho k_\rho!)\), and \(L^{(k_\rho)}(\rho)=k_\rho!c_\rho\) makes it exactly \(1\). Consequently the moment calculation yields
\[
 R_{U,P}^{\le N}(x)
 =\frac14\sum_{\rho\in\mathcal Z} k_\rho H_B(\rho)x^\rho+
 O_\epsilon\!\left(
   x^\beta A^{-\delta}N^{1-\beta+\epsilon}(\log x)^{k+2}
  +A^{2\beta}N^d(\log x)^k
  +x^\beta N^{d-\beta}(\log x)^k\right).
\tag{12}
\]
The leading term is exactly the original top-line pole contribution. Thus \(N=(\log x)^C\) with \(C>k/(\beta-d)\), or \(N=\exp((\log\log x)^2)\), recovers it up to \(o(x^\beta)\). For \(N=x^\nu\), any sufficiently small fixed positive \(\nu<\min\{1-2\lambda,\lambda\delta/(1-\beta)\}\) gives a fixed power saving in (12). The centered version has the same leading term. Indeed the Dirichlet comparison by roots of unity or the dyadic mixed-variation proof gives error \(O_\epsilon(x^\beta A^{-(\beta-1/2)}N^{1-\beta+\epsilon})\), strictly lower for these cutoffs.

This finite-top calculation identifies the cancellation of the higher logarithmic powers seen in the \(n=1\) band. The terms with \(2\le n\le N\) cancel them through the vanishing Dirichlet moments, leaving precisely the simple log-derivative zero signal. The truncation at any fixed positive power in (3) does not require the top-line hypothesis. These are hand proofs, with no numerical checks or new Lean verification. The surviving short-\(n\), signed prime–inverse correlation still requires its upper-window bound.
