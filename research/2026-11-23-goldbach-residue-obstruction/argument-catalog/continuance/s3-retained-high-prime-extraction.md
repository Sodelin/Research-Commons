# Extracting a prime pair from the balanced retained \(S_3\) sum

Let \(L(s)\) be the standard factor of a fixed \(S_3\) closure. Write \(a(n)\) for its coefficients, \(\mu_L(n)\) for the coefficients of \(1/L\), and \(\Lambda_L(n)\) for the coefficients of \(-L'/L\). Let \(\beta_*=\sup\Re\rho\) be its actual completed zero supremum. Fix
\[
 \frac13<u=\frac12-\eta<\frac12,\qquad
 \max\{(1-u)/2,1-2u\}<v<u,
\]
and put \(U=\lfloor x^u\rfloor\), \(V=x^v\). The outer prime cutoff \(p>x^u\) is exactly \(p>U\). The original kernel \(K_B\) vanishes for \(t>e^B\). All claims also hold with \(U=\lfloor Y^u\rfloor\), \(V=Y^v\) on \(Y\le x\le Y^{1+o(1)}\), with strict inequalities in the exponents preserved.

Define \(\beta_z=\mu_{L,>z}*a\) for real \(z>0\), allowing \(z<1\). Write \(P^+(1)=1\). The balanced signed remainder
\[
 R(x)=-\frac14\sum_{\substack{p>U\\h>U}}\Lambda_L(p)\beta_U(h)K_B(ph/x)
\]
has the following reduction, with \(\varepsilon>0\) arbitrary:
\[
 \begin{split}
 R(x)={}&\frac14\sum_{p>U,\ q>V}\Lambda_L(p)a(q)K_B(pq/x)\\
 &-\frac14\sum_{\substack{p>U,\ h>U\\P^+(h)\le V}}
          \Lambda_L(p)\beta_U(h)K_B(ph/x)\\
 &+O_{L,B,u,v,\varepsilon}
       \left(x^{\max\{2u\beta_*,\,1/2+u(\beta_*-1/2)\}+\varepsilon}\right).
 \end{split}
\tag{1}
\]
Both sums keep the exact kernel support and signs. In an off-line case the error has a fixed exponent gap from \(\beta_*\), and in the critical-line case it is at square-root scale up to the arbitrary \(\varepsilon\). Thus the smooth sector with a large prime factor can be absorbed into a pure prime-pair term, leaving a smooth companion with every factor at most \(x^v\). The range \(q>U\) in that pair remains symmetrizable. There is also an exact signed strip \(V<q\le U<p\). [Balanced support and twisted prefixes](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd)

## Exact extraction

Any \(h\) that contributes satisfies \(h\le H=e^Bx/U\). If \(h=qr\) with prime \(q>V\), then \(q^2>H\) and \(H/q<U\) for sufficiently large \(x\), by the conditions on \(v\). Thus \(q\) is unique, \(q\nmid r\), and \(r<U\). By multiplicativity, splitting inverse divisors according to whether \(q\) occurs gives, on this support,
\[
 \beta_U(qr)=a(q)\beta_U(r)+\mu_L(q)\beta_{U/q}(r)
             =-a(q)\beta_{U/q}(r).
\]
Here \(\beta_U(r)=0\) because \(r\le U\). The relation includes \(q>U\), when \(U/q<1\) and \(\beta_{U/q}=\mathbf1_{\{1\}}\). It also makes the lower condition \(h>U\) automatic. Put
\[
 J_{U,V}(s)=\sum_{\substack{q>V,\ qd\le U\\q\text{ prime}}}a(q)\mu_L(d)(qd)^{-s},
 \quad
 D^p_{>U}(s)=\sum_{p>U}\Lambda_L(p)p^{-s},
 \quad
 A_{>V}(s)=\sum_{q>V}a(q)q^{-s}.
\]
The Dirichlet series for \(\beta_{U/q}\) is \(1-L(s)\sum_{d\le U/q}\mu_L(d)d^{-s}\) in absolute convergence. Thus the entire \(P^+(h)>V\) sector of \(R\) is exactly the Mellin transform of the pure pair term minus \(\tfrac14\) times the inverse Mellin integral of
\[
 x^s H_B(s)L(s)J_{U,V}(s)D^p_{>U}(s).
\tag{2}
\]
This opens on \(\Re s=2\). The equality of sums on the original arithmetic side follows because \(K_B\) makes every term satisfy \(pqr\le e^Bx\), where the preceding classification applies.

## The finite combined inverse prefix

For each fixed \(\sigma>0\) and every \(\varepsilon>0\),
\[
 |J_{U,V}(\sigma+it)|
 \ll_{L,\sigma,\varepsilon}
 U^{(\beta_*-\sigma)_++\varepsilon}(3+|t|)^\varepsilon.
\tag{3}
\]
Indeed the untruncated series \(A_{>V}(s)/L(s)\) has coefficients bounded by \(O(d_2(n)^2)\), uniformly in \(V\). The complete prime series \(A(s)=\sum_q a(q)q^{-s}\) continues to \(\Re s>\beta_*\) as the primitive of \(-D^p(s)\), where \(D^p(s)=\sum_p\Lambda_L(p)p^{-s}\). On a fixed line to the right of \(\beta_*\), integrate horizontally from \(2+it\) using the local logarithmic derivative and the absolutely convergent higher powers to obtain \(A(s)\ll\log(3+|t|)\). The prefix \(A_{\le V}(s)\) is subpower in \(V\) and \(t\) there by the twisted prime-prefix estimate and partial summation with \(1/\log p\). Multiplication by the zero-free half-plane bound for \(1/L\) therefore gives \(A_{>V}/L\ll V^\delta(3+|t|)^\delta\) for arbitrarily small \(\delta>0\) on any fixed half-plane strictly to the right of \(\beta_*\).

Apply truncated Perron to the twisted prefix at \(U+\tfrac12\), start with \(\Re w=2\) and take height \((U+\tfrac12)^3\). The coefficient bound controls the endpoint truncation error as in the balanced prefix estimates. Shift \(w\) to \((\beta_*-\sigma)_++\delta\) and absorb \(V^\delta\), the height power, and the logarithmic factors by taking \(\delta\) small. This yields (3) without a sum of absolute inverse coefficients in \(d\).

In (2) use the exact identity
\[
 L(s)D^p_{>U}(s)=-L'(s)-L(s)Z(s)-L(s)B_U(s),
 \quad Z=\sum_{p,k\ge2}\Lambda_L(p^k)p^{-ks},
 \quad B_U=\sum_{p\le U}\Lambda_L(p)p^{-s}.
\]
Shift the \(L'J_{U,V}\) and \(LB_UJ_{U,V}\) terms to a sufficiently small fixed positive \(\sigma\) using degree-two convexity, (3), and the twisted prime-prefix power for \(B_U\). Both shifts converge absolutely against \(H_B(s)\ll_B (1+|t|)^{-2}\), and they cost \(O(x^{2u\beta_*+\varepsilon})\). For \(LZJ_{U,V}\), absolute convergence of \(Z\) just to the right of \(1/2\) gives \(O(x^{1/2+u(\beta_*-1/2)+\varepsilon})\). This proves (1). The \(Z\) term can instead be shifted with separate square and cube residues using its known virtual-character decomposition. [Exact square and cube references](https://github.com/Sodelin/Research-Commons/commit/5c48cb118860e1f2cd6cfb5e52fe1abadf9c681b)

## Centered completely split primes on both sides of the pair

Under verified Dirichlet GRH for the trivial character and the resolvent character \(\chi\), define real signed measures on \(t\ge2\) by
\[
 \begin{aligned}
 dM_{\rm sp}(t)&=\sum_{p\ \rm split}(\log p)\delta_p(dt)-dt/6,\\
 dN_{\rm sp}(t)&=\sum_{p\ \rm split}\delta_p(dt)-dt/(6\log t).
 \end{aligned}
\]
On the retained support all prime atoms are unramified for sufficiently large \(x\). The Dirichlet-centered signed remainder is exactly the target
\[
 -\frac34\int_{t>U}\sum_{h>U}\beta_U(h)K_B(th/x)\,dM_{\rm sp}(t).
\]
The same extraction gives the explicit comparison
\[
 \begin{split}
 -\frac34\int_{t>U}\sum_{h>U}\beta_U(h)K_B(th/x)\,dM_{\rm sp}(t)
={}&\frac94\iint_{\substack{t>U\\w>V}}K_B(tw/x)\,dM_{\rm sp}(t)dN_{\rm sp}(w)\\
 &-\frac34\int_{t>U}
   \sum_{\substack{h>U\\P^+(h)\le V}}\beta_U(h)K_B(th/x)\,dM_{\rm sp}(t)\\
 &+O_{L,B,u,v,\varepsilon}
   \left(x^{\max\{2u\beta_*,\,1/2+(1-v)(\beta_*-1/2)\}+\varepsilon}\right).
 \end{split}
\tag{4}
\]
The main references inside the pair are the exact Lebesgue measures displayed above, on the same product support. In the symmetric sector \(t,w>U\), \(dM_{\rm sp}=(\log t)dN_{\rm sp}\) and pairing gives weight \(\tfrac12\log(tw)\). The prime diagonal costs \(O_B(\sqrt x)\) in that sector by Chebyshev.

To verify (4), the unramified trace is \(3\mathbf1_{\rm sp}-(1+\chi)/2\), so
\[
\begin{aligned}
 \sum_pa(p)\log p\,\delta_p&=3\,dM_{\rm sp}+dE_{\log},\\
 \sum_qa(q)\,\delta_q&=3\,dN_{\rm sp}+dE_1,\qquad
 dE_1=(\log t)^{-1}dE_{\log}.
\end{aligned}
\]
Equalities here are restricted to unramified supports, with
\(dE_{\log}=-\tfrac12(\sum_p(1+\chi(p))\log p\,\delta_p-dt)\).
For the correction in the extracted sector, replace \(D^p_{>U}\) in (2) by the Mellin transform of the centered outer measure. This adds only a \(dE_{\log}\) transform, holomorphic and subpower on any fixed line to the right of \(1/2\), with the same error \(x^{1/2+u(\beta_*-1/2)+\varepsilon}\) as above. This uses the exact twisted Dirichlet centering on the unchanged lower support. [Twisted Dirichlet centering](https://github.com/Sodelin/Research-Commons/commit/4bfc76b31db848316d834a98b0b468381feee86a) · [Verified Dirichlet statements](https://math.mit.edu/~drew/grh/#what-was-verified)

The only additional error in replacing the inner prime measure by \(3dN_{\rm sp}\) is the product with \(dE_1\). Restrict the Mellin transform to the rectangular hull \(t\le e^Bx/V,\ w\le e^Bx/U\), which contains the full kernel support. On a fixed line \(\sigma>1/2\), the transform of the finite \(dE_1\) interval is \(O_\varepsilon(x^\varepsilon(3+|t|)^\varepsilon)\) by partial summation with \(1/\log w\) in the twisted Dirichlet estimate. The outer centered splitting transform is bounded by its trace prefix plus its Dirichlet error, giving a factor \(O((x/V)^{(\beta_*-\sigma)_++\varepsilon}(3+|t|)^\varepsilon)\). Shift to that line and use the original quadratic Mellin decay, then take \(\sigma\) just above \(1/2\). This is the second error exponent in (4). It is strictly smaller than \(\beta_*\) in an off-line case since \(v>0\).

All steps are hand arguments. The comparison leaves a product-supported signed prime pair and a smaller-prime smooth sector. The upper window for their sum remains open.

## Lowering the largest-prime threshold by finite inclusion–exclusion

The single-pair statement requires \(2v>1-u\). If a finite sum over products of large primes is allowed, it suffices that \(1-2u<v<u\). Put \(V=x^v\). For every \(q>V\) dividing a supported \(h\), \(h/q<U\) by this new restriction. If \(h=q^e r\) with \(q\nmid r\), opening the three inverse terms at \(q\), of exponents \(0,1,2\), then gives the exact local rule
\[
 \beta_U(q^e r)=
 \begin{cases}
 \mu_L(q^e)\beta_{U/q^e}(r), & e=1,2,\\
 0, & e\ge3 .
 \end{cases}
\tag{5}
\]
The lower local terms have truncated inverse threshold at least \(r\), so vanish. For a subset of several extracted primes the same rule iterates, since \(h/(qD)<U/D\) after removing an earlier product \(D\). The number of prime factors above \(V\) in a supported \(h\) is bounded in terms of \(u,v,B\).

For \(k\) distinct primes \(q>V\), let \(D\) range over their products with individual exponents \(e_q\in\{1,2\}\). Write
\[
 c(D)=\prod_{q\mid D}\mu_L(q^{e_q}),\qquad
 L^{(D)}(s)=L(s)\prod_{q\mid D}L_q(s)^{-1}.
\]
Inclusion–exclusion over the set of large prime divisors of \(h\), with exact \(q\)-adic exponents and (5), gives the high sector as the alternating sum over \(k\ge1\) of
\[
 -\frac14(-1)^{k+1}
 \sum_{\substack{p>U,\ D,\ r\ge1\\(r,D)=1}}
     \Lambda_L(p)c(D)\beta_{U/D}(r)K_B(pDr/x).
\tag{6}
\]
The coprimality condition is essential to impose the exact exponents. The Dirichlet series over \(r\) in (6) is
\[
 1-L^{(D)}(s)
     \sum_{\substack{d\le U/D\\(d,D)=1}}\mu_L(d)d^{-s}.
\]
Thus the main term of (6) has \(r=1\). With \(a(q)\) for exponent one and \(-\chi(q)\) for exponent two, all selected \(D\) terms in the main contribution have coefficient
\[
 \frac14\prod_{e_q=1} a(q)\prod_{e_q=2}(-\chi(q)).
\]
The factors are unramified for large \(x\). In particular all squarefree sectors have the same sign prefactor after replacing \(\mu_L(q)\) by \(-a(q)\), despite the alternating extraction.

The inverse correction of (6) uses the following combined prefix:
\[
 J_k(s)=
 \sum_{\substack{D d\le U\\(d,D)=1}}
 \frac{c(D)\mu_L(d)\prod_{q\mid D} L_q(s)^{-1}}{(Dd)^s}.
\]
At a fixed line \(\sigma>1/2\) this obeys
\[
 |J_k(\sigma+it)|
 \ll_{L,k,\sigma,\varepsilon}U^{(\beta_*-\sigma)_++\varepsilon}
 (3+|t|)^\varepsilon.
\tag{7}
\]
Indeed the untruncated series in the independent variable \(z\), keeping the local factors \(L_q(s)^{-1}\) fixed, equals \(L(z)^{-1}e_k((w_q)_{q>V})\), where
\[
 w_q=L_q(s)^{-1}L_q(z)
      \bigl(\mu_L(q)q^{-z}+\mu_L(q^2)q^{-2z}\bigr).
\]
This follows from removing the inverse Euler factor at a selected prime in the coprime \(d\) series. For \(\Re z\ge\beta_*+\delta\), \(w_q=\mu_L(q)q^{-z}+O(q^{-\Re z-\min(\sigma,\Re z)})\). The error converges absolutely since \(\sigma>1/2\). The leading sum is \(-A_{>V}(z)\), already controlled by the continued prime series and its twisted prefix. All power sums \(\sum_{q>V}w_q^j\) with \(j\ge2\) converge absolutely. Newton identities express the fixed elementary symmetric polynomial \(e_k\) in these power sums. Hence the untruncated series is holomorphic and subpower on every fixed half-plane strictly to the right of \(\beta_*\), with an arbitrary small power of \(V\) as before. Its coefficients in the variable \(z\) are bounded by \(O_k(d_2(n)^{O_k(1)})\), uniformly in \(s\) on the selected \(\sigma\)-line, by counting divisors \(D\mid n\) and bounding the finitely many local polynomials. Truncated Perron at \(U+\tfrac12\) proves (7).

The correction still has \(L(s)D^p_{>U}(s)\), so after replacing it by \(-L'-LZ-LB_U\) one can shift to any fixed \(\sigma>1/2\). The original quadratic Mellin decay handles all three terms. Using (7) and the bound on \(B_U\), then taking \(\sigma\) just above \(1/2\), the error is at most
\[
 O_{L,B,u,v,\varepsilon}
 \left(x^{1/2+2u(\beta_*-1/2)+\varepsilon}\right).
\tag{8}
\]
This has a strict gap from \(\beta_*\) in the off-line case and is at square-root scale with arbitrary subpower loss in the critical-line case. The remaining companion has \(P^+(h)\le x^v\) for any fixed \(v>1-2u\), which can be near \(2\eta\) in the balanced regime. The single-pair form (4) has the advantage of only two centered prime measures, while the extension (6)–(8) permits more prime factors.

## Removing each squared selected prime from the pure term

Under verified Dirichlet GRH for the resolvent \(\chi\), every squared selected prime in the main terms of (6) can also be discarded. The error from this removal is
\[
 O_{L,B,u,v,\varepsilon}
 \left(x^{1/2+(1-2v)(\beta_*-1/2)-v/2+\varepsilon}\right).
\tag{9}
\]
In particular (6) retains only \(D\) squarefree, with coefficient \(\tfrac14\prod_{q\mid D}a(q)\). In the critical-line case, (9) has a power saving over square-root scale.

For each fixed \(k\), compare the elementary symmetric polynomials in
\(w_q=a(q)q^{-s}-\chi(q)q^{-2s}\) and \(w^0_q=a(q)q^{-s}\), over \(q>V\). By Newton identities the difference is a fixed finite sum of products of power sums, and each product has a difference factor
\[
 T_j(s)=\sum_{q>V}\bigl(w_q^j-(w_q^0)^j\bigr)
\]
for some \(1\le j\le k\). For \(j\ge2\), each summand only involves exponents at least \(j+1\ge3\), so \(|T_j(\sigma+it)|\ll_k V^{1-3\sigma}\) uniformly on fixed \(\sigma>1/2\). For the \(j=1\) factor use the sharper Dirichlet bound
\[
 \left|\sum_{q>V}\chi(q)q^{-2s}\right|
 \ll_{\sigma,\varepsilon}
 V^{1/2-2\sigma+\varepsilon}(3+|t|)^\varepsilon.
\tag{10}
\]
To prove (10), first keep the \(\log q\) weight. The complete twisted Dirichlet prime series \(D_\chi(z)\) is holomorphic for \(\Re z>1/2\) and logarithmically bounded on each closed sub-half-plane, by verified GRH and subtraction of its absolutely convergent higher powers. With \(z=2s\), apply truncated Perron to the sharp prefix at \(\lfloor V\rfloor+1/2\) and shift the auxiliary line across \(w=0\) to \(1/2-2\sigma+\delta\), with \(\delta>0\) arbitrarily small. The residue is exactly \(D_\chi(z)\), hence bounds the tail by the new vertical and horizontal integrals. A height \(V^C(3+|t|)\) with \(C\) sufficiently large makes the truncation and horizontal errors smaller than the new vertical bound. The new line argument \(z+w\) has real part \(1/2+\delta\), giving \(V^{1/2-2\sigma+\delta}\) times logarithms. Remove the \(\log q\) weight by partial summation against \(1/\log q\) using the same tail bound at every \(V\). This proves (10).

In each product, leave one \(T_j\) factor untruncated. Every norm on its arithmetic support exceeds \(V^2\). Restrict the product of all other factors, including the outer prime factor \(D^p_{>U}\), to its single exact prefix with norm at most \(e^Bx/V^2\). This leaves the original support unchanged after inserting \(K_B\). The remaining product has divisor-bounded coefficients up to a harmless power of \(\log n\), is holomorphic on \(\Re s>\beta_*\), and is subpower there in \(U,V,|t|\). Indeed its \(j=1\) prime factors are controlled by the continued prime series and their finite prefixes, and its higher power sums converge absolutely there. Truncated Perron as in (3) therefore bounds the combined prefix on the \(\sigma>1/2\) line by
\[
 O_\varepsilon\bigl(
       (x/V^2)^{(\beta_*-\sigma)_++\varepsilon}
       x^\varepsilon(3+|t|)^\varepsilon\bigr).
\]
Multiplication by \(T_j\) and \(x^sH_B(s)\), followed by the shift to \(\sigma\) just above \(1/2\), is absolutely integrable because of the quadratic smoothing. It gives (9). This uses cancellation only for the determinant term and keeps the signed squarefree multiprime pieces as part of the target.
