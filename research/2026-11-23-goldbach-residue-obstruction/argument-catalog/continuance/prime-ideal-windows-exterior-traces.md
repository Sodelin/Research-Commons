# Prime-ideal windows from exterior-power trace means

The positive-count window for a fixed dual-closed standard automorphic family remains equivalent to the original window after retaining just prime ideals, whenever the exterior traces satisfy the means below. Kim's exterior-square lift supplies the new input for \(\mathrm{GL}_4\), with no critical-line hypothesis on the lift. The required upper window for the chosen standard family remains open. [Pinned damped-window audit](https://github.com/Sodelin/Research-Commons/blob/a4f70e178b29f71ac91d8f29c14f89bb23209725/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/damped-window-threshold-and-prime-ideal-audit.md)

## Sufficient coefficient estimates in general degree

Keep the analytic and local growth assumptions of the pinned standard-family window. For a member \(\pi\) of degree \(n\ge2\), let \(A_{\mathfrak p}\) be its normalized Satake matrix at an unramified prime ideal, \(q=\mathrm N\mathfrak p\), \(p_k=\operatorname{tr}(A_{\mathfrak p}^k)\), and \(e_j=\operatorname{tr}(\bigwedge^j A_{\mathfrak p})\). Choose a common finite root bound \(q^\tau\) with \(0\le\tau\le\delta<1/2\), where \(\delta\) is the damping exponent. Fix an integer \(K_0\ge2\) with \(\tau+1/K_0\le1/2\). Suppose that for \(2\le j\le\min(\lfloor n/2\rfloor,K_0-1)\)
\[
 \sum_{q\le X}|e_j|\log q\ll_\pi X^{j/2}(1+\log X)^A
 \tag{1}
\]
for some fixed \(A\ge0\), with sums over unramified primes. Then all powers \(\mathfrak p^k\) with \(k\ge2\) can be dropped from both the nonnegative count and its exact reference, with an error \(O(x^{1/2}(1+\log x)^A)\) in the square-root-normalized statistic. The stated first absolute means suffice even though Newton's identities are nonlinear.

Indeed the unitary local contragredient gives \(e_{n-j}=e_n\overline{e_j}\) with \(|e_n|=1\). Thus (1) controls all the corresponding upper-index traces as well. The first absolute mean of \(e_1\) follows by Cauchy–Schwarz from the usual Rankin–Selberg second moment:
\[
 \sum_{q\le X}|e_1|^2\log q\ll_\pi X.
 \tag{2}
\]
The self Rankin–Selberg function \(R=L(s,\pi\times\widetilde\pi)\) has nonnegative log coefficients, including the first prime coefficient \(|e_1|^2\log q\). It has a simple pole at \(1\) and no other pole on \(\Re s=1\). In the pole classification a shifted pole would force a pure norm self-twist, which is excluded by the central character. Nonnegativity and \(3+4\cos v+\cos(2v)\ge0\) give
\[
 3(-R'/R)(\sigma)+4\Re(-R'/R)(\sigma+it)+\Re(-R'/R)(\sigma+2it)\ge0
\]
for \(\sigma>1\). A zero of multiplicity \(m\ge1\) at \(1+it\), \(t\ne0\), would give coefficient at most \(3-4m\) of \(1/(\sigma-1)\), a contradiction. Thus \(-R'/R(s)-1/(s-1)\) is regular on the line, and Wiener–Ikehara gives the summatory bound for its nonnegative coefficients. This proves (2). The prime-ideal Chebyshev bound gives the first absolute moment of \(e_1\) by Cauchy–Schwarz and handles the constant \(e_n\). [Rankin–Selberg pole classification](https://doi.org/10.2307/2374264) · [Nonnegative self-pair coefficients, Brumley Appendix A](https://arxiv.org/abs/1804.03654)

For a fixed \(2\le k<K_0\), Newton's identities express \(p_k\) as a polynomial in \(e_j\), \(j\le\min(k,n)\), of weighted degree \(k\), with \(e_j\) of degree \(j\). Consequently
\[
 |p_k|\ll_{n,k}1+\sum_{j\le\min(k,n)}|e_j|^{k/j}.
\]
The \(j=1\) term can use (2): at \(q\le X\), the pointwise bound is \(|e_1|\ll_n X^\tau\), so its moment is at most \(O_\pi(X^{1+(k-2)\tau})\). For each \(j\ge2\), \(|e_j|\ll_n X^{j\tau}\), and its first absolute moment gives at most \(O_\pi(X^{j/2+(k-j)\tau}(1+\log X)^A)\). The reflection identity for exterior traces ensures that only the indices in (1) were needed. Both \(1+(k-2)\tau\) and \(j/2+(k-j)\tau\) are at most \(k/2\). On setting \(X=T^{1/k}\), each contributes at most \(O_\pi(\sqrt T(1+\log T)^A)\). Summing over these finitely many powers gives \(O_\pi(\sqrt T(1+\log T)^A)\) before damping.

Partial summation with \(n^{-\delta}\) and the bounded difference kernel of the pinned observable give an error \(O(x^{1/2-\delta}(1+\log x)^A)\) in the damped statistic. The powers \(k\ge K_0\) are already admissible for deletion by the elementary high-power bound using \(\tau+1/K_0\le1/2\). The finitely many ramified primes give \(O(1+\log x)\) in the damped statistic by the coefficient cap. A degree-one factor uses the elementary argument with \(\tau=0\).

After multiplying by \(x^\delta\), the window integral changes by at most \(O((1+\log Y)^{A+1})\). Here the inequality \(|a_+-b_+|\le|a-b|\) applies pointwise, and the same finite truncation is used on the raw and reference counts. This preserves the bound by \(Y^\eta\) on arbitrarily late windows, using budget \(Y^{\eta/2}\) before adding the error. It also preserves the strictly positive logarithmic growth rate when an off-line zero exists. A prime ideal here means exactly exponent \(k=1\) in its local Euler factor, regardless of its residue degree over \(\mathbb Q\).

The weaker bounds \(O_{\pi,\epsilon}(X^{j/2+\epsilon})\) in (1) for all \(\epsilon>0\) also suffice. They give an error \(O_{\pi,\epsilon}(x^{1/2+\epsilon})\) in the normalized statistic, after taking the mean estimates with a smaller \(\epsilon\) if needed. For a fixed window \([Y,Y^{1+\kappa}]\), choose \((1+\kappa)\epsilon<\eta/2\), or below the positive rate being tested. This preserves the criterion and the rate, with constants depending on the fixed family.

## Degree four and the square coefficient

For a unitary cuspidal \(\pi\) on \(\mathrm{GL}_4\) over a number field, only \(e_2\) is extra. Kim's Theorem A, proved as Theorem 5.3.1, gives the exterior-square lift as an isobaric sum \(\Pi=\boxplus_{i=1}^r \sigma_i\) of unitary cuspidal representations. The assertion of unitarity for all the constituents is already established for the weak lift in Proposition 4.1.6 and Theorem 4.2.3. The possible exceptions to the stronger local matching concern supercuspidal places over \(2,3\) and do not affect the good-prime trace argument. [Kim, Proposition 4.1.6, Theorems 4.2.3 and 5.3.1](https://doi.org/10.1090/S0894-0347-02-00410-1)

Away from finitely many places \(e_2=\sum_i\lambda_{\sigma_i}(\mathfrak p)\), so
\[
 |e_2|^2\le r\sum_i|\lambda_{\sigma_i}(\mathfrak p)|^2.
\]
Apply (2) separately to each unitary cuspidal constituent and use Cauchy–Schwarz with the prime-ideal Chebyshev bound. This proves (1) with \(A=0\), so the normalized error is \(O(\sqrt x)\) for every such fixed family. The finite exceptional places are absorbed by the damped coefficient cap. Thus every fixed family of degrees up to four in the original scope admits the prime-ideal-only criterion without any added RH hypothesis. Neither the exterior-square factors nor their Rankin–Selberg factors enter the zero set of the window.

## The converse for absolute estimates

The same condition describes what is needed for absolute deletion, as opposed to a signed cancellation between higher powers. For a single good-prime matrix family, assume
\[
 \sum_{\mathfrak p,\ k\ge2:\ q^k\le T}|p_k|\log q
       \ll \sqrt T(1+\log T)^A.
\]
Each fixed \(p_k\) then has first absolute mean \(O(X^{k/2}(1+\log X)^A)\) on \(q\le X\). The reverse Newton identities express \(e_j\) as a polynomial of weighted degree \(j\) in the \(p_k\), with weight \(k\). Use (2) on the \(p_1\) term and these first absolute means on \(p_k\) for \(k\ge2\); the same local growth calculation gives (1). Together with the forward argument this characterizes the absolute square-root estimate under the given local bound and (2).

For a product of several factors, this necessity concerns the exterior traces of the direct-sum good-prime matrix. Its \(p_k\) are the summed log traces, which can cancel between constituents. Checking exterior traces constituent by constituent remains a sufficient condition. In particular the square identity \(p_2=e_1^2-2e_2\) identifies the first missing mean: given (2), the absolute square-power estimate is equivalent to a linear first absolute moment for \(e_2\). In degree five it is the only additional index in (1).

## A limitation of the standard second moment alone

For a local data model over \(\mathbb Q\), take \(0<t<1/4\) and assign at each prime the self-dual unitary complementary-series root list
\[
 i p^t,\quad i p^{-t},\quad -i p^t,\quad -i p^{-t},\quad 1 .
\]
It has determinant \(1\), first trace \(1\), and square trace \(1-2p^{2t}-2p^{-2t}\). Its formal self-pair coefficients at \(p^k\) are \(|p_k|^2\log p\). The \(k=1\) contribution has the ordinary prime number theorem main term \(X\), and the sum for \(k\ge2\) is \(O(X^{1/2+2t})=o(X)\) by Chebyshev and the local root bound. Thus even the self-pair prime number theorem and the local cap are consistent with these square traces. With damping \(\delta=t\), the square coefficients are negative and of size \(\log p\) after damping. In the normalized two-scale count their contribution is positive and \(\asymp_B x^{1/2+t}\), by the fixed sign of the difference kernel and the prime count up to \(\sqrt x\). The powers \(k\ge3\) have normalized absolute effect \(O_B(x^{1/3+t})\). Thus this information alone cannot justify deletion of the square term at a square-root scale. The model uses independently assigned local parameters and makes no assertion about a global automorphic representation.

These coefficient and window comparisons are hand proofs. Lean verifies the pinned generic Landau implication used in the original window. The specialized forward estimate is open, and no computation or numerical zero check is used. There is no additive Goldbach bound from these single-prime means.
