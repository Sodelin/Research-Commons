# A prime-only Vaughan reduction for the degree-two dilation window

Work at \(\delta=0\) with one fixed tempered degree-two standard factor \(L\), for example the conductor-23 standard \(S_3\) Artin factor. Let \(a(n)\) and \(\mu_L(n)\) be the coefficients of \(L\) and \(L^{-1}\), let \(D(n)=a(n)\log n\), and let \(\Lambda_L\) be the coefficients of \(-L'/L\). A subscript \(\le U\) or \(>U\) means restriction to that set of indices. Use the dilation kernel
\[
 K_B(t)=e^{-B}(e^B/t-1)_+-(1/t-1)_+,
 \qquad \mathscr K_x(c)=\sum_{n\ge1}c(n)K_B(n/x),
\]
where \(B>0\) is fixed. The arithmetic-reference observable is \(C_{0,B}(x)=-\mathscr K_x(\Lambda_L)/4\) for one self-dual degree-two factor. For a dual-closed family, sum the argument over the factors and replace \(1/4\) by \(1/(2d)\), where \(d\) is the total degree. [Pinned observable](https://github.com/Sodelin/Research-Commons/blob/1e5d50b6571a6333d3d2382f82345a1f22a1ee16/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/positive-window-standard-automorphic-families.md#positive-count-and-fixed-reference-subtraction)

For \(U,V\ge1\), the exact convolution identity is
\[
\Lambda_L=
 \mu_{L,\le U}*D+\Lambda_{L,\le V}
 -\mu_{L,\le U}*a*\Lambda_{L,\le V}
 +(\mu_{L,>U}*a)*\Lambda_{L,>V}.
\tag{1}
\]
Indeed, split \(\Lambda_L=\mu_L*D\) at \(U\), use \(D=a*\Lambda_L\), and split the latter \(\Lambda_L\) at \(V\). The identity \(\mu_{L,>U}*a=\mathbf1_{\{1\}}-\mu_{L,\le U}*a\) gives the two middle terms.

The Mellin contour of the degree-two Type I argument yields
\[
\mathscr K_y(a),\ \mathscr K_y(D)\ll_{L,B,\epsilon}y^\epsilon\qquad(y>0).
\]
For \(a\), use \(L(s)\) in place of \(-L'(s)\) in that contour. In both cases the dilation kills the kernel pole at \(1\). The unit-disc root bounds give \(|\mu_L(m)|\le\tau(m)\) and \(|\Lambda_L(p^k)|\le2\log p\), including the ramified factors. Thus the first term of (1), after applying \(\mathscr K_x\), is \(O(x^\epsilon U^{1-\epsilon}\log(2U))\). The second is \(O(V)\) by Chebyshev. For the third, apply the \(a\)-bound at \(y=x/(mr)\) and sum over \(m\le U,r\le V\) to get
\[
O_{L,B,\epsilon}\bigl(x^\epsilon(UV)^{1-\epsilon}\log(2U)\bigr).
\]
Fix an integer \(U=Y^{o(1)}\) with \(U\ge1\), for example \(U=\lfloor(\log Y)^A\rfloor\) for fixed \(A>0\), and put \(V=\lfloor\sqrt Y/U\rfloor\) on a window starting at \(Y\). These three bounds are each \(O_{L,B,\epsilon}(x^{1/2+\epsilon})\) for all sufficiently large \(Y\), uniformly for \(x\ge Y\), after decreasing the contour \(\epsilon\) to absorb logarithms. The threshold on \(Y\) can depend on the chosen function \(U\).

Put \(\beta_U=\mu_{L,>U}*a\), supported on \(h>U\). In the last term of (1), the variable \(r\) supporting \(\Lambda_{L,>V}\) is a prime power. Its powers with exponent at least two can all be removed at square-root cost. For each fixed \(r\), the exact inner sum is
\[
 \mathscr K_{x/r}(\beta_U)=K_B(r/x)-\sum_{m\le U}\mu_L(m)\mathscr K_{x/(mr)}(a)
 \ll_{L,B,\epsilon} 1+x^\epsilon U^{1-\epsilon}\log(2U).
\]
The bound \(\sum_{p^k\le e^Bx,\ k\ge2}\log p\ll_B\sqrt x\) then makes the removed power sector \(O_{L,B,\epsilon}(x^{1/2+\epsilon})\), again taking \(Y\) sufficiently large for the specified \(U\). This uses the signed inner identity before taking absolute values.

The same fixed-\(r\) estimate removes the primes \(V<p\le Q\) for any cutoff \(Q\ge V\) with \(Q\le Y^{1/2+o(1)}\). Chebyshev gives \(\sum_{p\le Q}|\Lambda_L(p)|\ll Q\), so the cost is again \(O_{L,B,\epsilon}(x^{1/2+\epsilon})\) for all sufficiently large \(Y\), uniformly for \(x\ge Y\).

The resulting exact signed prime remainder is
\[
R_{U,Q,B}(x)=-\frac14\sum_{Q<p\le e^Bx/(U+1)}\Lambda_L(p)
 \sum_{U<h\le e^Bx/p}\beta_U(h)K_B(hp/x),
\quad \beta_U(h)=\sum_{m\mid h,\ m>U}\mu_L(m)a(h/m).
\tag{2}
\]
There is one more exact cancellation in the inner support. Let
\[
 E_U(h)=\prod_{p\le U,\ p\mid h} p^{\min(2,v_p(h))}.
\]
If \(1<E_U(h)\le U\), then \(\beta_U(h)=0\). In fact for \(h>U\) one has \(\beta_U(h)=-(\mu_{L,\le U}*a)(h)\). All nonzero inverse coefficients at divisors \(m\mid h\) with \(m\le U\) are supported on divisors of \(E_U(h)\). When \(E_U(h)\le U\), the whole divisor sum factors, and any prime \(p\le U\) dividing \(h\) gives the local factor \((\mu_L*a)(p^{v_p(h)})=0\). If \(h\) has no prime factor at most \(U\), its coefficient is \(-a(h)\). Thus the inner support in (2) can be restricted to those rough \(h\) and to \(E_U(h)>U\).

For a shorter window \(Y\le x\le Y\exp H(Y)\) with \(0\le H(Y)=o(\log Y)\), choose \(Q=\sqrt Y\exp(H(Y)+J(Y))\), where \(J(Y)\to\infty\) and \(J(Y)=o(\log Y)\). Throughout the remaining sum, \(p>Q\) and \(h\le e^B\sqrt Y\exp(-J(Y))\). This includes windows with \(H(Y)=O((\log\log Y)^2)\).

All discarded terms are \(O_{L,B,\epsilon}(x^{1/2+\epsilon})\). For every fixed \(b>1\), this changes the weighted positive-part integral on \([Y,Y^b]\), with weight \(x^{-1/2}dx/x\), by at most \(O(Y^{\eta/2}\log Y)\) for any prescribed \(\eta>0\) after choosing \(\epsilon\) sufficiently small. Thus (2) has the same one-sided subpower budget criterion as the undamped observable. The same comparison applies to the shorter windows above. The resulting problem is a signed trace sum over actual primes with the two-variable weight displayed above. Its required window estimate remains open.
