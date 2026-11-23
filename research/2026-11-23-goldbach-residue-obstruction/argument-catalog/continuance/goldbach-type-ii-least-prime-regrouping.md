# A least-prime regrouping in the fixed Selberg Goldbach Type II sum

Keep the original fixed-target expansion with the peer's fixed nonnegative Selberg square \(W_N(n)\). Write \(L=\log N\), \(H=\sqrt N\), \(m=qh\), \(n=N-m\), and \(Y_0=\exp(L^{.005})\). Keep ordered \(q,h\in(H/2,H]\), squarefree \(m\) with \((m,N)=1\), the exact count and mark projector \(F(m)\), squarefree \(Y_0\)-rough \(n\), prime \(N^{1/10}<\ell\le N^{1/8}\), and the original strict \(d=n/\ell>D_0\). Write \(U=V=N^{1/5}\), \(P=H^{21/20}\). Opening \(B_V(v)\) gives
\[
 qh+\ell uws=N,\quad u>U,\quad w>V,
 \qquad
 \tfrac12 F(m)W_N(n)\mu(h)\mu(u)\Lambda(w)\log(h/q)
             \frac{\log\ell}{\log(uws)}.
 \tag{1}
\]
The endpoint masks make \(w\) prime and distinct from \(\ell\), with \((\ell w,us)=1\). We may retain the base restriction \(\ell w>P/U\) from the preceding charge. The same small-base proof works with the fixed square, since the pinned Type I transfer keeps it intact on grouped indices at most \(P\). [Pinned fixed Selberg expansion and Type I proof](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md) · [Pinned small-base regrouping](https://github.com/Sodelin/Research-Commons/blob/581f30cc217415f438594c02cfc4f894837fe981/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-small-prime-base.md).

## A subpower least prime of the remaining product

For fixed \(q,h,\ell,w\), put \(M=n/(\ell w)=us\). Restrict to \(M>1\) with least prime \(p\le V_0\), where \(V_0\ge2\) and \(\log V_0=o(L)\). The signed sum of (1) on this slice is
\[
 O_A\!\left(\frac{\varphi(N)(1+\log V_0)}L+\frac N{L^A}\right)=o(N)
 \tag{2}
\]
for each fixed \(A>0\). The bound holds separately on either endpoint parity, and with any further mask fixed by \(q,h,n,\ell,w\).

Use this charge before imposing any further condition on the actual divisor \(u\), such as a ratio interval or a factor count of \(u\). The identity below needs the entire tail \(u\mid M, u>U\) at each fixed \(q,h,\ell,w\). The base cutoff, endpoint cut, count selections depending on \(\ell\), and any allocation mask depending only on \(q,h,m\) preserve that tail.

All factors outside \(\mu(u)\) in (1) are fixed in that tail, since \(d=n/\ell=wM\). For squarefree \(M=pM'\), the exact identities are
\[
 \sum_{\substack{u\mid M\\u>U}}\mu(u)
 =-\sum_{\substack{u\mid M\\u\le U}}\mu(u)
 =-\sum_{\substack{a\mid M'\\ U/p<a\le U}}\mu(a).
\]
In the short sum, \(a\) and \(pa\) cancel when \(a\le U/p\), including equality. When \(U/p<a\le U\), only \(a\) is present. This replaces the original tail by terms with \(u'=a\in(U/V_0,U]\), \(v'=d/a\), leaving the equation \(qh+\ell u'v'=N\) and the strict \(d>D_0\) unchanged. The new sign is the exact minus sign in the displayed identity. For fixed transformed \(q,h,\ell,u',v'\), each admitted \(w\) divides \(v'\) and has at most one least-prime selection \(p\). Its nonnegative \(\Lambda(w)\) weights sum to at most \(\log v'\). Thus the absolute transformed weight is \(O(W_N(n)\log\ell)\).

In each dyadic endpoint band and at fixed \(\ell\), the identity \(\log(u'/v')=2\log u'+\log\ell-\log n\) gives a log interval of width at most \(2\log V_0+\log2\). The peer's absolute fixed-square count applies on this interval. Its only lower-size requirement on the smaller factor is used in the harmonic averaging error \(D^2N^{o(1)}/X\), with \(D=N^\kappa\), \(\kappa<1/100\), and a dyadic scale \(X\) of that factor. Here \(u'>N^{1/5-o(1)}\) and \(v'\ge w>V\), so \(X\gg N^{1/5-o(1)}\) still gives a power saving. The modulus cap \(\ell\min(u',v')\le\sqrt{\ell n}\le N^{9/16}\) is unchanged, so the lattice remainder remains a power saving too. The local main term and its fixed Selberg quadratic form are unaffected. Summing over the full prime \(\ell\) band yields (2). [Pinned absolute square count and errors](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md#averaging-the-type-ii-square-over-the-two-factors).

## Two separate endpoint-parity identities

On the expanded arithmetic support, restrict to \(\mu(n)=-1\), \(u>U\), and \(s>U\). Exchanging \(u,s\) fixes every other variable and coefficient in (1), including \(W_N(n)\) and the strict \(d\) cutoff. The condition \(v>V\) remains automatic from \(w>V\). Since \(\ell,w\) are distinct primes and \(n\) is squarefree, \(\mu(u)\mu(s)=\mu(n)=-1\). The two ordered terms cancel exactly. This identity permits further \(u,s\)-symmetric masks. The parity condition here concerns expanded \(n\); it is an additional restriction of that arithmetic sum.

Another test on the opened support before divisor-dependent cuts keeps both endpoint parities and imposes \(r'=\ell ws\le P\). Multiply the weight by \(\mu(n)\), which changes \(\mu(u)\) into \(\mu(s)\) on the squarefree endpoint support. Group \(\ell,w,s\) into the signed index \(r'\), leaving \(u\) as the smooth complement. After the common endpoint trim \(n\ge N/L^B\), the original \(u>U\) is automatic since \(u=n/r'\ge N/(PL^B)>U\). The condition \(v>V\) follows from \(w>V\), and the base test \(\ell w>P/U\) belongs in the grouped coefficient. The pinned integral for \(1/\log d\) makes the complement smooth and the grouped coefficient \(O(L^2)\), by the at most five possible \(\ell\mid r'\) and the von Mangoldt divisor sum on \(r'/\ell\). In estimating this transformed sum, adding nonsquarefree rough endpoints costs arbitrary logarithmic savings by the pinned \(O(N/Y_0)\) endpoint union and divisor moments. Keeping \(W_N(n)\) and roughness uses exactly the pinned polynomial-period Type I transfer. This proves arbitrary logarithmic saving for the twisted sum on \(r'\le P\), hence for the difference between its original even- and odd-endpoint sums. It supplies no estimate on their sum.

## Absolute small-prime bound with additional selections

There is also an absolute bound for the part of the same expansion on which some \(p\le V_0\) divides \(n\), with \(\log V_0=o(L)\). It is
\[
 \ll_A \varphi(N)\left(\frac{1+\log V_0}{L}\right)^{2/3}+N/L^A.
 \tag{3}
\]
This upper bound survives arbitrary further intersections, including tests on \(u\). The stronger exponent in (2) uses complete signed regrouping.

For the proof use the averaged local Bernoulli endpoint density \(g=g_2\) of the pinned Selberg square. Write \(D=N^\kappa\), \(z=N^c\) for its fixed levels, and \(h(r)=\prod_{p\mid r}g(p)/(1-g(p))\) on squarefree supported indices. Its diagonal coordinates are \(y_d=\sum_{d\mid a}\lambda_a g(a)=\mu(d)h(d)/G_D\) for \(d\le D\), with \(G_D=\sum_{d\le D}h(d)\asymp\prod_{p\le z}(1+h(p))\). Force \(Y_p=1\) for one \(p\le V_0<z\), leaving the other flags independent. For \(p\nmid d\) the new diagonal coordinate for the same square is
\[
 y_d^{(p)}=y_d+(1/g(p)-1)y_{pd}.
\]
Indeed forcing the flag replaces each coefficient \(\lambda_a\), \(p\nmid a\), by \(\lambda_a+\lambda_{pa}\). The displayed coordinate is zero for \(d\le D/p\) by the formula for \(y_{pd}\), and equals \(y_d\) otherwise. The diagonal identity therefore gives
\[
 \mathbb E[W_N\mid Y_p=1]
 =G_D^{-2}\sum_{\substack{D/p<d\le D\\p\nmid d}} h(d).
\]

The full Euler-product normalization of \(h\) is the law of a random squarefree product with independent prime frequencies \(g(r)\). Write \(T_0=\sum_{r\le z}Y_r\log r\). Its probability in any log interval \(I\) of length at most \(\Delta\), \(1\le\Delta\le\log z\), is \(O((\Delta/\log z)^{2/3})\). To prove this, separate the event with no selected prime exceeding \(Y_1\), of probability \(O((\log Y_1/\log z)^2)\) by Mertens and the dimension-two survival factors of the fixed square. For any occurrence with such a selected prime, take a union over \(r>Y_1\). If \(T_{-r}=T_0-Y_r\log r\), independence and conditioning on \(Y_r=0\) give
\[
 \sum_{Y_1<r\le z}g(r)\mathbb P(T_{-r}\in I-\log r)
 \le \mathbb E\sum_{\substack{Y_1<r\le z\\ T_0\in I-\log r}}\frac{g(r)}{1-g(r)}
 \ll \frac{\Delta}{\log Y_1}.
\]
The last bound uses the reciprocal prime sum over a log interval, \(r>Y_1\), and \(g(r)=O(1/r)\). Choose \(\log Y_1=(\Delta\log^2 z)^{1/3}\). Taking \(\Delta=1+\log p\) in this interval bound yields
\[
 \mathbb E[W_N\mid Y_p=1]
 \ll G_D^{-1}\left(\frac{1+\log p}{L}\right)^{2/3}.
\]
A union bound with \(g(p)=O(1/p)\) and partial summation over \(p\le V_0\) gives averaged model mass
\[
 \mathbb E[W_N\mathbf1_{\exists p\le V_0:Y_p=1}]
 \ll G_D^{-1}\left(\frac{1+\log V_0}{L}\right)^{2/3}.
\]
For transfer, insert the event \(p\mid n\) separately in each rectangle count and sum the resulting upper bounds. This adds at most one prime \(p\) to each CRT modulus from the Selberg square, with no extra CRT test when \(p\mid\min(u,v)\). Both this prime and the total number of such choices are \(N^{o(1)}\). The harmonic average in the smaller factor uses the same affine dependence on its prime flags and floor error as in the fixed-square proof. Thus the lattice and harmonic-average errors still save a power. Restoring the dyadic and prime-complement weights contributes \(O(NL^2)\) times the model mass. Since \(G_D^{-1}\ll\varphi(N)/(NL^2)\), this proves (3). [Pinned square, Euler product, and rectangle transfer](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md)

These are hand proofs. The broad signed sum on the remaining fixed-target support remains open. No numerical or Lean verification is used.
