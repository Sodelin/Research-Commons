# A long-divisor transfer for the paired Goldbach outer rows

Fix \(N=2^k\), \(L=\log N\), \(H=\sqrt N\), \(\alpha=H/L^{K_0}\), with \(K_0>3\) fixed. Let \(\mathcal P\) be the ordered raw support with \(q,h>\alpha\), \(qh<N\), \(q,h\) odd, \(qh\) squarefree, and \((q,h)\) outside the central square \((H/2,H]^2\). Since \(\alpha>N^{1/4}\) eventually, these are exactly the terms in the seven outer rows whose transposes are present, apart from the negligible single possible even von Mangoldt argument. Write \(m=qh,\ n=N-m\). Define the paired outer row on \(\mu(m)=\epsilon\), \(\epsilon\in\{-1,+1\}\), using \(q<h\) and the signed weight
\[
 W(q,h)=-\mu(h)\log h-\mu(q)\log q
        =-\mu(h)(\log h+\epsilon\log q).
\]
The raw contribution in this row is \(\sum W(q,h)\Lambda(n)\). [Exact pairing of the raw outer cells](https://github.com/Sodelin/Research-Commons/commit/0bcaccdd69d047590e171051120d6c801a4cd527)

Let \(P=N^\gamma\) for any fixed \(1/2<\gamma<10/19\), in particular \(\gamma=21/40\) as in the separate center. For either choice of \(\epsilon\) the following identity holds for every \(A>0\) at all sufficiently large powers of two:
\[
 \sum_{\substack{(q,h)\in\mathcal P,\,q<h\\\mu(m)=\epsilon}}
        W(q,h)\Lambda(n)
 =
 2\sum_{\substack{(q,h)\in\mathcal P,\,q<h\\
          \mu(m)=\epsilon,\ \mu^2(n)=1,\ \mu(n)=+1}}
         W(q,h)\sum_{\substack{d\ell=n\\d>P}}\mu(d)\log\ell
  +O_A(N/L^A).
\tag{1}
\]
There is no extra endpoint roughness test in this outer identity. It keeps the raw paired coefficients, their parity, both strict cutoffs and the noncentral support. The long even-endpoint sum in (1) still needs a signed lower bound.

## A determinant estimate with both squarefree masks

The ordered region is a union of fixed rectangular bin restrictions in \(q,h\), with \(qh<N\) and both \(q,h\) of size \(N^{1/2+o(1)}\). Work first with a signed factor \(\mu(h)\) and an amplitude having a fixed power of \(L\) as a bound for its normalized derivatives. In particular the amplitudes below use \(\log h,\log q,\log n\) after trimming \(n\ge N/L^C\). Each sum in this proof is at a fixed \(N\).

For the small-divisor sum \(d\le P\), start from \(d\mid n\) and the two squarefree masks. Open
\[
 \mu^2(q)=\sum_{a^2\mid q}\mu(a),\quad
 \mathbf1_{(q,h)=1}=\sum_{c\mid(q,h)}\mu(c),\quad
 \mu^2(n)=\sum_{b^2\mid n}\mu(b).
\]
Every variable in a nonzero summand is odd. Truncate \(a,b,c\) at \(L^{C_1}\): if a discarded factor is \(a\) or \(c\), the product \(m\) has a square divisor \(>L^{2C_1}\); if it is \(b\), the same is true of \(n\). At most \(O(N/L^{C_1})\) products on either side satisfy these tests. For any exceptional set of \(K\) products, a fixed divisor moment and Cauchy–Schwarz give an absolute error \(O(\sqrt{KN}\,L^{C_2})\), including these opened masks and the endpoint logs. The full amplitudes have at most fixed powers of \(\tau(m)\tau(n)\) over each product. The same argument absorbs the discarded strips \(m,n\le 2N/L^C\), with smooth transitions up from \(N/L^C\). Choose the fixed powers \(C,C_1\) large enough for the requested saving. [Fixed-product moment and square-divisor tails](https://github.com/Sodelin/Research-Commons/commit/da2d8b33d1d17fda62722507cde8ac66a470e0e3)

Put \(E=[a^2,c]\) and \(r=[d,b^2]\). At fixed \(b\), aggregate the \(d\)-coefficient at \(r\) after separating \(\log(n/d)=\log n-\log d\). At most \(\tau(b^2)\) choices of \(d\) have this \(r\), since \(r/d\mid b^2\). The resulting two coefficients are bounded by fixed powers of \(L\) and \(r\le PL^{2C_1}\). At fixed \(h\) the sum over \(q\) is on \(q=E(2j+1)\) in a single \(j\)-class modulo \(r\). The congruence forces \((Eh,r)=1\). Keep odd \(h\) and \(c\mid h\) in its coefficient.

In a dyadic box with \(q\asymp X_q,\ h\asymp X_h,\ r\asymp R\), all \(X_q,X_h\) have order \(H\) up to logarithms and \(X_qX_h\ll N\). Smooth the fixed \(q\) interval edges at width \(X_q/L^J\), while leaving the \(h,r\) intervals sharp. The \(m,n\) masks are already smooth. For \(R\le X_q\), counting changed \(q\)'s and then \(h\) modulo \(r\) bounds the unweighted discrepancy by
\[
 O((X_q/L^J+1)(X_h+R)).
\]
For \(R>X_q\), count instead \(r\) in its class modulo \(q\) at fixed \(q,s=n/r\le N/R\). This is
\[
 O((X_q/L^J+1)(N/R)(R/X_q+1)).
\]
In both cases the bound is \(O(N/L^{J-O(1)}+N^{\gamma+o(1)})\), which the fixed-product moment argument absorbs after increasing \(J\). Smooth polylogarithmic dyadic partitions or sharp dyadic intervals with these edge treatments give the same conclusion.

Poisson in \(j\) gives the nonzero phase
\( (-1)^\nu e(\nu (N/2)\overline{Eh}/r)\).
The smooth amplitude has prefactor the reciprocal frequency scale \(T_0^{-1}\), where \(T_0=2ER/X_q\). Rapid integration by parts removes \(|\nu|>T_0N^\eta\) for fixed sufficiently small \(\eta>0\). On each remaining frequency box of size \(T\), separate the smooth amplitude by three-variable partial summation in normalized \(h,r,\nu\). Its normalized derivatives cost at most \(N^{O(\eta)}L^{O(1)}\) because \(|\nu|/T_0\le N^\eta\). The product of the three coefficient norms times \(T_0^{-1}\) is \(O(N^{1/2+O(\eta)}L^{O(1)})\): before the \(T_0^{-1}\) it is bounded by \(\sqrt{X_hRT}\) times logarithms. The phase parameter \(N/2\) gives a factor
\((1+(N/2)T/((EX_h)R))^{1/2}\ll N^{O(\eta)}L^{O(1)}\), as the \(m\) trim ensures \(X_qX_h\gg N/L^C\).

Apply Bettin–Chandee with inverse-variable length \(EX_h=N^{1/2+o(1)}\), denominator length \(R\le N^{\gamma+o(1)}\), and frequency length \(T\le N^{\gamma-1/2+O(\eta)+o(1)}\). Its two terms, before arbitrarily small fixed slack, are bounded by the exponents
\[
 \frac12+\frac{7}{20}(2\gamma)+\frac14\gamma
    =\frac12+\frac{19}{20}\gamma,
 \qquad
 \frac12+\frac38(2\gamma)+\frac18(2\gamma-\tfrac12)
    =\frac7{16}+\gamma .
\]
Both are strictly below \(1\) for the stated \(\gamma\). Thus the nonzero part has power saving. The zero part has the factor \(X_q/(2Er)\) times a smooth function of \(h/X_h\) with polylogarithmic size and variation. The uniform masked Möbius prefix on \((h,2r)=1,\ c\mid h\) has arbitrary log savings. Applying summation by parts, summing reciprocal \(r\), and increasing the desired saving for the finitely many log factors gives \(O_A(N/L^A)\) at zero frequency. This proves the small-divisor estimate on the actual paired outer region with squarefree \(n\). [Bettin–Chandee, Theorem 1](https://arxiv.org/abs/1502.00769) · [Exact phase, amplitude and zero mode on the upper \(q\) strip](https://github.com/Sodelin/Research-Commons/commit/df38cbba5cc981fd3e6fc8447465f2ec1a8fca63)

## Reflected endpoint parity

On squarefree \(n\), inserting \(\mu(n)\) multiplies the \(d>P\) coefficient \(\mu(d)\) by \(\mu(n)\), giving exactly \(\mu(\ell)\). Here \(\ell=n/d<N/P\). After the same squarefree-mask opening, the modulus for this sum is \(r=[\ell,b^2]\le (N/P)L^{2C_1}\), below \(X_q\) by a fixed power. Keep the exact strict \(n>P\ell\) condition. In addition to the fixed-bin smoothing, smooth this particular edge in \(n-P\ell\) at width \(N/L^J\). At fixed \(h,\ell,b\), the changed \(q\)'s lie in an interval of width \(O(N/(hL^J))\) and one progression modulo \(r\). Summing the bound \(O(N/(hL^Jr)+1)\) over the \(h\) box, the \(\ell\le N/P\) and the polylogarithmic mask indices gives
\[
 O\bigl(N/L^{J-O(1)}+N^{3/2-\gamma+o(1)}\bigr).
\]
The second exponent is strictly below \(1\). The moment bound therefore controls the full boundary discrepancy. After smoothing, all fixed derivatives cost powers of \(L\) as before. The small frequency scale \(2Er/X_q\) removes the nonzero frequencies by repeated integration by parts alone. The zero mode uses the same masked signed \(h\)-prefix. Hence the \(\mu(n)\)-twisted long-divisor contribution has arbitrary log savings. [Small-frequency mechanism on the exact fixed-target equation](https://github.com/Sodelin/Research-Commons/commit/da2d8b33d1d17fda62722507cde8ac66a470e0e3)

Proper prime powers in the original \(\Lambda(n)\) expression cost \(N^{1/2+o(1)}\), so it may start on squarefree \(n\). Expand \(\Lambda(n)=\sum_{d\ell=n}\mu(d)\log\ell\), remove \(d\le P\) by the first estimate, and use the negligible twisted long sum to insert \((1+\mu(n))/2\) and multiply the resulting sum by 2. To retain the parity of \(m\), start in the ordered region with the projector \((1+\epsilon\mu(q)\mu(h))/2\). The transpose-invariant region allows the \(\mu(q)\) term to be transposed, leaving exactly the signed factor \(-\mu(h)(\log h+\epsilon\log q)/2\). Thus every determinant estimate above applies to the two weights after the original sharp parity projection. Pairing the remaining ordered terms gives the coefficient in (1). The \(n=1\) term has zero long bracket. This proves (1) with its original sign and factor of two.

The transfer treats the full raw paired row on either block parity. Estimates that first restrict this row by its prime-factor profile use a different arithmetic mask and are separate deductions. Identity (1) gives a smaller signed expression for the full row, with no resolved lower bound for its long even-endpoint sum. This is a hand proof at fixed \(N\), with no new Lean or numerical check.
