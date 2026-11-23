# The signed semiprime remainder after completing the Type II divisor sum

23 November 2026. Fixed-target hand proof. This audits the signs and masks of the full-range semiprime reduction and uses the determinant estimate to remove every short reflected index. [Full semiprime reduction and strict cutoff](https://github.com/Sodelin/Research-Commons/blob/ef82e66f32ed05a21477543b6aa57c1b2bb6739a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-semiprime-cutoff-2308z.md#a-type-ii-reduction-for-the-full-semiprime-range)

## Signs and cutoff in the opened sum

Use the fixed even target \(N\), \(H=\sqrt N\), \(L=\log N\), \(P=N^{21/40}\), \(U=V=N^{1/40}\), and \(Z_1=\exp(L\sqrt{\log\log L}/\log L)\). Keep \(q,h\in(H/2,H]\), squarefree \(m=qh\), \((m,N)=1\), squarefree \(n=N-m\) with \(P^-(n)>Z_1\), and the original count and mark tests \(F_\epsilon(m)\) for block parity \(\epsilon=\mu(m)\). Let \(S_\epsilon(N)\) be the original ordered signed contribution on surviving squarefree semiprimes \(n=pr\), \(Z_1<p<r\), \(r>P\).

The ordered prime-tested weight is \(+\mu(h)\log h\log p\), from \(\mu(r)=-1\) in the original ledger weight. Replacing the large-prime test by \(\Lambda(r)/\log r\) is exact on squarefree \(n\). The last Vaughan convolution enters with a plus sign and has coefficient \(\mu(u)B_V(v)\). Opening \(B_V(v)=\sum_{w\mid v,w>V}\Lambda(w)\) sets \(v=ws\) and \(n=pwus\). Here \(p\) and \(w\) are distinct primes, with \(Z_1<p\le N/P\) and \(w>V\). The condition \(v>V\) then holds automatically. For fixed \(q,h,p,w\) with \(pw\mid n\), write
\[
 M=\frac n{pw},\qquad r=\frac np=wM .
\]
The original strict cutoff in this expansion is \(wM>P\), with denominator \(\log(wM)\). Both are fixed during any rearrangement of the divisors of \(M\). The opened \(r=wM\) can be composite. The parity of \(n\) on the opened support can be either sign.

The remaining divisor sum in each such group is
\[
 \sum_{\substack{u\mid M\\u>U}}\mu(u)
 =-\mathbf1_{M>U}\sum_{\substack{b\mid M\\b\le U}}\mu(b).                 \tag{1}
\]
For \(M\le U\) the left side is empty, including equality. On \(M>U>1\) the identity follows from \(\sum_{d\mid M}\mu(d)=0\). This gives an exact reflection before a ratio interval or a condition on the individual \(u,s\) allocations. The \(M>U\) indicator also removes the exceptional \(M=1\) case directly. The former logarithmic factors stay fixed. Only the divisor weight changes from \(+\mu(u)\) to \(-\mu(b)\). [Earlier complete-tail identity on the fixed prime band](https://github.com/Sodelin/Research-Commons/blob/581f30cc217415f438594c02cfc4f894837fe981/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-small-prime-base.md)

## A narrower exact signed remainder

Let \(D=N^\theta\) with \(21/40<\theta<10/19\) fixed. In (1) now write \(s=M/b\), the complement of the reflected divisor. The full reflected Type II sum has \(n=pwbs\), \(b\le U\), \(bs>U\), \(wbs>P\), \(Z_1<p\le N/P\) prime and \(w>V\) prime, with the masks above. Put \(R=pwb\). Let \(\mathcal R_\epsilon(D)\) be the sum over \(q<h\) on this support with \(R>D\), \(\mu(m)=\epsilon\), and \(F_\epsilon(m)=1\), with weight
\[
 -\mu(h)\mu(b)c_\epsilon(q,h)\,
            \frac{\log p\,\log w}{\log(wbs)},\qquad
 c_{-1}=\log(h/q),\quad c_{+1}=\log(qh).                              \tag{2}
\]
Then for every fixed \(A>0\),
\[
  S_\epsilon(N)=\mathcal R_\epsilon(D)+O_{A,\theta}(N/L^A).             \tag{3}
\]
The factor \(c_\epsilon\) comes from adding the two ordered placements at \(q<h\), using \(\mu(q)=\epsilon\mu(h)\). The pairs are distinct because \(m\) is squarefree. There is one term per \(q,h\) orbit for each \(p,w,b,s\) placement. In the original even-endpoint lower budget the factor of two on \(E_{d,+}\) is external to (2).

The reflected support in (2) implies the strict size restrictions
\[
 D/U<pw<N/U,\qquad 1<s<N/D,\qquad s>U/b .
\]
In particular \(pw>D/U>H\). For \(D=N^{799/1520}\), the lower bound on \(pw\) is \(N^{761/1520}\) and \(s<N^{721/1520}\). The original cutoff \(wbs>P\) still holds. The sign in (2) is adverse precisely when \(\mu(h)\mu(b)=+1\). The expanded endpoint parity is \(\mu(n)=\mu(b)\mu(s)\). The original prime-tested endpoint parity is \(+1\), while the expansion in (3) uses both values.

## Removing the short reflected index

The proof of (3) remains to bound \(R\le D\) in the exact reflected expression. Work with ordered \(q,h\), keeping the weight \(-\mu(h)\mu(b)\log h\,\log p\log w/\log(wbs)\), and use \(\tfrac12(1+\epsilon\mu(m))\) for the block parity. The mask \(F_\epsilon(m)\) stays fixed while expanding this projector. All conditions on \(p,w,b\), including \(R\le D\), are on the coefficient side. Consequently any further bounded restriction on those three variables also fits this estimate.

The sharp thresholds on \(r=wbs\) and \(M=bs\) can both be separated by Fourier inversion in their logarithms. Smooth each step from the inside over log width \(\eta=L^{-J}\) with fixed large \(J\). The exception at \(r=P\) is contained in \(O(\eta N+N/P)\) candidate pairs \((p,r)\) with \(p\le N/P\). The exception at \(M=U\) is contained in \(O(\eta N+N/U)\) candidate pairs \((g,M)\) with \(g=pw\le N/U\). Indeed the intervals have lengths \(O(\eta P)\) and \(O(\eta U)\); this counts the rounding cost as well. Exact equality at either cutoff remains excluded by the inside smoothing. The number of placements at a given \(n\), including factorizations of \(g,M\) and of \(N-n\), is bounded by fixed powers of the two divisor counts. Cauchy–Schwarz and their fixed moments give arbitrary logarithmic savings on both discrepancies. This uses \(U\) and \(P\) of fixed polynomial size.

Include \(1/\log r\) in the smooth function of \(\log r\) and cut both functions smoothly above \(L\), past their actual arguments. The two transforms have polylogarithmic absolute mass and arbitrarily log-small tails past fixed powers of \(L\), by repeated integration by parts. At retained frequencies \(\alpha,\gamma\), the two factors separate exactly:
\[
 r^{2\pi i\alpha}M^{2\pi i\gamma}
    =(wb)^{2\pi i\alpha}b^{2\pi i\gamma}s^{2\pi i(\alpha+\gamma)} .
\]
The last factor is smooth in the normalized \(s\) coordinate of each dyadic box. The coefficient on \(R=pwb\) includes the first two factors and \(-\mu(b)\log p\log w\). Its absolute value is at most
\[
 \left(\sum_{p\mid R}\log p\right)\left(\sum_{w\mid R}\log w\right)
 \le (\log R)^2 .
\]
Here both sums are over primes. Put squarefreeness, roughness and \((R,N)=1\) in that coefficient, and open the squarefree, rough and coprimality masks of \(s\) as in the audited determinant argument on \(qh+Rs=N\). Its zero mode uses the uniform signed \(h\) prefix and the reciprocal combined periods. Its nonzero modes accept an arbitrary coefficient of this size on the sparse \(R\) positions. The fixed bound \(R\le N^\theta\), \(2\theta<20/19\), gives power slack. In the \(\mu(m)\)-twisted term the \(q,h\) swap restores the signed \(h\) variable and moves \(\log h\) to the smooth variable. All scale cuts and phases on the endpoint survive. Integrating over the two Fourier frequencies proves the required \(O_{A,\theta}(N/L^A)\) estimate. The strict \(R>D\) complement keeps the original unsmoothed thresholds \(wbs>P\) and \(bs>U\). [Determinant power range and mask uniformity](https://github.com/Sodelin/Research-Commons/commit/5ea16bc7f76f066d04b5077764ec67c57cf715ab)

## Which groups still carry a sign

If \(pw>D\), every \(b\le U\) is included in (2). Let \(C\) be the product of the primes of \(M\) at most \(U\), with empty product one. When \(1<C\le U\), the short divisor sum is the complete divisor sum on \(C\) and vanishes. When \(C=1\), only \(b=1\) survives and the reflected divisor weight is \(-1\). For \(C>U\), the sum remains incomplete. When \(D/U<pw\le D\), the actual additional lower cutoff is \(b>D/(pw)\), so the full small-prime product test alone gives no cancellation there. [Related complete-tail calculation on the earlier prime band](https://github.com/Sodelin/Research-Commons/blob/ef82e66f32ed05a21477543b6aa57c1b2bb6739a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-complete-tail-and-inner-reflection.md#exact-zero-for-a-complete-tail-with-one-small-prime-product)

At fixed \(q,h,p\) one can also sum the von Mangoldt prime first. Put \(r=n/p\). The exact coefficient multiplying \(\mu(h)c_\epsilon(q,h)\log p/\log r\) in (2) is
\[
 -\sum_{\substack{b\mid r\\b\le U}}\mu(b)
  \sum_{\substack{w\mid r,\ w\ {\rm prime}\\
       \max(V,D/(pb))<w<r/U}}\log w .
\]
Here \(w>V=U\) and \(b\le U\) ensure \(w\nmid b\). The upper edge \(w<r/U\) comes from \(M>U\), and the lower edge \(w>D/(pb)\) comes from \(R>D\). Both edges are strict. When \(r\) has exactly one prime \(t\le U\), the divisor coefficient is the difference between the intervals for \(b=t\) and \(b=1\). It is a nonnegative sum over prime divisors \(w\) with \(D/(pt)<w\le D/p\) and the same \(V<w<r/U\). The prefactor still carries \(\mu(h)\).

Even endpoint parity in the opened expression permits both aggregate signs at fixed \(M\). For example, at \(U=10\) the divisor tail in (1) is \(+1\) for \(M=3\cdot7\) and \(-1\) for \(M=11\cdot13\), with \(\mu(M)=+1\) in both examples. These are algebraic examples for the divisor weight. The remaining fixed-target lower bound concerns the signed correlation in (2), including both the complete \(pw>D\) groups that survive this test and the groups with \(D/U<pw\le D\). The independently chosen fixed-band stress expansion has its own cutoffs and square. [Related fixed-band stress expansion](https://github.com/Sodelin/Research-Commons/blob/f4aa6c2ba575353f40bbff10c0b39995f137f189/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rebalanced-expansion.md)

## Evidence and review

The previous boundary estimate is uniform in the relative width and costs \(O(\eta\varphi(N)+N^{9/10})\) on \(P<r\le(1+\eta)P\). A separate peer checked its moving rectangle and the Fourier separation of the strict cutoff in the previous semiprime reduction. The extra reflected-index estimate (3) is a hand proof with independent review pending.

An exact-integer check used the squarefree \(M\le512\) and integer or half-integer cutoffs, including equality at \(M=U\) and at the new index cutoff. It passed 2,820 strict divisor-tail checks, 16,920 strict index splits, and 16,108 paired sign comparisons. Rational arithmetic checked the displayed powers of \(N\). These finite checks concern only the algebra and exponent arithmetic. Lean status is unformalized.
