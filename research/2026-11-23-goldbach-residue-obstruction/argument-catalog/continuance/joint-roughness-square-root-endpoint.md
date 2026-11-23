# Joint roughness at the square-root endpoint

This extends the progression sieve in the prime-only windows and asymmetric shells note to complementary divisors as large as \(\sqrt N\). It is a pointwise hand estimate.

Let \(L=\log N,\ H=\sqrt N,\ W=\exp(L^\omega)\) with \(0<\omega<\beta\). Let \(R=\exp(L^\nu)\) for fixed \(0<\nu<1\) with \(\nu\ge\delta/2\), where \(\delta=1-\beta\). One can also use the original \(R=Y=\lfloor\exp(L^{\delta/2})\rfloor\). Keep the original square-root block, middle-count mask and squarefree \(m=qh\) with \((m,N)=1\). Impose that \(q,h\) are \(W\)-rough and \(N-qh=d\ell\) is \(R\)-rough. Retain \(d>D\) in the orientation of the original summand \(-\mu(h)\mu(d)\log h\log\ell\). On \(\mu(m)=-1\), the signed contribution for \(B<\ell\le 2B\) satisfies
\[
\ll \frac{N(1+\log L)\log(2B)}{(\log W)^2(\log R)^2}+(B^{3/2}+H\sqrt B)N^{o(1)}
\tag{1}
\]
uniformly for \(R/2\le B\le N^{2/3-\epsilon}\) with any fixed \(\epsilon>0\). The case \(\ell=1\) has zero weight. Both \(N-qh\) parities and composite \(d\) are allowed. All implicit constants may depend on fixed exponents.

For each fixed \(R\)-rough \(\ell\) coprime to \(N\), count all \(q,h\in(H/2,H]\) with \(qh\equiv N\bmod\ell\). Enlarge the support for the upper count, retaining the two \(W\)-roughness tests and the \(R\)-roughness test on \(d=(N-qh)/\ell\). The base density is \(\varphi(\ell)/\ell^2\). Omit the prime 2, and for each other active prime \(p\le\max(W,R)\) define a bad event as failure of any of its active tests. If \(p\nmid\ell N\), the local survival probabilities are
\[
\begin{array}{c|c}
\text{tests} & \text{survival probability}\\ \hline
q,h,d &(1-1/p)(1-2/p)\\
q,h &(1-1/p)^2\\
d & 1-1/p+1/p^2 .
\end{array}
\]
Indeed \(q=0\) or \(h=0\) has probability \(2/p-1/p^2\), while \(qh=N\bmod p\) has probability \((p-1)/p^2\) and is disjoint from those events. For \(p\mid N\), \(p\nmid\ell\), the \(d\) bad event is \(q=0\) or \(h=0\), so the only potentially larger survival factor occurs when all three tests are active. The ratio to the generic factor is then \((p-1)/(p-2)\). If \(p\mid\ell\), \(q,h\) are already units at \(p\); the \(d\) test, if active, raises the modulus by one \(p\) and fails with conditional probability \(1/p\). In fact \(p\mid\ell\) implies \(p>R\) on this support. Missing factors from \(p\mid\ell\) are bounded uniformly by roughness. Therefore the product of survival probabilities is
\[
\ll \frac{1+\log L}{(\log W)^2\log R}.
\tag{2}
\]

Here is the error justification. Use upper Bonferroni with even truncation \(k\asymp C_A\log L\), applied to the bad events indexed by primes. The active bad primes are coprime to \(\ell\), since \(p\mid\ell\) implies \(p>R\) and \(q,h\) are already units at \(p\). An intersection indexed by a squarefree product \(e\) is a union of at most \(e^2\) residue pairs \((a,b)\bmod e\). On each, write \(q=a+eu,\ h=b+ev\). Since \((e,\ell)=1\), shifts in \(u,v\) reduce the congruence to a modular hyperbola with right-hand side \(Ne^{-2}\bmod\ell\), a unit. The main term per box is \((H/(2e))^2\varphi(\ell)/\ell^2\). The two intervals each split into full periods modulo \(\ell\) and one remainder. Full-period pairs are exact. For a full period against a remainder, the count is the number of units in that remainder, with error \(O(\tau(\ell))\) by inclusion–exclusion. For two remainders the rectangular Kloosterman estimate gives \(O(\ell^{1/2+o(1)})\). Thus the error per residue pair is \(O(\ell^{1/2+o(1)}(1+H/\ell))\), including rounding. The CRT gives exactly the product of bad densities in the summed main term.

There are \(N^{o(1)}\) terms over the entire truncation since \(e\le\max(W,R)^k=N^{o(1)}\), even counting the residue pairs. In the independent local model, consecutive Bonferroni truncations differ by at most \((\sum_p\Pr(\mathrm{bad}_p))^{k+1}/(k+1)!\), which is \(O_A(L^{-A})\) for large enough \(C_A\) since the mean is \(O(\log L)\). This proves (2) times the base main count, plus the hyperbola error. [Estermann’s composite-modulus bound](https://doi.org/10.1112/S0025579300002187) · [Shparlinski, fixed-rectangle equation (10)](https://arxiv.org/pdf/1103.2879).

Summing over rough \(\ell\) in the shell gives \(\sum\varphi(\ell)/\ell^2\ll1/\log R\). Indeed, at \(B\ge R/2\), the upper sieve at \(\min(R,B^c)\) for sufficiently small fixed \(c>0\) gives \(O(B/\log R)\) choices. The errors summed over all \(\ell\) are \(O((B^{3/2}+H\sqrt B)N^{o(1)})\). Finally, on squarefree odd \(m\), reflection \(q\leftrightarrow h\) replaces \(\log h\) by \(\tfrac12\log(h/q)\) in the original signed sum, costing only \(O(\log(2B))\) for the reflected weight. This proves (1). The same count bounds the absolute weight for either parity with an extra \(L\) in the main term.

Two consequences:
- For the original \(R=Y\), any fixed \(\omega>(1-\delta)/2\) gives \(o(N)\) in every individual shell, including \(\ell\asymp H\) and individual shells up to \(B\le N^{2/3-\epsilon}\). A union of \(O(L^\tau)\) shells is \(o(N)\) whenever \(1+\tau<2\omega+\delta\).
- With additional endpoint roughness \(R=\exp(L^\nu)\), the entire oriented range \(d\ge H\), where \(\ell\le H\) has signed weight \(O(N(1+\log L)L^{2-2\omega-2\nu})+N^{3/4+o(1)}\) by dyadic summation. It is \(o(N)\) if \(\omega+\nu>1\). This requires stronger roughness than in the original project. The shell estimates alone give no such conclusion on the full original-\(Y\) range.

A separate finite check compared 225 local survival counts against the displayed formulas for primes from 3 through 19, all residues of the target, and the three active-test patterns. The estimate itself is proved by the argument above.
