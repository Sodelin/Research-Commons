# Complete divisor tails and inner-factor reflection in Goldbach Type II

**Unconditional hand proof at each even target.** Keep the exact square-root block \(q,h\in(H/2,H]\), \(H=\sqrt N\), squarefree \(m=qh\) with \((m,N)=1\), and the original projector \(F(m)\). Keep \(n=N-qh=\ell d\) squarefree and \(Y_0\)-rough, the actual prime \(N^{1/10}<\ell\le N^{1/8}\), and the strict \(d>D_0\). Write \(L=\log N\), \(U=V=N^{1/5}\), \(P=H^{21/20}\), and keep the same fixed Selberg square \(W_N(n)\). A Type II tuple has \(d=uv\), \(u>U\), and \(v>V\). Its weight is
\[
 C(q,h,\ell,d)\mu(u)B_{\ell}(v),\qquad
 C=\tfrac12 F(m)W_N(n)\mu(h)\log(h/q)\frac{\log\ell}{\log d}.
\]
With the retained base restriction \(\ell w>P/U\), use \(Q_\ell=\max(V,P/(U\ell))\) and \(B_\ell(t)=\sum_{w\mid t,\ w>Q_\ell}\Lambda(w)\). For the original expanded sum use \(Q_\ell=V\). The squarefree endpoint makes every \(w\) in either formula a prime. The two identities below concern this semiprime-origin band. The peer's separate analysis of the triple-complement center uses its own support and weights. [Pinned fixed-square expansion](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md) · [Pinned base restriction](https://github.com/Sodelin/Research-Commons/blob/581f30cc217415f438594c02cfc4f894837fe981/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-small-prime-base.md) · [Separate triple-complement center](https://github.com/Sodelin/Research-Commons/commit/bfd3f2d1281fe76fa8541279a7aef3e4949e051e).

## Exact zero for a complete tail with one small-prime product

Set \(S(d)=\prod_{p\mid d,\ p\le U}p\). For composite \(d\) on the complete Type II divisor support at fixed \(q,h,\ell,d\), the inner coefficient is exactly
\[
 \sum_{\substack{uv=d\\u>U,\ v>V}}\mu(u)B_\ell(v)
 =-B_\ell(d)\sum_{\substack{a\mid S(d)\\a\le U}}\mu(a).
 \tag{1}
\]
Indeed, open \(B_\ell(v)\) and fix an eligible prime \(w\mid d\). Then \(u\mid d/w\), the condition \(v>V\) is automatic, and \(d/w>1\). The sum over \(u>U\) is the negative of the sum over \(u\le U\) by \(\sum_{u\mid d/w}\mu(u)=0\). Since \(w>V=U\), the divisors of \(d/w\) at most \(U\) are exactly the divisors of \(S(d)\) at most \(U\). This proves (1), including any extra selection on \(w\) independent of the allocation \(u\).

When \(1<S(d)\le U\), the sum on the right vanishes. In particular every complete group with exactly one prime of \(d\) at most \(U\) contributes zero, even when that prime has polynomial size. This group identity keeps the full tail \(u\mid d/w,\ u>U\) at each \(q,h,\ell,d,w\).

For \(n\) with exactly four prime factors, \(d\) has three. With no additional \(w\) selection, its inner coefficient is \(-B_\ell(d)\) when all three primes exceed \(U\), is zero when exactly one is at most \(U\), and is \(B_\ell(d)\) when exactly two are at most \(U\) and their product exceeds \(U\). In this last case only \(u=S(d),v=d/S(d)\) can contribute, and \(\log(u/v)\le \tfrac45 L-\log d\). If the product of the two smaller primes is at most \(U\), (1) gives zero. Three primes at most \(U\) yield \(B_\ell(d)=0\).

When all three exceed \(U\), at any fixed eligible \(w\) the other two primes give exactly three admitted allocations, with signs \((-1,-1,+1)\) and magnitude \(|C|\Lambda(w)\) each. Complete grouping therefore leaves exactly one third of the termwise absolute mass and at most one half of the termwise negative mass. This comparison holds with the retained base cut. When all three are eligible, the coefficient is \(-\log d\), leaving precisely the signed \(qh+\ell p_1p_2p_3=N\) correlation with weight \(-C\log d\) and each unordered triple counted once.

## Quantitative bound when both reflected ratio strips are kept

Retain the expanded even endpoint \(\mu(n)=+1\), so \(\mu(d)=-1\). Impose any \(u,v\)-symmetric support and put \(\rho=\log(u/v)\). In particular, keep both signs of \(L/20\le|\rho|\le L/10\) in the same accounting row. The map \(u\leftrightarrow v\) preserves the thresholds since \(U=V\), the additive equation, and the strict \(d\) cutoff. Squarefreeness gives \(\mu(v)=-\mu(u)\). Thus each unordered pair of allocations contributes exactly
\[
 C\mu(u)\big(B_\ell(v)-B_\ell(u)\big).
 \tag{2}
\]
This grouping is on the \(w\)-summed weight. Its definition keeps the base cut through the same function \(B_\ell\) on each inner factor.

If every prime of \(d\) exceeds \(Q_\ell\), then \(B_\ell(t)=\log t\) for \(t\mid d\). The ratio of the absolute grouped weight to the sum of the two original absolute weights is \(|\rho|/\log d\) when the denominator is positive. After the standard endpoint trim \(n\ge N/L^B\), which costs \(O_A(N/L^A)\) for sufficiently large fixed \(B\), we have \(\log d\ge(7/8)L-B\log L\). On the double strip this yields
\[
 \sum_{\rm groups}|{\rm grouped\ weight}|
 \le \left(\frac4{35}+O_B\!\left(\frac{\log L}{L}\right)\right)
             \sum_{\rm ordered\ terms}|{\rm weight}|.
 \tag{3}
\]
The corresponding ratio for the negative mass is at most \(2|\rho|/(\log d+|\rho|)\) on each pair, since a negative grouped term has the larger of the original magnitudes on its negative side. Its upper bound is \(8/39+O_B((\log L)/L)\). These are pointwise inequalities for the stipulated strips and have the exact inherited signs.

The base-cut version also gives a constant saving when all primes of \(d\) exceed \(U\) and just one is ineligible. Let \(s=\prod_{p\mid d,\ p\le Q_\ell}p\) and \(a=(\log\ell)/L\in(1/10,1/8]\). Then \(\log s\le(13/40-a)L\), and for \(u,v\) the omitted products multiply to \(s\). Hence
\[
 \frac{|B_\ell(v)-B_\ell(u)|}{B_\ell(u)+B_\ell(v)}
 \le \frac{|\rho|+\log s}{\log d-\log s}
 \le \frac{13}{27}+O_B\!\left(\frac{\log L}{L}\right)
\]
on the same trimmed double strip. The negative-mass factor there is at most \(13/20+O_B((\log L)/L)\), by applying \(r\mapsto2r/(1+r)\) to the absolute factor. The one-sided positive stress interval can be used for the peer's ratio-edge argument. Equations (2)–(3) require both orientations in the same sum. [Pinned small-prime stress-interval grouping](https://github.com/Sodelin/Research-Commons/blob/19499a27e3024772d8874d020f4b17db94b6374d/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-negative-ratio-budget-2217z.md).
