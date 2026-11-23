# A small grouped base and repeated prime powers in Goldbach Type II

This is a hand deduction on the pinned fixed-target Vaughan expansion. Let \(N\) be even, \(H=\sqrt N\), \(L=\log N\), and keep \(q,h\in(H/2,H]\), squarefree \(m=qh\), \((m,N)=1\), and the exact count and mark projector \(F(m)\) of the typical odd-semiprime band. The expression is over ordered \(q,h\). Keep prime \(N^{1/10}<\ell\le N^{1/8}\), the original sharp condition \(d=(N-m)/\ell>D_0=H^{20/19-\delta_0}\), and any pinned previous lower endpoint cutoff. Write \(U=N^{u_0}\), \(V=N^{v_0}\) with fixed positive \(u_0,v_0\) and \(u_0+v_0<61/152\). [Pinned Type II reduction](https://github.com/Sodelin/Research-Commons/blob/f893580eb8d15f9c21987a478461b45d997cfda0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md).

Open the divisor sum in the second Type II coefficient. The exact arithmetic equation and weight then have the form
\[
 qh+\ell uws=N,\qquad u>U,\quad w>V,
\]
\[
 \frac12 F(qh)\,\mu(h)\mu(u)\Lambda(w)\log(h/q)
             \frac{\log\ell}{\log(uws)}.
\tag{1}
\]
Here \(s\ge1\) is unrestricted except through the equation and the retained support. In particular \(d=uws\) need not be prime and the arithmetic endpoint \(n=\ell uws\) need not be squarefree. The condition \(w>V\) already implies \(ws>V\).

## Grouped-base cancellation

Fix \(P=H^{20/19-\delta_1}\), with \(\delta_1>0\) sufficiently small that \(N^{1/8}UV<P\). The entire contribution of (1) with \(\ell w\le P/U\) is \(O_A(N/L^A)\) for each fixed \(A>0\). This region includes the previously removed slice \(\ell u w\le P\), since the original \(u\) exceeds \(U\). [Pinned grouped-index removal](https://github.com/Sodelin/Research-Commons/blob/f69923e5396ebc8bb17d72c9a73a3f14dda877e3/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-central-count-and-swaps.md).

First remove \(n<N/L^B\) with error \(O_A(N/L^A)\) by the pinned endpoint divisor-moment bound, choosing fixed \(B\) in terms of \(A\). Fix a surviving \(q,h,\ell,w\) with \(\ell w\mid n\), and put \(M=n/(\ell w)\). The base condition gives \(M\ge NU/(P L^B)>1\). Both \(d=n/\ell\) and the logarithmic denominator are independent of the chosen divisor \(u\mid M\). Thus the exact identity
\[
 \sum_{\substack{u\mid M\\u>U}}\mu(u)
 =-\sum_{\substack{u\mid M\\u\le U}}\mu(u)
\]
replaces the sum over \(u>U\) by a sum over \(u\le U\) on the same base condition. In the new terms use the factor \(s=M/u\). Every grouped index \(r=\ell u w\) is now at most \(P\).

Use the pinned integral for \(1/\log(uws)\). For each integral parameter \(t\in[0,10]\), the coefficient on \(r\) is the sum of \((\log\ell)\mu(u)\Lambda(w)(uw)^{-t}\) over the stated base condition and \(\ell u w=r\), with the minus sign from the identity. There are at most five distinct eligible primes \(\ell\mid r\). At each such \(\ell\), the sum of \(\Lambda(w)\) over \(w\mid r/\ell\) is at most \(\log(r/\ell)\). Thus this coefficient is \(O(L^2)\) uniformly in \(t\), and the complementary factor carries the smooth weight \(s^{-t}\). The optional lower endpoint cutoff and the new common cutoff \(n\ge N/L^B\) are of the sharp endpoint form already allowed in the pinned transfer. The original \(d>D_0\) is automatic on this trimmed range because \(\ell\le N^{1/8}\). The determinant estimate on \(r\le P\) therefore bounds the transformed sum by \(O_A(N/L^A)\). [Pinned smooth-factor and sharp-endpoint transfer](https://github.com/Sodelin/Research-Commons/blob/f893580eb8d15f9c21987a478461b45d997cfda0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md#determinant-transfer-with-the-exact-masks).

## Proper powers and repeated large primes

The terms with \(w=p^j>V\), \(j\ge2\), can be removed with a fixed power saving in \(N\). Such an endpoint is a multiple of an admitted proper prime power. Since \(p^j\le N\), there are \(O(L)\) possible exponents and
\[
 \#\{n\le N:\ p^j\mid n\text{ for some }p^j>V,\ j\ge2\}
 \ll N\sum_{\substack{p^j>V,\ p^j\le N\\ j\ge2}}p^{-j}
 \ll NV^{-1/2}.
\]
For \(p>\sqrt V\), sum the geometric tail starting at \(p^{-2}\). For \(p\le\sqrt V\), the geometric sum from the first allowed \(p^j>V\) is \(O(1/V)\) per prime. Both bounds give \(O(V^{-1/2})\) after summing.

After this removal, \(w\) is prime. The terms with \(\ell^2\mid n\) or \(w^2\mid n\) also lie on a sparse endpoint set. Its size is at most
\[
 N\sum_{p>N^{1/10}}p^{-2}+N\sum_{p>V}p^{-2}
 \ll N(N^{-1/10}+V^{-1}).
\]
At each \(n\), there are at most \(d_4(n)\tau(N-n)\) expanded placements in (1), and the absolute weight of a placement is \(O(L)\). The fixed-order divisor bound makes the total weight per endpoint \(N^{o(1)}\) uniformly. All these sparse families consequently have power-saving absolute weight. They may be removed after the grouped-base argument, without asking the determinant transfer to handle their arithmetic indicators.

On the retained support \(\ell,w\) are distinct primes and \((\ell w,us)=1\). The remaining Type II sum has \(\ell w>P/U\), hence \(\ell uw>P\), with the same cutoff and original signs in (1). This controls neither the remaining signed sum nor repeated small prime factors in \(us\).

## Complement-dependent Vaughan cutoffs

One can choose the exact Vaughan identity separately at each prime \(\ell\), with real cutoffs \(U_\ell,V_\ell>1\) satisfying \(\ell U_\ell V_\ell\le P\). The first Type I coefficient is supported at indices \(\ell u\le P\) and the second at \(\ell u w\le P\). In the coefficient sums, the inequalities \(u\le U_\ell\) and \(w\le V_\ell\) are imposed within the sum over the eligible prime divisors \(\ell\) of the index. There are again at most five such primes, and the divisor sum of \(\Lambda(w)\) gives the same uniform \(O(L^2)\) bound. The standalone \(\Lambda_{\le V_\ell}(d)\) term vanishes since \(V_\ell\le P/\ell<D_0\). The determinant and endpoint arguments therefore apply to both Type I terms with the same \(q,h\) masks.

Taking \(U_\ell=V_\ell=(P/\ell)^{1/2}\) gives an equivalent signed Type II expression, up to \(O_A(N/L^A)\), with both \(u,w>(P/\ell)^{1/2}\). In this expression \(r=\ell uw>P\) holds automatically. If \(P>N^{21/40}\), the two lower thresholds are larger than \(N^{1/5}\) throughout the band. The sparse endpoint argument again permits taking \(w\) prime, distinct from \(\ell\), with \((\ell w,us)=1\), using \(V_{\min}=(P/N^{1/8})^{1/2}\) as its uniform lower bound. The exact fixed-target signed lower bound on this remaining expression is open. The deductions use arithmetic identities and the pinned hand determinant estimate. No numerical or Lean certification is used.
