# An explicit cap using the two least-prime ratio edges

23 November 2026. Unconditional hand proof at powers of two. Reference ID GB-TYPE-II-EDGE-CAP-2246. Keeping the least prime fixed permits an explicit charge for the terms that survive its sign change. This sharpens the direct roughness bound on the same positive Type II stress interval. [Pinned exact expansion and grouping](https://github.com/Sodelin/Research-Commons/blob/38ef35f193f2098942b64baf461128a06278482f/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-negative-ratio-budget-2217z.md) · [Pinned very rough cap](https://github.com/Sodelin/Research-Commons/blob/b8d0afa3e5fab3380f662ce172eacad56ea05316/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-rough-negative-cap-2234z.md)

## Statement and exact signed edges

Write \(N=2^k\), \(L=\log N\), \(H=\sqrt N\), \(m=qh\), \(n=N-m=\ell uws\), \(v=ws\) and \(d=uv\). Keep the paired odd-\(m\) support \(H/2<q<h\le H\), squarefree \(m\) coprime to \(N\), and the original count and mark projector \(F(m)\). Keep squarefree \(Y_0\)-rough \(n\), the same polynomial Selberg square \(W_N(n)\) with indices at most \(N^\kappa\) and primes at most \(N^\delta\), prime \(N^{1/10}<\ell\le N^{1/8}\), prime \(w>N^{1/5}\), \(u>N^{1/5}\), and the original strict \(d>D_0\). Any prior restriction on \(\ell,w\) or \(n\) stays in the definition. Use the positive ratio interval \([A,B]=[L/20,L/10]\). The two Möbius signs in the opened term are \(\mu(h)\mu(u)\) and its weight is

\[
F(m)W_N(n)\mu(h)\mu(u)\log(h/q)\frac{\log\ell\log w}{\log d}.
\]

Let \(r=d/w\). Write \(G_{q,h,\ell,w}\) for the exact subtotal over \(u\) in this group and \(x_-=\max(0,-x)\). Put \(J=3/8-(\log 2)/2\), \(\Pi=\prod_{j>2,\ j\ {\rm prime}}(1+1/(j(j-1)))\). For fixed \(\min(\kappa,\delta)\le\alpha\le 1/40\), \(\alpha>0\), the new bound is

\[
2\sum_{N^\alpha<P^-(r)\le N^{1/25}}(G_{q,h,\ell,w})_-
\le N\left[
\frac{17 J\Pi}{1400}\left(\frac1\alpha-\frac{136}{5}\right)+o(1)
\right].
\tag{1}
\]

The factor of two is the one in the exact remainder budget. Together with the direct rough cap above \(N^{1/25}\), (1) gives a doubled charge at most \(N/25\) for **all** \(P^-(r)>N^{1/100}\) at every sufficiently large power of two. The old square satisfies \(\kappa<1/100\), so this conclusion uses the same weights.

To prove (1), trim \(n<N/L^{B_0}\) at arbitrary log saving by the pinned divisor moments, for sufficiently large fixed \(B_0\). On the remaining part any \(\rho=\log(u/v)\) in \([A,B]\) gives \(u\ge N^{37/80}/L^{B_0/2}>N^{1/5}\). The \(v\) cutoff is automatic since \(w>N^{1/5}\). Fix the group and let \(p=P^-(r)\), \(r=pab\). Here \(a\) runs over divisors of \(r/p\), and \(b=r/(pa)\). Fix \(a,b\) and let \(T=\log p\), \(R=\log(a/(wb))\). The two choices for \(u\) are \(a\) and \(pa\). Their signs are \(\mu(a)\) and \(-\mu(a)\), and their ratios are \(R-T\) and \(R+T\), respectively. Every other factor of the term stays fixed. Thus the exact signed difference in this pair is the fixed coefficient times

\[
\mu(a)\bigl(\mathbf 1_{I_+(p)}(R)-\mathbf 1_{I_-(p)}(R)\bigr),
\quad
I_\pm(p)=[A\pm T,B\pm T]\setminus[A\mp T,B\mp T].
\tag{2}
\]

The set differences preserve the closed original ratio edges. Each interval has length \(\min(2T,B-A)\). The grouped negative part is bounded by the sum of the absolute weights of the surviving terms in (2). The exact sign formula keeps both parities of the expanded \(n\).

## Counting at a modulus that includes \(p\)

Write \(t=(\log p)/L\) and \(e(t)=\min(t,1/40)\). Since \(p>N^\alpha\), all primes of \(n\) exceed the smaller of the two old index and prime cutoffs. Thus the original \(W_N(n)=1\) here. Both \(a,b\) are free of primes at most \(p\). Fix \(\ell,w,p,b\) and use \(M=\ell wpb\), so \(a=(N-qh)/M\). On \(I_+\) the admitted term has \(v=wpb\), and \(M=\ell v\le N^{43/80}\). On \(I_-\) it has \(v=wb\), and \(M=p\ell v\le N^{43/80+1/25}=N^{231/400}\). The same \(\ell v\) bound follows directly from \(\rho\ge L/20\), \(\ell\le N^{1/8}\), and \(v^2=n e^{-\rho}/\ell\).

On \(I_-\) one has \(b\le N^{9/40}\) from \(v\le N^{17/40}\) and \(w>N^{1/5}\). On \(I_+\) the actual ratio \(R-T\) is at least \(\max(A,B-2T)\), and \(b=v/(wp)\). Using \(\ell>N^{1/10}\) gives \(b\le N^{1/5}\) for \(t\le1/40\), since the increase \(tL\) in the allowed \(\log v\) is canceled by \(\log p\) in \(v/(wp)\). For \(t\ge1/40\) the bound is \(b\le N^{9/40-t}\le N^{1/5}\). Consequently the two \(b\) reciprocal sums are bounded by

\[
\sum_{\substack{b\le N^{c_\pm}\\P^-(b)>p}}\frac1b
\le \prod_{p<j\le N^{c_\pm},\ j\ {\rm prime}}(1-1/j)^{-1}
=\frac{c_\pm}{t}+o(1),
\qquad c_+=1/5,\quad c_-=9/40.
\]

The error is uniform for the fixed exponent interval and the sum includes \(b=1\). For fixed \(\ell,p,b\), the identity \(2\log w=\log n-\log(\ell p b^2)-R\) confines the possible \(w\)'s on each edge to a log interval of width at most \(L e(t)+O_{B_0}(\log L)\). Keeping \(w>N^{1/5}\) and using Mertens' theorem bounds \(\sum_w(\log w)/w\) by \(L e(t)+o(L)\), uniformly in all these choices.

For the roughness of \(a\) use the auxiliary Selberg square of the direct rough cap with index bound \(D_p=\min(p/2,N^{1/32})\). This strict bound below \(p\) keeps its sieve primes coprime to \(M\). Put \(d(t)=\min(t,1/32)\), so \(\log D_p=L d(t)+O(1)\). The square has the same local densities \(g(2)=3/4\) and \(g(j)=(j-1)/j^2\) at odd primes. The fixed-\(M\) main upper count weighted by \((\log(h/q))_+\) is

\[
N(J+o(1))\frac{\varphi(M)}{M^2}\frac{\Pi}{2L d(t)}.
\]

In this positive count the original count, mark and squarefree tests may be relaxed after fixing the exact support above. The pinned completion and Selberg normalization use only \(M\) odd and coprime to all auxiliary sieve primes. The grid for the log weight has \(O(L^2)\) rectangles. For fixed \(M\) the error is \(N^{1/8+o(1)}(M^{1/2}+H/M^{1/2})\), since opening the square and enumerating CRT residues costs at most \(D_p^4N^{o(1)}\). At most \(d_4(M)=N^{o(1)}\) quadruples give a fixed \(M\). Keep the cap \(M\le N^{231/400}\) during completion. Summing all errors, including both edges and the log weights, gives

\[
N^{793/800+o(1)}+N^{731/800+o(1)}=o(N).
\]

The proof of the main count and its reciprocal Euler constant is the same one-dimensional calculation at \(D_p\) in the pinned rough cap. Its denominator has an \(O(1)\) error as a function of \(D_p\), which is uniform here because \(D_p\gg N^{\min(\alpha,1/32)}\). [Pinned sieve count and constant](https://github.com/Sodelin/Research-Commons/blob/b8d0afa3e5fab3380f662ce172eacad56ea05316/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-rough-negative-cap-2234z.md#sieve-at-the-modulus-ell-ws)

## Summing the explicit charge

Use \(\varphi(M)/M\le1\) in the nonnegative main term. The remaining factors are \(1/(\ell wpb)\). Also \(\log d\ge (7/8)L-B_0\log L\) and \(\sum_\ell (\log\ell)/\ell=L/40+o(L)\). After taking the two reciprocal \(b\) bounds and the separate prime-\(w\) bounds, the doubled main charge divided by \(N\) is at most

\[
\frac{17J\Pi}{1400}
\sum_{N^\alpha<p\le N^{1/25}}\frac{e(t)}{p\,t\,d(t)}+o(1).
\]

Here \(17/1400=(8/7)(1/40)(c_++c_-)\). The prime sum converges by Mertens and partial summation to \(\int_\alpha^{1/25}e(t)/(t^2d(t))\,dt\). For \(\alpha\le1/40\) the integral is

\[
\int_\alpha^{1/40}\frac{dt}{t^2}
+\frac1{40}\int_{1/40}^{1/32}\frac{dt}{t^3}
+\frac45\int_{1/32}^{1/25}\frac{dt}{t^2}
=\frac1\alpha-\frac{136}{5}.
\]

This proves (1). To combine it with the direct rough cap, use the constant \((45/448)J\Pi\) above \(N^{1/25}\). The full doubled charge for \(P^-(r)>N^\alpha\) on this stress strip is at most

\[
N\left[
J\Pi\left(\frac{17}{1400}\left(\frac1\alpha-\frac{136}{5}\right)+\frac{45}{448}\right)+o(1)
\right].
\tag{3}
\]

All primes in \(\Pi\) are odd, so \(\Pi\le\exp(\sum_{j\ge3,\ j\ {\rm odd}}1/(j(j-1)))=\exp(1-\log 2)=e/2<34/25\). With \(J<29/1000\), the coefficient in (3) at \(\alpha=1/100\) is less than \(1/25\). An exact-rational check verifies both scale exponents, the integral and this constant inequality. For a fixed square satisfying \(\min(\kappa,\delta)\le1/200\), (3) also gives a charge below \(N/11\) for \(\alpha=1/200\).

## Remaining same-target inequality

On the unchanged exact strip the subpower range \(P^-(r)\le\exp(\sqrt L)\) has \(o(N)\) negative loss. Let \(\mathcal D_{\rm mid}\) sum the grouped negative parts for \(\exp(\sqrt L)<P^-(r)\le N^{1/100}\). The available bound gives the sufficient condition

\[
2\mathcal D_{\rm mid}(N)+N/25
\le M_0(N)+E_{\rm other}(N)-\eta N
\]

for fixed \(\eta>0\) at every sufficiently large power of two. Here \(M_0\) is the comparison term and \(E_{\rm other}\) collects the signed rows outside this doubled stress interval. The estimate in (3) grows like \(1/\alpha\) as \(\alpha\) decreases. The next step requires signed information about (2) at lower primes or an estimate using the actual suppression from \(W_N\) there.

The parallel proof removes small-prime endpoints from the complete signed divisor bracket, where every admissible divisor shares the product masks. This allows moving from the long side of the bracket to its short side. In the selected Type II interval \(\ell\) stays an actual fixed prime and only one ratio orientation is retained. The two ratio boundaries survive as in (2). [Pinned complete-center proof and its scope](https://github.com/Sodelin/Research-Commons/blob/5ea16bc7f76f066d04b5077764ec67c57cf715ab/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-goldbach-composite-completion-2245z.md)
