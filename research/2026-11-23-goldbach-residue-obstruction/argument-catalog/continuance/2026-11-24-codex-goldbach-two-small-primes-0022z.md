# A fixed-target charge for the residual with exactly two small primes

24 November 2026. Reference GB-TWO-SMALL-PRIMES-0022. Hand proof on the original positive Type II strip and its original square and masks. This removes the branch with exactly two primes at most \(N^{1/100}\) in \(r=d/w\) from the unbounded group loss. [Original two gap exclusions](https://github.com/Sodelin/Research-Commons/blob/c44fa72ccea39f009cdbad6cca195a058d9e2da8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-prime-gaps-2310z.md) · [One-small-prime charge and the deeper sieve](https://github.com/Sodelin/Research-Commons/blob/b012ad2a792969d8a7fab05c30d0be171af02d1a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-24-codex-goldbach-single-small-prime-0009z.md)

## Exact support and result

Let \(N=2^k\), \(L=\log N\), \(H=\sqrt N\), \(\beta=1/100\), and \(A=L/20,\ B=L/10\). Keep the original ordered odd-\(qh\) support \(H/2<q<h\le H\), \(m=qh\) odd and squarefree with \(\mu(m)=-1\), its original count and mark mask and the original moving cutoff. The expanded endpoint \(n=N-m=\ell uws\) stays squarefree and \(Y_0=\exp(L^{.005})\)-rough. Keep primes \(N^{1/10}<\ell\le N^{1/8}\), \(w>N^{1/5}\), the strict \(\ell w>N^{13/40}\), \(u>N^{1/5}\), \(d=uws>N^{21/40}\), and \(A\le\rho=\log(u/(ws))\le B\).

In each fixed \((q,h,\ell,w)\) group, let \(p_1<p_2<p_3<\cdots\) be the primes of \(r=d/w\). Keep the original short-cofactor exclusion and select the residual
\[
 z<p_1<p_2\le N^\beta<p_3,\qquad
 p_2\le N^{f_1(t)},\qquad p_3\le N^{f_2(\sigma)},\qquad
 t=\log p_1/L,\quad\sigma=\log p_2/L,
\]
where \(f_j(x)=\gamma_j(x/\beta)^{1/4}\), \(\gamma_1=7/160,\ \gamma_2=1/25\). Put \(\mathcal D_2(N)\) equal to the negative group mass on precisely this branch. Then
\[
 2\mathcal D_2(N)\le N/37
\tag{1}
\]
for every sufficiently large power of two. The same cap holds on the doubled absolute group mass. Imposing any interval of width \(\Delta\) on \(\log p_3\) gives the alternative absolute bound \(O(N(1+\Delta)/L+N^{789/800+o(1)})\). In particular, any such interval of width \(o(L)\) has \(o(N)\) total weight, uniformly in its location. Both statements cover both expanded endpoint parities.

## Exactly one possible survivor for each allocation of the other primes

Since \(p_3>N^\beta\), \(\sigma>\sigma_*=\beta(\beta/\gamma_2)^4=1/25600\). Failure of the first gap gives \(t\ge g(\sigma)=\beta(\sigma/\gamma_1)^4\). Thus \(t>g(\sigma_*)=1/157351936000000\). These fixed positive exponent bounds give \(p_1>z^2\) eventually for the growing-depth square. All prime factors of \(n\) exceed \(z\), so the square equals one.

Trim \(n<N/L^C\) for sufficiently large fixed \(C\) by the same fixed-target divisor moments as in the one-small-prime proof. The absolute trim is \(O_J(N/L^J)\) for any prescribed \(J\), and the strict \(u\) edge is then automatic on admitted ratios. Write \(r=p_1p_2ab\) with \(a,b\) free of primes at most \(Y=N^\beta\). At each fixed placement of \(p_2\) and of the remaining factors \(a,b\), pair the two allocations of \(p_1\). A complete pair cancels exactly. In the lower edge \(p_1\mid u\) and \(A\le\rho<A+2\log p_1\). In the upper edge \(p_1\mid s\) and \(B-2\log p_1<\rho\le B\). The common positive weight is \(\log(h/q)\log\ell\log w/\log d\); the sign with marks \(p_i\) placed in \(u\) when \(\epsilon_i=1\) is \(\mu(h)\mu(a)(-1)^{\epsilon_1+\epsilon_2}\).

Measure the ratio with the placement of \(p_1\) removed. In this coordinate the two edge intervals are \([A-\log p_1,A+\log p_1)\) and \((B-\log p_1,B+\log p_1]\). Switching \(p_2\) increases the coordinate by \(2\log p_2>2\log p_1\), which exceeds either interval's width. A shift from the lower interval to the upper would require \(2(\log p_1+\log p_2)> B-A\). But \(2(t+\sigma)\le4\beta<1/20\). At most one signed term remains across these four placements for each fixed \(a,b\). The short-cofactor test is common within each \(p_1\) pair. All estimates that drop any original masks below do so on the absolute upper sum after this pairing. [Exact edge signs from the previous proof](https://github.com/Sodelin/Research-Commons/blob/b012ad2a792969d8a7fab05c30d0be171af02d1a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-24-codex-goldbach-single-small-prime-0009z.md#exact-cancellation-before-the-estimate)

## Deep upper square with both actual primes

Take \(M=\ell w p_1p_2b\), so \(a=(N-qh)/M\). Using \(v=ws\), write \(M=\ell v p_1^{\epsilon_1}p_2^{\epsilon_2}\). Thus \(M\le N^{43/80+2\beta}\). Use the depth-three auxiliary upper square of level \(D=Y^3\) on \(a\), omitting \(2,p_1,p_2\). The omitted odd primes cost a relative \(O(1/p_1+1/p_2)=o(1)\) in the denominator by writing the indices divisible by one prime as that prime times a coprime index. All other factors of \(M\) exceed \(Y\).

The pinned full-modulus completion applies to \(qh\equiv N\bmod M[d_1,d_2]\) with \(q,h\) still odd. At fixed \(M\) the error is \(N^{o(1)}(D^3\sqrt M+HD/\sqrt M)\). Each representation of \(M\) by the displayed factors is a divisor choice of subpower multiplicity. The two summed error exponents, including all marks, are
\[
 (3/2)(43/80+2\beta)+9\beta=741/800,\qquad
 1/2+(43/80+2\beta)/2+3\beta=647/800.
\]
The ordered \(\log(h/q)\) weight gives normalized area \(J=3/8-\log2/2\), and the odd progression density is \(1/4\). Write \(\Pi=\prod_{p>2}(1+1/(p(p-1)))\) with product over primes. The level-\(Y^3\) denominator is \((\Phi_3+o(1))\log Y/(2\Pi)\) with
\[
 \Phi_3\ge 1+10\log(3/2)-3\log3>879/500.
\]
Consequently the positive main term at each \(M\), including the ordered log weight, is at most \(N(J+o(1))\varphi(M)(2\Pi+o(1))/(4M^2\Phi_3\beta L)\). [Pinned inclusion–exclusion, coefficient norm and completion details](https://github.com/Sodelin/Research-Commons/blob/b012ad2a792969d8a7fab05c30d0be171af02d1a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-24-codex-goldbach-single-small-prime-0009z.md#the-auxiliary-square-at-level-y3)

## The prime window clipped by \(\ell w>N^{13/40}\)

Set \(x=\log\ell/L\), \(y_0=13/40-x\), and \(B_b=\log b/L\). The base condition requires \(\log w>y_0L\), which includes \(w>N^{1/5}\) since \(x\le1/8\). For the lower and upper edges respectively put \(c_A(x)=3/20+x/2,\ c_B(x)=1/8+x/2\). At a fixed edge \(E\) and placement \(\epsilon_2\), let \(C_E=c_E(x)-(1-\epsilon_2)\sigma\). The exact identity
\[
 2\log w=\log n-\log\ell-\rho-2\log b
             -2(1-\epsilon_1)\log p_1-2(1-\epsilon_2)\log p_2
\]
together with \(N/L^C\le n<N\) bounds the length of the \(w\) log interval by
\[
 L\min(t,(C_E-B_b)_+)+O(\log L).
\]
Indeed its upper endpoint before clipping is at most \(L(y_0+C_E-B_b)\). The width of its enclosing interval before clipping is at most \(tL+O(\log L)\). The original base condition retains only the part above \(y_0L\), so every surviving \(b\) satisfies \(B_b<C_E\). This works at the upper edge as well, where the \(2\log p_1\) shift of the ratio cancels the \(p_1\) in \(s\). The prime harmonic log weight on this interval is bounded by its length plus \(O(1)\) by Mertens.

Use the identity \(\min(t,(C_E-B_b)_+)=\int_0^t\mathbf1_{B_b\le C_E-y}\,dy\), where changing inclusion at the integration endpoint does not change the integral. Summing reciprocals of squarefree \(Y\)-rough \(b\) uses \(\mathcal H(u)\le(4/7)(u+1)\) for \(u\ge1\). The range of \((C_E-y)/\beta\) is compact and above 1. The summed \(b,w\) bound is therefore
\[
 \frac47 L\left[t(C_E/\beta+1)-\frac{t^2}{2\beta}\right]+o(Lt).
\tag{2}
\]
Uniformity follows from \(t>g(\sigma_*)>0\) and the fixed compact exponent ranges in the rough harmonic estimate. The \(O(\log L)\) error in each \(w\) interval is multiplied by a bounded \(b\) harmonic sum. [Pinned rough harmonic limit and linear bound](https://github.com/Sodelin/Research-Commons/blob/bc292106d03065e910b8dc6d2bbca1589313169b/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rough-harmonic-cap.md#the-harmonic-mass-of-a-rough-factor)

Summing (2) over both placements of \(p_2\) and both edges gives \((4/7)L\) times \(t((2c_A+2c_B-2\sigma)/\beta+4)-2t^2/\beta\), with \(o(Lt)\) error. Use the upper main count, \(\varphi(M)/M^2\le1/M\), and \(\log d\ge(1-x)L-O(\log L)\). The prime \(\ell\) harmonic measure gives \(dx/(1-x)\). For the two actual marked primes, \(1/p_1,1/p_2\) give \(dt/t,d\sigma/\sigma\) on the region \(g(\sigma)\le t<\sigma\), \(\sigma_*<\sigma\le\beta\). These limits are uniform by a fixed mesh and Mertens on the compact positive exponent intervals. Including the external doubling gives the upper coefficient
\[
 \frac{J\Pi(4/7)}{\Phi_3\beta^2}
 \left[\left(\frac{259}{100}I_0-2I_1-I_2\right)\log(36/35)-\frac{I_0}{20}\right],
\quad
 \begin{aligned}
 I_0&=\int_{\sigma_*}^{\beta}(1-g(\sigma)/\sigma)\,d\sigma,\\
 I_1&=\int_{\sigma_*}^{\beta}(\sigma-g(\sigma))\,d\sigma,\\
 I_2&=\int_{\sigma_*}^{\beta}(\sigma^2-g(\sigma)^2)\,d\sigma/\sigma .
 \end{aligned}
\]
These three integrals are rational because \(g(\sigma)=\beta\sigma^4/\gamma_1^4\). Enclose \(J<28427/10^6,\ \Pi<649/500\) and \(\Phi_3>879/500\). The first and third inequalities use the geometric remainder for the atanh log series, and the second uses the exact prime product through 499 and tail at most \(499/498\). The same log series upper bounds \(\log(36/35)\), whose coefficient is positive. The rational upper bound is less than \(0.02691<1/37\), leaving strict slack for the \(o(1)\) and summed completion errors. This proves (1).

## Short third-prime intervals and the remaining inequality

For an interval in \(\log p_3\), mark the actual \(p_3\) as well. Now \(M=\ell w p_1p_2p_3b\le N^{43/80+2\beta+\gamma_2}\). Pair \(p_1\) with the other two placements fixed. The same auxiliary square applies as \(p_3>Y\) and the quotient is \(Y\)-rough. The summed error exponents become \(789/800\) and \(663/800\), with the remaining choices still of subpower multiplicity per \(M\). For the main bound use the rough \(b\) harmonic sum \(O(1)\), the log window \(O(\log p_1)\) of \(w\), and the bounded prime harmonics on the compact \(t,\sigma,x\) ranges. This gives \(O(N\sum_{p_3}1/p_3)\) on the selected interval. Since \(p_3>N^\beta\), Mertens bounds that harmonic sum by \(O((1+\Delta)/L)\), uniformly in the ends. This proves the stated interval charge at each target.

Let \(\mathcal D_{\ge3}\) be the original remaining negative group mass with \(p_3\le N^{1/100}\), still after both gap cuts and the short-cofactor selection. The same original budget can now use
\[
 2\mathcal D_{\ge3}(N)+\frac{11333}{133200}N
 \ \le\ M_0(N)+E_{\rm other}(N)-\eta N,\qquad
 \frac{11333}{133200}=\frac{209}{3600}+\frac1{37},
\]
for fixed \(\eta>0\) at every sufficiently large power of two. The new charge is a linear upper bound. The grouped signs in the region with at least three small primes and the original other signed rows still need a same-target estimate. An exact next target is the branch \(p_3\le N^{1/100}<p_4\), after the same first and second gap exclusions.

The analytic statements are hand proofs. Exact rational checks verified the coefficient and completion powers, and 675 rational placements at and between the boundaries verified the two-mark nonoverlap. Independent review is pending. Lean formalization remains open.
