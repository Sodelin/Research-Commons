# Opposite-edge cancellation with exactly three small primes

24 November 2026. Reference GB-THREE-SMALL-PRIMES-0034. This is a hand proof at each sufficiently large power of two, on the original Type II ratio residual. Moving the second and third primes together cancels an exact overlap of the two ratio edges. The resulting bound on the doubled negative group mass in this branch is \(27N/500\). [Original gap ledger](https://github.com/Sodelin/Research-Commons/commit/c44fa72ccea39f009cdbad6cca195a058d9e2da8) · [Two-small-prime charge and clipped prime interval](https://github.com/Sodelin/Research-Commons/commit/a407395d23e2a193a67695b3b463d508b87e9ead)

## Original support

Let \(\beta=1/100,\ L=\log N,\ H=\sqrt N\), and \(A=1/20,\ B=1/10\) in normalized log-ratio coordinates. Keep \(H/2<q<h\le H\), odd squarefree \(m=qh\) with \(\mu(m)=-1\), the original moving cutoff and the original count and mark projector. Keep \(n=N-qh=\ell uws\) squarefree and \(\exp(L^{.005})\)-rough. The actual primes and cutoffs are \(N^{1/10}<\ell\le N^{1/8}\), \(w>N^{1/5}\), \(\ell w>N^{13/40}\), \(u>N^{1/5}\), and \(d=uws>N^{21/40}\). Keep \(\rho/L\in[A,B]\), \(\rho=\log(u/(ws))\), and group at fixed \((q,h,\ell,w)\).

Put \(r=d/w\), and keep the original short-cofactor exclusion and both gap exclusions. The new branch is
\[
 z<p_1<p_2<p_3\le N^\beta<p_4,\qquad
 p_2\le N^{f_1(t)},\qquad p_3\le N^{f_2(\sigma)},\qquad
 (t,\sigma,\tau)=L^{-1}(\log p_1,\log p_2,\log p_3).
\]
Here \(f_j(x)=\gamma_j(x/\beta)^{1/4}\) with \((\gamma_1,\gamma_2)=(7/160,1/25)\), and a missing \(p_4\) is assigned infinity. Write \(r=p_1p_2p_3ab\), where \(a,b\) partition the remaining factors. They are squarefree and \(N^\beta\)-rough. The original Selberg weight is one. Both expanded endpoint parities are retained.

## The exact opposite-edge pair

Trim \(n<N/L^C\) at arbitrary logarithmic saving by the pinned fixed-target divisor moments. On the remaining support an admitted ratio implies \(u>N^{1/5}\). For each fixed \(a,b\), assign \(\epsilon_i=1\) if \(p_i\) is placed in \(u\), and set
\[
 X=L^{-1}\log\frac{a}{wb p_2p_3},\qquad
 \frac{\rho}{L}=X+(2\epsilon_1-1)t+2\epsilon_2\sigma+2\epsilon_3\tau.
\]
The sign is \(\mu(h)\mu(a)(-1)^{\epsilon_1+\epsilon_2+\epsilon_3}\), and the magnitude is the same throughout this group. The short-cofactor test is constant within each \(p_1\) pair. Pairing \(p_1\) leaves the lower edge \(X+2\epsilon_2\sigma+2\epsilon_3\tau\in[A-t,A+t)\) with \(\epsilon_1=1\), and the upper edge with that coordinate in \((B-t,B+t]\) with \(\epsilon_1=0\).

The possible shifts of that coordinate are \(0,2\sigma,2\tau,2(\sigma+\tau)\). Any difference except the full shift is at most \(2\tau\le 2\beta\), which is smaller than \((B-A)-2t\). Thus the two edges can both be occupied only by the lower placement \((1,0,0)\) and upper placement \((0,1,1)\). For these two to be admitted requires \(t+\sigma+\tau>1/40\), hence \(t>1/200\). Since \(\log z=o(L)\), this gives \(p_1>z^2\) for all sufficiently large \(N\), so both pass the short-cofactor test. The two signs are opposite and their weights cancel exactly. The intermediate shifts cannot survive at either edge when the two extreme placements survive, since their distances from the respective extreme shifts are greater than \(2t\).

Put
\[
 \lambda=\min(t,1/40-\sigma-\tau),\qquad
 \delta=t-\lambda=(t+\sigma+\tau-1/40)_+ .
\]
When \(\delta>0\), the overlap in the base coordinate \(X\) is the open intersection of \([A-t,A+t)\) with \((B-t-2(\sigma+\tau),B+t-2(\sigma+\tau)]\). Removing it leaves the two extreme placements on \(\rho/L\in[A,A+2\lambda]\) and \(\rho/L\in[B-2\lambda,B]\), respectively. The original half-open intervals continue to apply when \(\delta=0\). The other six edge windows keep their first-prime pairing intervals. All subsequent enlargements apply to the nonnegative count after these exact cancellations. [Pinned first-prime edge mechanism](https://github.com/Sodelin/Research-Commons/blob/b012ad2a792969d8a7fab05c30d0be171af02d1a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-24-codex-goldbach-single-small-prime-0009z.md#exact-cancellation-before-the-estimate)

## Counting after the pair is removed

Use \(M=\ell wp_1p_2p_3b=\ell v\prod_{i=1}^3p_i^{\epsilon_i}\), where \(v=ws\). Since \(\ell v\le N^{43/80}\), one has \(M\le N^{43/80+3\beta}\). The upper square on the \(Y=N^\beta\)-rough \(a=(N-qh)/M\) has level \(D=Y^3\) and omits \(2,p_1,p_2,p_3\). The other factors of \(M\) exceed \(Y\). Omitting the marked odd primes costs relative \(O(1/p_1+1/p_2+1/p_3)=o(1)\) in its denominator. The full odd modulus \(M[d_1,d_2]\) gives the pinned error \(N^{o(1)}(D^3\sqrt M+HD/\sqrt M)\) at each \(M\), still with odd \(q,h\). Following divisor multiplicities and summing the two errors over \(M\) gives exponents \(753/800\) and \(651/800\). [Pinned auxiliary square and full-modulus completion](https://github.com/Sodelin/Research-Commons/blob/b012ad2a792969d8a7fab05c30d0be171af02d1a/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-24-codex-goldbach-single-small-prime-0009z.md#the-auxiliary-square-at-level-y3)

Set \(x=\log\ell/L\), \(c_A(x)=3/20+x/2\), \(c_B(x)=1/8+x/2\), and \(c=c_A+c_B=11/40+x\). For an original half-width \(t\), placement \((\epsilon_2,\epsilon_3)\), and edge \(E\), put \(C_E=c_E(x)-(1-\epsilon_2)\sigma-(1-\epsilon_3)\tau\). The strict \(\ell w\) cutoff clips the \(w\)-log interval at \((13/40-x)L\). Its length is at most \(L\min(t,(C_E-\log b/L)_+)+O(\log L)\); its prime harmonic log weight has the same bound. Summing \(1/b\) against this clipped width, using \(\mathcal H(v)\le(4/7)(v+1)\) for the squarefree rough harmonic sum, gives
\[
 \frac47 L\left[t(C_E/\beta+1)-t^2/(2\beta)\right]+o(Lt)
\]
uniformly. The rough harmonic argument lies in a fixed compact range above 1. The interval rounding error is \(o(Lt)\) because \(p_1>\exp(L^{.005})\). [Clipping identity and the uniform rough harmonic bound](https://github.com/Sodelin/Research-Commons/blob/a407395d23e2a193a67695b3b463d508b87e9ead/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-24-codex-goldbach-two-small-primes-0022z.md#the-prime-window-clipped-by-ell-wgt-n1340)

For the shortened lower extreme, replace \(t\) by \(\lambda\) and keep \(C_A=c_A-\sigma-\tau\). For the shortened upper extreme, use half-width \(\lambda\) and \(C_B=c_B-\delta\), since the lower end of that ratio window has moved up. The two changes delete a combined \(\delta[(c-\sigma-\tau-t)/\beta+2]\) from the linear harmonic envelope after taking out \(4L/7\). Thus the total normalized envelope for all placements is
\[
 t\left[4(c-\sigma-\tau)/\beta+8\right]
     -4t^2/\beta-\delta\left[(c-\sigma-\tau-t)/\beta+2\right].
\tag{1}
\]
Each of its window contributions is nonnegative. This is the envelope obtained after removing the exact opposite-sign pair.

## Integrating the envelope and the same-target charge

Enlarge the nonnegative main integral to \(0<t<\sigma<\tau\le\beta\), with product measure \(dt/t\,d\sigma/\sigma\,d\tau/\tau\). To justify extending the scaled prime harmonics to the lower endpoint, the envelope is \(O(t)\). For \(t<\varepsilon\), sum the least-prime weight first using \(\sum_{p\le x}(\log p)/p=\log x+O(1)\). It gives at most \(\min(\sigma,\varepsilon)+O(1/L)\). The remaining two harmonic sums give \(O(\varepsilon(1+\log^2(\beta/\varepsilon)))+o(1)\): for \(p_3\le N^\varepsilon\) the inner sum is \(O(\tau)\), and for \(p_3>N^\varepsilon\) split the \(p_2\) sum at \(N^\varepsilon\). The \(O(1/L)\) term costs \(O((\log L)^2/L)\). On \(t\ge\varepsilon\) ordinary Mertens sums on a fixed mesh give the integral. Taking \(\varepsilon\) down to zero proves the claimed enlargement.

The three moments of \(t,t^2,t(\sigma+\tau)\) are \(\beta,\beta^2/8,3\beta^2/4\). Hence the integral of the first two terms in (1) is \(4(c+9\beta/8)\). Where \(\delta>0\), its multiplying factor is at least \(c/\beta-1\). To lower-bound the integral of \(\delta\), change to \(u=\beta-t,\ v=\beta-\sigma,\ w=\beta-\tau\). There \(u\ge v\ge w\ge0\), \(u+v+w<\beta/2\), and \(\delta=\beta/2-u-v-w\). Replace \(1/(t\sigma\tau)\) from below by \(1/\beta^3\); the resulting symmetric simplex integral divided by six is \(\beta/2304\). This gives upper main integral \(4(c+9\beta/8)-(c-\beta)/2304\) at each \(x\).

With \(I=\log(36/35)\), the prime-\(\ell\) measure \(dx/(1-x)\) and the original doubling, the upper coefficient is therefore at most
\[
 \frac{J\Pi(4/7)}{\Phi_3\beta}
 \left[\left(4(1+11/40+9\beta/8)-\frac{1+11/40-\beta}{2304}\right)I
           -\frac{4-1/2304}{40}\right].
\]
Here \(J=3/8-\log2/2\), \(\Pi=\prod_{p>2}(1+1/(p(p-1)))\), and \(\Phi_3\) is the auxiliary denominator factor at level \(Y^3\). Use \(J<28427/10^6,\ \Pi<649/500,\ \Phi_3>879/500\) and the pinned rational upper bound on \(I\). The exact rational upper coefficient is \(29292110419051447/543527470080000000<27/500\). The summed errors and \(o(1)\) losses fit in this strict slack. If \(\mathcal D_3\) is the negative group mass in the exact branch, this proves \(2\mathcal D_3\le27N/500\), and the same charge covers the doubled absolute group mass. [Pinned Euler product and logarithm enclosures](https://github.com/Sodelin/Research-Commons/blob/a407395d23e2a193a67695b3b463d508b87e9ead/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-24-codex-goldbach-two-small-primes-0022z.md#the-prime-window-clipped-by-ell-wgt-n1340)

The original fallback budget can now use
\[
 2\mathcal D_{\ge4}(N)+\frac{92629}{666000}N
 \le M_0(N)+E_{\rm other}(N)-\eta N ,
\]
with fixed \(\eta>0\) at every sufficiently large power of two. Here \(\mathcal D_{\ge4}\) keeps the original group support with \(p_4\le N^{1/100}\). Those groups and the original other signed rows still need the uniform same-target bound.

This is a hand proof. Exact rational verification checked the coefficient, completion exponents and 7,272 placements at and between the ratio boundaries, including four cases of actual opposite-edge cancellation in the log model. Independent review is pending. Lean formalization remains open.
