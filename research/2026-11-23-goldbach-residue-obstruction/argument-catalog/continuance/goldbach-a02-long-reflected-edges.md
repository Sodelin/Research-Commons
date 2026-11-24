# Exact and absolute charges on the long reflected \(A_{02}\) row

**Unconditional hand proof at fixed \(N=2^k\).** Keep the pinned unmatched support \(Q=N^{1/4}\le q\le\min(\alpha,H/2)\), odd squarefree \(q\), \(H<h<N/q\), \((h,2q)=1\), \(H=\sqrt N\), \(\alpha=H/L^{K_0}\) and \(L=\log N\). In the reflected sum use \(U=V=N^{1/10}\), \(D_q=\sqrt{N/q}/L^B\), and the exact equation and tests
\[
 qh+wbs=N,\qquad
 w>V\text{ prime},\quad b\le U,\quad bs>U,\quad wb>D_q.
\]
The signed weight is \(+\mu(h)\mu(b)\log h\log w\). The statements here concern subregions of this exact long reflected sum. The separate Type I error is the one in the pinned identity. [Pinned adaptive cutoff, signs and support](https://github.com/Sodelin/Research-Commons/blob/eb8764f7be7658e10cba6b942ad94bbd97ed81bc/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-unmatched-outer-adaptive-mobius.md).

## Completion at both adaptive divisor thresholds

Fix \(q,h,w\) and write \(M=(N-qh)/w>U\), \(T=D_q/w\). The signed group is \(\mu(h)\log h\log w\) times
\[
 F_U(M)-F_T(M),\qquad
 F_t(M)=\sum_{\substack{b\mid M\\b\le t}}\mu(b).
 \tag{1}
\]
The strict \(wb>D_q\) puts the equality case \(b=T\) in the subtracted prefix. Let \(S_t=\prod_{p\mid M,\ p\le t}p\), with the empty product one. For \(1\le t\) and \(S_t\le t\), the prefix in (1) contains every squarefree divisor of \(S_t\). It has value one if \(S_t=1\) and zero if \(S_t>1\). Consequently the group vanishes, even for \(w\le D_q\), when \(1\le T<U\), both \(S_U\le U\), \(S_T\le T\), and both products are nontrivial or both are one. This is a pointwise cancellation of the entire \(b\)-group on the original support.

When \(w>D_q\), the prefix \(F_T\) is empty. If also \(M/P^-(M)\le U\), every proper divisor is admitted, and the full prefix equals \(-\mu(M)\) by completing the Möbius sum on \(M>1\). Thus all nonsquarefree \(M\) in this subregion give exact zero. In particular this holds throughout \(w>N/(3U)\): \(M<3U\) is odd, so its least prime is at least 3, and \(w\) is above the adaptive cutoff for large \(N\).

## Absolute charge at the extreme upper prime edge

For \(N^{-1/10}\le\eta\le1/2\), retain
\[
 (1-\eta)N/U<w<N/U .
\]
The upper inequality follows from \(wM<N\), \(M>U\). In this region \(U<M<U/(1-\eta)\le2U\); the preceding exact group weight is \(-\mu(h)\mu(M)\log h\log w\). The sum of its absolute values is
\[
 O\!\left(NL^2(\eta^2+\eta/U)\right).
 \tag{2}
\]
In particular \(\eta=L^{-1-\varepsilon}\) gives \(o(N)\) for every fixed \(\varepsilon>0\).

To prove (2), fix \(q,M\). The equation puts \(w\) in a single reduced class modulo \(q\), as \(M\mid n\) and \((n,q)=1\). The additional \(h\) tests can be dropped for upper counting after the exact grouping. The \(w\) interval has length \(Y=\eta N/U\), with \(\log(Y/q)\gg L\) throughout the retained \(q\) range. Interval Brun–Titchmarsh bounds the number of primes by \(O(Y/(\varphi(q)L))\). Multiplying by the original \(\log h\log w\le L^2\) yields \(O(YL/\varphi(q))\). There are \(O(\eta U+1)\) values of \(M\), and \(\sum_{q\le H}1/\varphi(q)\ll L\). These bounds give (2) with the upper prime cutoff intact. [Montgomery–Vaughan interval Brun–Titchmarsh](https://doi.org/10.1112/S0025579300004708).

## Two allocation changes across the moving index

There is also an exact reduction when both factors in the modular cutoff can move. At fixed endpoints \(m=qh\), \(n=N-m=wM\), choose \(p\mid m\) and a prime \(r\mid M\), by any rule depending only on the fixed group. Write \(e=\nu_r(M)\ge1\), choose \(a,h_0,b_0,s_0\) with \(m=a h_0p\) and \(M=b_0s_0r^e\), and take \(r\nmid b_0s_0\). The allocations are
\[
 q=a p^i,\quad h=h_0 p^{1-i},\qquad
 b=b_0 r^j,\quad s=s_0 r^{e-j},
 \qquad i,j\in\{0,1\}.
\]
Terms with \(j\ge2\) would have \(\mu(b)=0\). Retain the orbit where both \(q,h\) allocations meet their original tests, \(b_0r\le U\), and \(M>U\). These are invariant conditions on the four positions. The only variable eligibility test is \(wb>D_q\).

Let \(x=\log(wb_0/D_a)\), \(\rho=(\log p)/2\), \(\tau=\log r\) and \(H_i=\log h_0+(1-i)\log p\). Since \(D_{a p^i}=D_a p^{-i/2}\), that strict test is \(x+i\rho+j\tau>0\). The exact sum of the four retained weights is
\[
 \mu(h_0)\mu(b_0)\log w
 \left[H_0\mathbf1_{(-\tau,0]}(x)
      -H_1\mathbf1_{(-\tau-\rho,-\rho]}(x)\right].
 \tag{3}
\]
In fact, at fixed \(i\), the two \(j\) terms differ only when \(x+i\rho\) lies in \((-\tau,0]\), and the Möbius sign changes with \(i\) as well. The strict inequalities explain the open left and closed right endpoints in (3). On the overlap of the two intervals the logarithmic factor is \(H_0-H_1=\log p\). A full \(\log h\) factor can survive only in their symmetric difference, which has total log width \(2\min(\rho,\tau)\). This is an exact signed restriction on this interior orbit, including squareful \(M\); the other groups retain their existing weights and need further estimates.
