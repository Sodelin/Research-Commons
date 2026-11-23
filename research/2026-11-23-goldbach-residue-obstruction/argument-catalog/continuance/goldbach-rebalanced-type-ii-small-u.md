# Signed small-\(u\) removal with the rebalanced Goldbach square

**Unconditional hand proof at each fixed power of two.** In the pinned rebalanced expansion keep \(U=N^{1/100}\), \(V=N^{1/5}\), \(D_s=N^{23/500}\), \(z=N^{17/5000}\), and \(\ell w>N^{13/40}\). Keep all other original tests and the same \(W_N(n)\). The signed row \(U<u\le N^{1/10}\), with both expanded endpoint parities, is \(O_A(N/L^A)\) for every fixed \(A\). On the remaining row \(u>N^{1/10}\), for any one ratio interval of width at most \(\Delta\) per actual \(\ell\) and dyadic \(n\) band, the absolute charge is
\[
 O_A\!\left(\frac{N(1+\Delta)}{L}+\frac{N}{L^A}\right).
\]
In particular every such \(o(L)\)-width strip is negligible on the target scale. Both statements use the fixed rebalanced square, without changing the signed stress partition. [Pinned rebalanced expansion](https://github.com/Sodelin/Research-Commons/blob/3894f49a36cb7cc752bdf1002b8f465253d3fafe/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rebalanced-expansion.md).

## Exact smooth-side reduction

Set \(Q_\ell=N^{13/40}/\ell\ge V\). The opened coefficient on \(v\) after the retained base is the exact divisor weight
\[
 B_\ell(v)=\log v-\sum_{\substack{w\mid v\\w\le Q_\ell}}\Lambda(w).
\]
Use the ordered \(\tfrac12F(m)\mu(h)\log(h/q)\) weight, which pairs to the original odd-\(m\) terms. In the first term group the signed index \(r=\ell u\). In the second write \(v=ws\) and group \(r=\ell u w\), retaining \(w\le Q_\ell\) in the arithmetic coefficient. The second index satisfies \(r\le N^{13/40+1/10}=N^{.425}\); the first is smaller. The denominator \(1/\log d\) is handled by the pinned integral on \([0,10]\), with negligible remainder. The coefficient on \(r\) is \(O(L^2)\) by the eligible prime-\(\ell\) divisor count and \(\sum_{w\mid r/\ell}\Lambda(w)\le\log r\). The remaining factor is smooth and carries \(1\) or its logarithm and the short nonnegative Mellin powers. The \(n\) trim makes \(d>D_0\) automatic after retaining \(\ell\). [Pinned grouped coefficients and endpoint trim](https://github.com/Sodelin/Research-Commons/blob/f893580eb8d15f9c21987a478461b45d997cfda0/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md#determinant-transfer-with-the-exact-masks).

The previous small-frequency proof alone would allow \(rF<H\) and need not cover this whole row. Here keep the polynomial period in the signed index for the nonzero modes. In opening the square let \(c=[a_1,a_2]\), \(c_1=(c,r)\), \(c_2=c/c_1\). The first factor and \((c_2,r)=1\) are kept in the arithmetic index. Let \(b_0\) be the subpower rough period on the smooth complement. Its period is \(F=[c_2,b_0]\le D_s^2N^{o(1)}\); the \(q\) period \(E\) is subpower. The rough-square extension and factorial tails are those of the original proof. Since \(N=2^k\), enforce both \(q,h\) odd directly. Then \(n,r,s\) are odd, and only odd divisibility periods are relevant. The \(m\) masks use their exact factorizations across \(q,h\) and the same truncated subset phases, on this odd support. 

## Combining the polynomial period with the signed index

At fixed original scale \(r\asymp R\), smooth-side scale \(s\asymp S\) and grouped scale \(j=Fr\asymp J\), the unit congruence is solved for the progression \(q=E(2k+1)\). A solution has \((Eh,j)=1\) exactly. Poisson in \(k\), using
\[
 k\equiv (N/2)\overline{Eh}-\overline2\pmod j,
\]
has reciprocal phase \((-1)^\nu e(\nu(N/2)\overline{Eh}/j)\). Indeed the shift phase \(e(-\nu\overline2/j)\) combines with \(e(\nu/(2j))\) after changing the integration variable to \(q/H\). The frequency scale is \(T_0=2EJ/H\). In normalized variables \(x=h/H\), \(y=j/J\), \(r_0=r/R\), its smooth amplitude has the form
\[
 \frac1{T_0 y}\int Q(u_0)
 G\!\left(\frac{N-Nu_0x}{RSr_0}\right)
 e\!\left(-\frac{\nu u_0}{T_0 y}\right)\,du_0.
\]
The product \(RS\gg N/L^B\) gives polylogarithmic normalized derivatives in the extra variable \(r_0\), as it does in \(x\). Smoothing the prescribed box and optional endpoint edges has the pinned divisor-moment cost. Integration by parts discards \(|\nu|>T_0H^\epsilon\) with an arbitrary power after summing all raw choices, for any sufficiently small fixed \(\epsilon>0\).

For a retained dyadic frequency scale, use four-variable partial summation in \(x,y,r_0,\nu/T\). The extra prefix in \(r_0\) is imposed inside the grouped coefficient at \(j\). At fixed \(j\) and any such prefix, \(r\mid j\) fixes \(F=j/r\), \(c_1\mid r\), \(c_2\mid F\), and \(a_1,a_2\mid c_1c_2\). There are only \(N^{o(1)}\) such choices by the divisor bound. Consequently the grouped coefficient on \(j\) has squared norm \(O(N^{o(1)}J)\) uniformly in the added prefix. The number of external \(q\) masks and fixed \(b_0\) choices is subpower. Any \(h\) restriction from coprimality acts either in its fixed coefficient or as \((Eh,j)=1\), the primitive restriction of the trilinear sum.

Apply Bettin–Chandee at scales \(EH,J,T\), phase parameter \(N/2\), and norms \(\sqrt{H},\sqrt J,\sqrt T\) up to subpower factors. The amplitude gives \(T_0^{-1}\sqrt{HJT}\ll H^{1+O(\epsilon)+o(1)}\). The phase amplification is \(H^{O(\epsilon)}\), since \((N/2)T_0/((EH)J)=1\). The two terms of the pinned argument now use \(J\) itself and have bounds, up to \(H^{O(\epsilon)+o(1)}\),
\[
 HJ^{7/10}(H+J)^{1/4},
 \qquad HJ^{3/4}\big((J/H)(H+J)\big)^{1/8}.
\]
Here \(J\le N^{.425+.092+o(1)}=H^{1.034+o(1)}\). For \(J\ge H\) these give powers \(1.9823\) and \(1.909\) on \(H\) before the small allowances; for \(J\le H\) both are smaller. Thus the nonzero sum saves a fixed power. This consolidation avoids charging all the \(F\) periods separately in that estimate. [Pinned Bettin–Chandee scales](https://github.com/Sodelin/Research-Commons/blob/9a77141e26f67c56ec8c61102ce6516f5ed24f12/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-joint-frequency-cutoff.md) · [Bettin–Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769).

For frequency zero keep the old separate sum over \(r,F\). The prefix on \(h\) excludes \(NrF<N^2\); normalized derivatives have log-power bounds. The factor \(1/[E,F]\), together with the \(O(R/c_1)\) count at fixed \(c_1\mid r\), assigns a reciprocal factor to each square prime. The old masks have only boundedly many local roles, so the entire reciprocal norm is polylogarithmic. The original uniform Möbius prefix with the \(h\) phase and smooth factors yields arbitrary log savings. This proves the signed small-\(u\) row under the same retained base. [Pinned zero-frequency reciprocal argument](https://github.com/Sodelin/Research-Commons/blob/3894f49a36cb7cc752bdf1002b8f465253d3fafe/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rebalanced-expansion.md#a-small-frequency-range-permits-the-larger-square).

## Absolute transfer for thin ratio rows after the removal

Now \(x=\min(u,v)\ge N^{1/10}\) and \(M=\ell x\le N^{9/16}\). Retain the original prime-\(\ell\) band and endpoint bands, enlarging each \(q,h\) rectangle only for positive upper counting. In the expansion of \(W_N(n)\), let \(c\) be the part of \([a_1,a_2]\) not already present in \(M\). Count the unit hyperbola at \(M c_{\rm odd}\), with the same three parity pairs for \(q,h\) if \(2\mid c\). The per-pair error is \(N^{o(1)}((Mc)^{1/2}+H/(Mc)^{1/2})\). Summing all pairs and all \(M\) costs \(N^{27/32+3\kappa+o(1)}+N^{25/32+2\kappa+o(1)}\), both below \(N\). The main term is the same fixed-square nonnegative kernel, with local flags forced at primes of \(x\) and unforced density from \(qh=N\) elsewhere. At each dyadic \(x\) scale its harmonic average is \(Q\log 2+O(D_s^2/X)\), from the exact harmonic sum of multiples. Here \(X\gg N^{1/10}\), hence the total floor error is \(N^{.992+o(1)}\). The main size is \(Q\ll L^{-2}\), and the interval for \(\log(u/v)\) gives \(O(1+\Delta)\) dyadic \(x\) scales through \(2\log x=\log(n/\ell)-|\log(u/v)|\). Finally use \(\sum_\ell\log\ell/\ell\ll L\), the dyadic endpoint rectangle area \(O(N4^{-j})\), and the absolute coefficient bound \(O(W_N(n)\log\ell)\). This gives the stated thin-row bound with the original fixed square. [Pinned harmonic averaging and ratio geometry](https://github.com/Sodelin/Research-Commons/blob/290227d6b4b2b5e69e39b241332620885c661ced/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-selberg-ratio-strips-2158z.md#averaging-the-type-ii-square-over-the-two-factors).
