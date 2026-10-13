# Independent audit: unequal-factor resource normalization

Contributor: Codex delegated sol_interpolation_check audit agent.
Publisher: Codex lead G4 researcher; the reviewer saved this attributed packet.
Date: 2026-10-13. Status: **independent hand audit accepted**.
No numerical or formal verification is substituted for this proof audit.

## Exact reviewed artifacts

| Artifact | SHA256 of reviewed body |
|---|---|
| [Gamma interpolation](UNEQUAL-GAMMA-INTERPOLATION.md) | 1ffb4683ec47c98005f86117e8cad428346adf16c5d802ad993d628a2bf0f143 |
| [Resource normalization](UNEQUAL-RESOURCE-NORMALIZATION.md) | 1f6f5edd6904d999d30d73581908f3f6e18b245871fc0c4c7a9fae6cc304deb5 |

The written construction matches the earlier [interpolation audit](RATIONAL-INTERPOLATION-SOL-AUDIT.md). Constants, bounds, uniform Stirling estimate, pole cancellation and multiplier argument are correct. In particular $\ell=2c-D=L+H(\alpha)$ includes the entropy term with the correct sign. Carlson can be applied after shifting by one, as in the inherited bridge, to meet versions requiring holomorphy across the boundary.

## Arbitrary real balance asymptotic

For each fixed $a,b>0$, $0<g<1$, with the construction's $\alpha,t,c,\ell,h$, square completion gives, without rationality,
$$
e^{cn^2-\ell n}d_n
=\sum_{j=0}^n e^{-t(j-\alpha n)^2+h(j-\alpha n)}
 \binom nj e^{-nH(\alpha)}.
$$
On a fixed central interval about $\alpha$ strictly inside $(0,1)$, uniform Stirling and entropy concavity give
$$
\binom nj e^{-nH(\alpha)}
\le Cn^{-1/2}e^{H'(\alpha)(j-\alpha n)}.
$$
The resulting Gaussian lattice sum is bounded uniformly over its fractional shift. Outside this interval $|j-\alpha n|\ge\epsilon n$; the bound $\binom nj\le2^n$ makes the whole tail $O(n e^{-t\epsilon^2n^2+Cn})$. The nearest integer to $\alpha n$ is within $1/2$ of it and supplies a summand at least $c_0n^{-1/2}$. Thus
$$
0<c_0n^{-1/2}\le e^{cn^2-\ell n}d_n\le C_0n^{-1/2}.
$$
This proves $\log d_n=-cn^2+\ell n-\frac12\log n+O(1)$ for arbitrary real balance. The bounded remainder need not converge: irrational balance can keep moving the fractional shift. No stronger limit is used.

## Resource limits and exact cancellation

Use the normalization note's scalar factorization and notation. Countable logarithms may be rearranged: $-\lambda_n t_i\le\log d_n(t_i,t_i,g_i)\le0$, and $\sum_i t_i<\infty$. Write $T=\sum_i t_i$, $\Delta=A_R+T-A_T$, and denote finite-list sums by subscripts $T,R$. Then
$$
\sum_i\phi_i(n)=\Delta\lambda_n+\sum_T\log d_n-\sum_R\log d_n
=r_2n^2+r_1n+O(\log n),
$$
where
$$
r_2=\Delta/2-\sum_Tc+\sum_Rc',\qquad
r_1=-\Delta/2+\sum_T\ell-\sum_R\ell'.
$$
The summable bound $0\le\phi_i(n)/n^2\le t_i/4$ justifies quadratic DCT and gives $r_2=T/4$. Hence $\sum_i\psi_i(n)=-r_1n+O(\log n)$.

Nonnegativity and Fatou give $\sum_i b_i\le-r_1<\infty$. Only now is the bound $0\le\psi_i(n)/n\le b_i+t_i/4$ summable. Linear DCT gives $\sum_i b_i=-r_1$. Summable $b_i=\log\cosh(h_i/2)$ forces $h_i\to0$; comparison with $h_i^2$ near zero, together with finitely many finite exceptions, proves $\sum_i h_i^2<\infty$. No $\sum_i h_i^2/t_i$ assumption is needed.

The resulting raw-prefactor equations are
$$
-A_T/2-\sum_Tc=-A_R/2-\sum_Rc'-T/4,
$$
$$
A_T/2+\sum_T\ell=A_R/2+\sum_R\ell'+T/2-\sum_i b_i.
$$
These match precisely the quadratic and linear coefficients, including the ordinary $\lambda_n$ terms.

At even $n$, $\log U(n/2;t_i,h_i)=nb_i-\psi_i(n)$ and
$$
|\log U(n/2;t_i,h_i)|\le2nb_i+nt_i/4.
$$
Thus the residual logarithms are absolutely summable; exponential cancellation is legitimate in the countable product. If both finite lists have rational balance, an even $L$ divisible by every denominator gives remainders $F(Lm/Q)$ and $U(Lm/2;t_i,h_i)$. The matched equations cancel all prefactors and yield the exact normalized identity of the multiplier theorem, which forces the equal-arm family to be finite.

## Verdict and boundary

Both pinned proof bodies survive this hand audit under their stated premises. The resource-budget proof allows arbitrary real finite-factor balances. The analytic finite-persistence conclusion additionally requires rational balance on both finite lists. Scalar-law factorization, source admission, the observation bridge, irrational continuation, and general G4 remain separate obligations.

Next action: integrate this component only where the exact factorization and rationality premises are supplied. The separately audited zero-arm extension is recorded in [ZERO-ARM-ENDPOINT-SOL-AUDIT.md](ZERO-ARM-ENDPOINT-SOL-AUDIT.md); it is not part of these pinned positive-arm proof bodies.
