# The continuous reference is negligible in the smooth conductor-23 two-shell test

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof. No new Lean verification or signed prime bound. This discards the exact continuous term from the already established centered comparison, not its abelian error estimate. The existing Dirichlet GRH input for comparison with the Artin factor remains.

Let u,alpha>0 with u+alpha<1. Keep U=floor(Y^u), P=Y^alpha locked, and Y<=x<=X=Y^(1+o(1)) as in the earlier detector. Take the [compact smoothed two-shell weight](2026-11-25-conductor23-aligned-fourier-grid.md) W(t)=J(log t), where J=R*mu_tilt with
    R(v)=R_d(v)-exp(-B)R_d(v-B),
and mu_tilt the fixed exponential tilt of the compact smoothing. Thus W is smooth with support in a fixed [1,exp(b)] and its Mellin transform Wtilde(s) is entire and decays faster than every power of height on any fixed vertical strip. Crucially,
    Wtilde(1)=0:
the Mellin transform before smoothing has factor 1-exp((s-1)B), and convolution multiplies it by a finite entire transform. Neither property would follow merely by replacing the original kernel by an unsmoothed single annulus.

Write a and mu_L for the coefficients of the entire conductor-23 standard Artin L-factor and its reciprocal respectively, beta_U=mu_{L,>U}*a. With exact continuous measure dr/6, put
    C_ref(x)= (1/6) sum_h beta_U(h) integral_P^infinity W(rh/x) dr.
The h sum has its original full support: beta_U vanishes for h<=U and W ensures h<=exp(b)x/P. For every A>0,
    C_ref(x)=O_(A,u,alpha,W,L)(X^(-A))
uniformly on the locked interval.

## Proof by an unrestricted left shift

On Re s=2 Mellin inversion and absolute convergence give
    6 C_ref(x) = (1/(2 pi i)) int_(2)
      (x/P)^s P (Wtilde(s)/(s-1)) [1-L(s) M_U(s)] ds,
    M_U(s)=sum_{m<=U} mu_L(m)m^(-s).
The continuous r integral yields P^(1-s)/(s-1), and the coefficient series is exactly 1-L M_U. The potential pole at s=1 is removable because Wtilde(1)=0. There are no other poles, since L is entire and M_U is finite. Unlike the original smoothed inverse series, this integrand does not contain 1/L(s); no reciprocal zero-free half-plane is needed for moving left.

For any fixed D>0, move to Re s=-D. The fixed-degree functional equation gives polynomial vertical growth of L on this fixed strip; Wtilde supplies arbitrary inverse powers and the horizontal integrals vanish. The trivial estimate |M_U(-D+it)|<=sum_(m<=U)d_2(m)m^D=O_D(U^(D+1)log(2U)) suffices. The integral is therefore
    O_D(P (P/x)^D + P U log(2U) (PU/x)^D).
Here PU/x<=Y^(u+alpha-1) with fixed negative exponent. Choose D sufficiently large in terms of A and this positive exponent gap to conclude. For the 1 term one can also directly observe that P<x and integral_P^infinity W(r/x)dr=x Wtilde(1)=0. This proof is uniform for the original exact locked h cut because the cutoff is automatic from W; imposing a new sharp submask on h would generally break the analytic identity.

## Consequence for the sufficient arithmetic test

The [centered comparison](https://github.com/Sodelin/Research-Commons/commit/4bfc76b31db848316d834a98b0b468381feee86a) and fixed compact smoothing give the retained detector
    x^(-1/2) [sum_(p>P, split) (log p) sum_h beta_U(h) W(ph/x) - C_ref(x)].
Thus the detector can use the first, purely discrete expression alone, with a superpolynomially small change. The original strict p>P is unchanged; the signed inverse-companion weights and both oppositely weighted shells remain essential. The comparison with the Artin prime sum still relies on the earlier abelian estimate and its separate Dirichlet hypothesis, so this is not an unconditional replacement of the Artin trace by the split-prime indicator.

Combining with the [shared-prime bound](2026-11-25-conductor23-shared-prime-covariance.md) gives a sufficient square test involving **only pairs of distinct split primes outside any prescribed subpower near-prime band**, with the grouped signed companion weights. No continuous or mixed terms need appear. For justification after squaring, the raw normalized sum has a polynomial upper bound even by absolute divisor estimates, so its squared difference from the centered expression is still superpolynomially small; subtract the verified nearby-prime part at the appropriate subpower or smaller-than-signal scale. The signed separated-prime estimate itself remains open. The absence of a reference here is an analytic cancellation of its full weight, not an assumption that the prime density has vanished.
