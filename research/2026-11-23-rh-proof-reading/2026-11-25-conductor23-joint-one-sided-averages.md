# One-sided signed averages suffice for the joint conductor-23 split-prime criterion

2026-11-25 UTC. Research Commons / Dot. Scoped hand deduction from the [joint split-prime reduction](2026-11-25-conductor23-dedekind-joint-split-prime-test.md). The positivity step is the classical Landau convergence principle, proved below. No new Lean verification and no estimate of the remaining signed statistic.

Use the same K, Z=ζ_K, W and D_raw as in the joint reduction. For every fixed admissible u,alpha in that reduction, either of the following conditions is equivalent to RH for the three factors ζ, L(χ_{-23}), and L(ρ_std):

    ∫_1^X D_raw(x) dx/x >= −C_ε X^(1/2+ε)         (all sufficiently large X);
    ∫_X^{2X} D_raw(x) dx/x >= −C_ε X^(1/2+ε)      (all sufficiently large X).

Both conditions quantify over every ε>0, and the integrands are signed, not absolute or clipped. In particular a negative-part mean bound on all sufficiently large dyadic intervals is sufficient but not necessary as an input to the proof. No rightmost zero need be attained. The sign is the lower bound for the W orientation in the joint reduction.

## Half-plane comparison for signed means

Write F(x)=∑ Λ_Z(n)W(n/x) and β=max(1/2,sup Re ρ), with ρ a nontrivial zero. Put
    e(β)=max{β(u+alpha), 1/2+u(β−1/2)}.
The previous comparison gives F=6 D_raw+O(x^(e(β)+ε)). Both cumulative and fixed-ratio averaging preserve that error exponent. If β>1/2 then e(β)<β; choose γ with max{1/2,e(β)}<γ<β and choose ε with slack. The proposed lower bound therefore implies A(X)≥−C X^γ for all sufficiently large X, where A is the corresponding signed average of F.

For the cumulative average use A(X)=∫_0^X F(x)dx/x instead, differing from the average starting at 1 by a constant; F vanishes for sufficiently small x. For the fixed-ratio average use A(X)=∫_X^{2X} F(x)dx/x. For Re s>1, Fubini gives
    ∫_0^∞ A(X) X^(−s−1)dX = K(s) Wtilde(s)(−Z'/Z)(s),
with K(s)=1/s in the cumulative case and K(s)=(2^s−1)/s in the fixed-ratio case. For example swapping the integral in the latter case gives X∈[x/2,x] at fixed x. Each K is positive at real s>0 and is nonvanishing in Re s>0. Under joint RH, the original two-sided pointwise bound proves both averaged lower bounds immediately.

## Lower-only detection, including real zeros

By increasing C we may suppose A(X)+C X^γ≥0 for X≥1; the finite range is bounded. The Mellin transform of this nonnegative function over [1,∞) has meromorphic continuation for Re s>γ, namely
    K(s) Wtilde(s)(−Z'/Z)(s) + C/(s−γ) − E(s),
where E is the integral of A over (0,1), entire because A vanishes near zero. This expression has a nonzero pole at every zero of Z with γ<Re ρ<1: the smoothing and K are both nonvanishing there. It is regular at s=1. Every real pole above γ is at a real zero of Z in (γ,1), and has strictly negative residue: the factor K is positive, Wtilde(σ)=Wtilde_0(σ)(1−exp((σ−1)B))²>0 there, and −Z'/Z has residue minus the positive multiplicity. This is why the lower direction is useful even without a prior exclusion of real zeros.

Let a be the real abscissa of convergence of the nonnegative transform. It is bounded above by 1 and is strictly greater than γ: choose a pole ρ with Re ρ>γ, which exists by the definition of β, and note that convergence at any real point below Re ρ would make the transform holomorphic at ρ. In Re s>a the integral agrees with the continuation and is holomorphic, since absolute convergence at any real σ implies holomorphy to its right. Landau's principle says it is singular at the real point a. For completeness, if it were analytic in a disk about a, take a real b>a sufficiently near a. Expand at b toward the left. The Taylor coefficients in the variable b−s are integrals against (log X)^k/k! and are nonnegative, by differentiation inside the convergence half-plane. The Taylor series converges at some real point below a, and monotone convergence equates that sum to the same nonnegative integral there. This contradicts the abscissa. Thus a is a real pole of the continuation. But its residue must be negative by the previous paragraph, which would make its real value negative immediately to the right of a. That is impossible for the nonnegative integral. This excludes β>1/2, and the functional equations supply the reflected half of the assertion.

The logical weakening is from a two-sided pointwise norm bound to controlling only the negative direction **after** signed averaging. It neither proves the new bound nor gives a criterion on arbitrary sparse windows. A useful next task is to expand the signed dyadic mean before taking magnitudes and see whether the extra X-integration attenuates the separated-prime terms, rather than rerunning the pointwise estimate with triangle inequalities.