# Independent review: fixed-beta frozen-prior Gaussian residual

20 October 2026. Reviewer: dot (OpenAI), working with Nolan. Independent assistant-context hand review. No historical novelty, external peer review, formal verification, or full P1 claim.

## Decision

**Scoped PASS** for Sections 1–4 and the corresponding limitations in Section 6 of P1-COMMON-REFERENCE-AND-FROZEN-PRIOR-20261020.md. The exact reviewed-source hash is recorded separately.

The construction disproves the proposed uniform bound I(Theta;G|C_n)<=C_(beta,k) M for isotropic G=Theta+sqrt(t)Z at t=1/(n beta^2), already at fixed beta=2,k=2. It uses admissible finite priors. It does **not** disprove delta_n<=C M/n, a Bures-risk bound, or the original testing goal. The actual dyadic Holevo increment tends to zero on this same family.

The beta-varying scalar diagnostic in Section 5 is not needed for this decision and is not part of the reviewed appendix result. I did not use its quadrature as proof.

## 1. Common-reference and conditional-information identities

Donald’s identity and relative-entropy monotonicity give the stated common-reference difference inequality. The lifted defect identity is algebraically correct and does not imply monotonicity of that defect.

For the Gaussian auxiliary, C and D are independent conditional on Theta,G. Chain rules give I(Theta;D|CG)=I(Theta;D|G)-I(C;D|G); adding G and dropping the latter nonnegative quantity gives the proposed upper comparison. The Gaussian smoothing term uses the existing trace-Hessian estimate, with the same H and full coefficient space. Coefficients outside the promise occur only in mathematical reference states, not input candidates or experimental copies.

Since G and C are independent conditional on Theta, I(Theta;G|C)=I(Theta;G)-I(G;C). Data processing gives I(G;C)<=I(Theta;C)=chi_n. These quantum-classical identities are valid even though C is not a measured classical posterior. Here the chosen example is diagonal, but the comparison formulas need not assume that.

## 2. Fixed-beta admission and uniform freezing

Every Hamiltonian has one-body Z and pairwise ZZ coefficients between -1 and -1/2; all other allowed coefficients are zero. The positive a_i,b_ij notation denotes their magnitudes. Hence the construction is inside the original coefficientwise cube, with unrestricted complete-graph incidence and fixed beta=2,k=2.

There are r=N(N+1)/2 independently variable coefficients, while the full original parameter count is M=3N+9 binom(N,2). Exactly 9r-M=6N>=0, so r>=M/9. This constant-fraction comparison is for k=2, not for arbitrary larger k while varying only pairwise terms.

For s flipped spins, each field and cross-cut pair costs at least one unit of energy. Thus the gap is at least s(N-s+1)>=N; the last inequality is the identity s(N-s+1)-N=(s-1)(N-s)>=0. The all-plus configuration is the unique ground state for every prior label. The denominator of the Gibbs excited probability includes its unit ground-state relative weight. Summing at most 2^N-1 excited relative weights proves q_theta<=exp[-(2-log2)N] uniformly, without a typical-coefficient assumption.

## 3. Entropy bound: no large-memory continuity problem

The one-copy prior mixture is diagonal and puts at least 1-q_N mass on the same all-plus configuration. For sufficiently large N, its entropy is bounded by h2(q_N)+q_N N log2. Entropy subadditivity and nonnegativity of the component entropies then imply chi_m<=m S(omega_1). This remains valid for m exponential in N: it does not apply a trace-distance continuity inequality to a 2^(mN)-dimensional state.

An explicit simplification confirms the rate. Since h2(q)<=q(1-log q),

    h2(q_N)+q_N N log2 <= q_N(1+2N).

With n=floor exp(N/4),

    chi_n <= (1+2N) exp[-(7/4-log2)N],
    chi_(2n) <= 2(1+2N) exp[-(7/4-log2)N].

The exponent is strictly negative. Both quantities tend to zero. In particular the construction does not have a hidden nN or n-squared entropy penalty large enough to invalidate the claim.

## 4. Finite prior and Gaussian information

For each N, choosing L=floor exp(N/16) grid values for each of r coefficients gives a finite uniform product prior with exactly L^r labels and entropy r log L. Dependence of this finite prior on N and n is permitted by the required uniform arbitrary-finite-prior statement. Fixed zero coordinates add only independent Gaussian noise and no source information.

At t=1/(4n), the standard deviation is 1/(2 sqrt n). Half the grid spacing divided by this deviation is sqrt n/[2(L-1)]. The two-sided Gaussian tail bound and union bound therefore give the displayed vector-error bound 2r exp[-n/(8(L-1)^2)]. Endpoint grid points have no larger error. Decoding signs in the negative coefficient convention makes no difference.

For large N, n>=exp(N/4)/2 and L-1<=exp(N/16), hence

    e_N <= 2r exp[-exp(N/8)/16] ->0.

Fano’s inequality for L^r equiprobable labels gives I(Theta;G)>=(1-e_N)r log L-h2(e_N), once the upper error bound is below 1/2. The replacement of actual error by this upper bound is then legitimate. Also log L=N/16+o(1). Thus I(Theta;G)=(1-o(1))rN/16, and subtracting the vanishing chi_n preserves this asymptotic for the residual.

Combining with r>=M/9 proves Omega(MN), so no constant depending only on beta=2 and k=2 can bound the residual by M. This is a growing-N failure of that auxiliary-information premise, not a varying-temperature argument.

## 5. Acceptance boundary

The Gaussian auxiliary resolves many Hamiltonian coefficients that the available quantum states do not distinguish at the selected sample scale. The actual information increment obeys 0<=chi_(2n)-chi_n<=chi_(2n)->0. The accepted PGM bridge is untouched and yields no adverse testing conclusion here.

The valid tactical conclusion is to abandon this universal isotropic-residual upper bound as a route to the desired rate. A state-sensitive auxiliary, cancellation-retaining estimate, direct information-increment argument, or direct risk method is not excluded. None is supplied by this review.

This is a hand proof review of all constants and limiting claims above. The producer's finite floating evaluations are diagnostic, not necessary to the argument and not independently certified here. No new experiments, external writes, installations, or publication were performed by the reviewer.

## 6. Publication successor cross-check

I also read publication/P1-ISOTROPIC-RESIDUAL-OBSTRUCTION-20261020.md in full, at the hash recorded in REVIEWED-SOURCE-SHA256.txt. **Scoped PASS** applies to this successor. It removes the scalar detour while preserving the reviewed fixed-beta construction.

Its added sufficient gate is correct: for any auxiliary kernel G|Theta and known states tau_g, the same conditional-information calculation gives the dyadic increment at most I(Theta;G|C_n)+n E D(rho_Theta||tau_G). Bounds by C M on both terms therefore suffice. Neither bound is supplied uniformly. For the displayed frozen prior, constant G and tau=omega_1 give zero residual and distortion n chi_1<=n S(omega_1)->0. This correctly demonstrates that the obstruction concerns isotropic coefficient resolution, not every auxiliary-reference approach. It makes no all-class construction or inverse-Hessian guarantee.
