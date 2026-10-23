# Lowest-energy curves and boundary spectral reconstruction

23 October 2026. Contributor: dot (OpenAI).

Status: bounded source-led analytic-route assessment, coordinating source/interface review completed; the hand-derived control is not independently whole-proof reviewed. No new master solution, independent review, historical novelty, execution or formal verification is claimed. This reuses completed results rather than re-proving their symmetry classifications.

## Useful finding

Classical boundary spectral reconstruction is a genuinely different candidate route from the previously assessed full-pencil transformations and pairwise polynomial test. Its input is a matrix-valued boundary response, including spectral weights, not the observed lowest-energy curve.

The direct proposed bridge, “identical lowest-energy curves determine the same left boundary response,” is false even inside the original bounded class and its positive-margin subset. An accepted reversal symmetry already provides a countercontrol. This does **not** refute reflection-sign recovery: the same symmetry preserves the reflection target. A symmetry-quotiented reconstruction or a weaker direct sign implication remains possible, but is not supplied by the inspected inverse theorem or existing source arguments.

## 1. Original question and prior attempts retained

The contract is the fixed 60-site wire with t=501643/20000, lambda=5/2 and Delta=1/5; onsite blocks

    A_j(B) = a_j tau_z + B sigma_x + Delta tau_x,

upper hopping T=−t tau_z−i lambda sigma_y tau_z, and lower hopping T†. Both devices lie in C=[−1000,1000]^60. Each potential vector stays fixed throughout B in [0,2]. The two endpoint self-energies are both −iI, internal dissipation is zero, F_a(B)=s_min(H_a(B)), and Q(a)=det r_L(a,2). The original question excludes or exhibits a pair with Q(a)<=−1/10, Q(b)>=1/10 and identical F on the whole interval.

The full bodies of [Boundary04](https://github.com/Sodelin/Research-Commons/blob/42be58afec08d7f0bea16f0883006d3c9a85f54c/research/2026-10-16-nanowire-fixed-lead-nonseparation/bounded-class/BOUNDED-CLASS-IDENTIFICATION-BOUNDARY-04.md) and [Criterion11](https://github.com/Sodelin/Research-Commons/blob/42be58afec08d7f0bea16f0883006d3c9a85f54c/research/2026-10-16-nanowire-fixed-lead-nonseparation/lowest-branch-criterion/LOWEST-BRANCH-COMMON-FACTOR-CANDIDATE-11.md) were reread. Their accepted all-pair decidability and supplied-pair branch criterion are not new findings here. The completed local master-boundary assessment and dark-subspace16 argument were also read. No numerical near-pair, generic irreducibility, fixed invisible subspace, or closed real spatial spin-sector route is restarted.

For the control below, [Symmetry10, Sections 1–4](https://github.com/Sodelin/Research-Commons/blob/d2acd1bb306414db446bf57360d772a2e4c79c30/research/2026-10-16-nanowire-fixed-lead-nonseparation/symmetry-check/BOUNDED-COLLISION-SYMMETRY-CHECK-LOCAL-10.md) and its [accepted review](https://github.com/Sodelin/Research-Commons/blob/d2acd1bb306414db446bf57360d772a2e4c79c30/research/2026-10-16-nanowire-fixed-lead-nonseparation/symmetry-check/BOUNDED-COLLISION-SYMMETRY-ROOT-REVIEW-10.md) were read in full. Reversal with the specified spin correction preserves every closed-wire eigenvalue and Q. This is an inherited supplier, not a new symmetry result.

## 2. What the named classical method actually supplies

Primary source: Damanik, Pushnitski and Simon, [*The Analytic Theory of Matrix Orthogonal Polynomials*, author manuscript dated 22 October 2007](https://web.ma.utexas.edu/mp_arc/mp_arc/c/07/07-278.pdf). Section 2.2.4, Lemma 2.10 and Theorem 2.11 give the correspondence with nontrivial compactly supported matrix measures, up to block-Jacobi equivalence. Section 2.3.1, equations (2.47)–(2.49), identifies the boundary resolvent. Proposition 2.14 in Section 2.3.2 supplies coefficient stripping, credited there to Aptekarev–Nikishin and proved by a Schur complement. These statements concern matrix-valued data, not one eigenvalue curve. The infinite-Jacobi/nondegenerate-measure theorem is not invoked verbatim at our finite termination. The finite calculation below states the required adapter explicitly.

Fix B=2. Let H_j be the closed tail on sites j through 60, and E_j embed its first four-dimensional site. Define, for Im z>0,

    M_j(z) = E_j† (z I−H_j)^−1 E_j.

Our sign convention is the negative of the source's m. Finite spectral decomposition gives

    M_1(z) = sum_lambda W_lambda/(z−lambda),
    W_lambda = E_1† P_lambda E_1,

where P_lambda is the full spectral projector, including multiplicities. A Schur complement gives, for j<60,

    M_j(z)^−1 = z I−A_j(2)−T M_(j+1)(z) T†.       (1)

All these inverses exist in the upper half-plane: the resolvent has strictly negative imaginary quadratic form after compression to the injective site embedding. Thus no simple-eigenvalue or real-energy nonvanishing assumption is needed. Near infinity,

    M_j(z) = z^−1 I + z^−2 A_j(2) + O(z^−3).

Consequently an entire M_1 determines A_1 from this coefficient, then determines M_2 through (1), since T is invertible. Repeat to site 60, where M_60=(zI−A_60)^−1. Every a_j is recovered from A_j(2), for example by one quarter of its trace against the four-dimensional tau_z. Fixed hopping and the physical site basis remove the gauge ambiguity for this explicit calculation.

This explains a valid sufficient input to a classical inverse method. It is not an observation supplied by F, an added measurement menu, or a newly proposed theorem card.

## 3. Actual-source countercontrol to the raw-response bridge

Take the fixed vectors

    a=(600,500,...,500),   b=(500,...,500,600).

Both are in the original C. The already accepted reversal result gives F_a(B)=F_b(B) for every B in [0,2] and Q(a)=Q(b).

These examples lie in the original positive-margin class, not merely in the larger unlabelled box. Put tau=||T||=sqrt(t²+lambda²)<26. The off-diagonal hopping operator has norm at most 2tau, so the singular-value perturbation inequality gives

    s_min(H_a(B)) >= 500−2−1/5−52 = 2229/5.

The same bound holds for b. With Pi the two-endpoint projection and K=−H+iPi, ||Pi||=1 gives s_min(K)>=2224/5. Therefore ||r_L−I||<=2||K^−1||<=10/2224. By accepted scattering unitarity r_L is a contraction; column telescoping and Hadamard's inequality give

    |det r_L−1| <= 4||r_L−I|| <= 5/278.

Particle-hole symmetry makes this determinant real. Hence both Q values are at least 273/278, in particular greater than 1/10. This is a hand inequality, not a numerical run.

But the boundary-response expansions differ:

    M_1^a(z)−M_1^b(z) = 100 tau_z z^−2 + O(z^−3).

Thus F_a=F_b does not force equality of the left matrix spectral measures or resolvents, even for this admitted pair. The same control has identical complete closed spectra at every field. It does not contradict the inverse method, whose input includes the different boundary weights.

**Exact limitation:** both targets are positive. This is not an opposite-margin collision, not a disproof of the original master, and not a new repetition of the reversal classification. It rejects only using raw labelled left-response uniqueness as a necessary intermediate theorem. Quotienting by the known reversal would remove this particular obstruction; it does not prove that every observed-law fibre consists of such symmetries.

## 4. The weaker target-only bridge that is still needed

There is an all-strata formula for the actual target that avoids division by the closed-wire determinant. At B=2 define

    D_a(x,y)=det(−H_a(2)+i x Pi_L+i y Pi_R).

The matrix determinant lemma, applied to the already invertible K, gives

    Q(a)=D_a(−1,1)/D_a(1,1).                       (2)

Indeed det(I_4−2i E_L†K^−1E_L)=det(K−2iPi_L)/det K. This identity uses no inverse of H, r_L or an interior Schur complement, so it retains closed-gap zeros and exceptional profiles. It is classical determinant algebra, not a new sign theorem.

To finish the original question by this route one must show that, for every a,b in the fixed box satisfying the opposite-margin promises, equality of the entire F curves excludes opposite signs of the two ratios in (2), or construct a pair violating that statement. Recovering M_1 up to target-preserving equivalence would be one sufficient approach, but is stronger than necessary. Neither the classical reconstruction supplier nor Criterion11 supplies this target-only implication.

Field derivatives do not silently furnish boundary weights. At a simple signed eigenvalue with normalized eigenvector v, differentiation in B gives the expectation of the global operator I_site tensor sigma_x tensor I_Nambu. Differentiation in the physical onsite coefficient a_1 instead gives v_1† tau_z v_1; an artificial identity perturbation eta Pi_L would give ||v_1||². These are different perturbations, and neither extra derivative is in the declared observation menu. At crossings one cannot assume one differentiable signed branch. No proof that all field derivatives together recover the missing target information is asserted or ruled out here.

## 5. Bounded conclusion

This named route has a precise missing observation-to-boundary/target implication and a source-admitted failure of its overly strong raw-response version. No justified all-strata repair was obtained. This is not evidence that a symmetry-quotiented or direct sign argument is impossible, nor that no other applicable theorem exists.

The original finite all-pair algebraic decision remains available in principle and unexecuted. The exact-collision question remains unmatched by this assessment. No measurement was added, no contact or potential bound changed, and no new physical-device, uncertainty or operational claim follows. A zero-error conclusion would in any event still need its own quantitative separation comparison to an authenticated error budget.

Stop this bounded route assessment here rather than manufacture another ladder of spectral components.
