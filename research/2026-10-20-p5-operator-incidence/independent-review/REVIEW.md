# Independent hand review: general operator-incidence supplier

20 October 2026. Reviewer: dot (OpenAI), working with Nolan. Independent assistant-context hand/source review, not external peer review or Lean verification.

## Decision

**Scoped PASS** for the operator-incidence estimates, full infinite-filter bounds, anisotropic auxiliary-reference theorem under its stated margin, and the unclosed actual differential inequality. **No full P5 result is accepted.**

Reviewed artifact: OPERATOR-INCIDENCE-AND-ACTUAL-JOIN.md, original review-time SHA256 recorded in REVIEWED-SOURCE-SHA256.txt. The publication successor is ../PROOF.md; its status and provenance presentation have been updated without changing the mathematical assertions. The reviewed final addition justifying b0<=1 is a clarification of an already checked consequence, not a repair of an invalid estimate.

## Detailed proof checks

1. The Pauli-twirl conditional expectation estimate ||F-E_Z F||<=sum_(j in Z) I_j(F)/4 holds for arbitrary global operators. For a Z-supported B, [B,E_Z F]=0, giving ||[B,F]||<=||B|| sum_j I_j(F)/2. Apply this to [H_Z,A_(i,a)] with norm at most 2||H_Z|| and sum three axes. This yields exactly M_ij=3 sum_(Z contains i,j)||H_Z||. The symmetric row/column bound is 3kh, not a coefficient-incidence bound. No Pauli expansion of H_Z is used.

2. The unitary Heisenberg commutator differential comparison applies also to reversed time. Integrating M exp(rM) proves the moved-local-operator estimate. Integrating against the full exponential covariance envelope gives gamma tauB M(Id-tauB M)^(-1), with no finite-time truncation or assumed sign of Phi. Summing with the column bound gives eta. The separate I([H,A_p])<=12kh estimate gives beta=12 gamma kh tauB/(1-v tauB). The direct operator difference gives q<=2 gamma h tauB. These statements retain general operator incidence h.

3. The denominator is admissible: the original lower bound and envelope imply b0 gamma<=Re k0_p<=|k0_p|<=integral |Phi_p|<=gamma, hence b0<=1 for a nonzero bath scale. The displayed use of k<=nu and k<=m follows the stated neighborhood convention. With that convention v tauB<=1/(4*2^m)<1. The reviewed text states the short b0<=1 reason explicitly.

4. In the negative dissipator estimate, ||D[Q]F||<=||Q|| (||[F,Q]||+||[Q^dagger,F]||)/2. Dividing by 2b_p and using both eta bounds gives q eta/(2b0 gamma), with the claimed final constant. This is influence-to-operator control, not boundedness of the full perturbation in the influence seminorm.

5. The anisotropic noise intertwiner is correct. Commutation with a fixed Pauli swaps the two transverse one-site Pauli eigenspaces, so swapping their noise coefficients intertwines the generators. The new rates remain nonnegative and retain the same lower floor.

6. The important damping gate is valid as written. For the instantaneous G=[A_p,F_t], E_i G=0. Decompose the intertwined noise as g(E_i-Id)+D_rem; D_rem is a genuine Pauli-noise generator after subtracting the common b_min at that site only. K=D_rem+i[H,.] generates a unital CP operator-norm contraction on the whole space. At the current G, the homogeneous derivative is (K-g Id)G. The first-order comparison with exp(dt K), with O(dt^2) remainder, gives D^+||G||<=-g||G|| plus the Jacobi forcing norm. This does not require exp(tK)G to remain locally traceless. There is no hidden factor of two or need to replace H by its even part. A finite-time factorization through the locally traceless subspace would have been invalid; the draft explicitly does not make it.

7. Therefore the Metzler comparison (-g Id+M) and integrated inverse (g Id-M)^(-1) are justified whenever rho(M)<g. Uniform scalar control requires g-3kh>0. Under h<=g/8 this is guaranteed for k=2 with margin at least g/4, but not for general k>=3. The initial estimate I(O_X)<=6|X|||O_X|| is valid and independent of ambient volume. A common lower bath floor may be used across volumes. No actual Redfield contraction is inherited from this reference theorem.

8. The exact perturbation Leibniz/Jacobi expansion retains V(delta_p F). The same-site nested-Pauli sum is 4I(F); the two Q terms yield 8qI. The two commutators with Q yield 2beta I. The homogeneous term gives 2q I_2. These prove the displayed actual differential inequality without assuming positivity of R*. The Pauli-word identities I(P)=4s and I_2(P)=16s^2 confirm that no ambient-volume-independent global I_2<=C I estimate is available. This is not a counterexample restricted to the actual reached family from fixed initial support.

## Independently authored finite evidence

I wrote check_noise_projection.py independently of the author's numerical script. It uses exact SymPy matrices and rational anisotropic rates on two qubits and verifies:

- 96 noise-intertwiner identities;
- 96 local isotropic damping identities;
- 1,536 projected Hamiltonian identities;
- 1,536 projected Jacobi identities.

All 3,264 checks pass. It additionally exhibits failure of invariance under the *unprojected* Hamiltonian. The projection identities are diagnostic cross-checks; the accepted proof uses the instantaneous argument and does not depend on this alternative projection construction. RESULT.json preserves the output. These finite tests establish only the displayed matrix identities in their tested basis, not the full analytic argument or original thermal admission. I did not rerun or adopt the author's broader-envelope bath fixture as a thermal check.

## Exact acceptance limits

Accepted: general-h first-gradient velocity 3kh; admitted full-filter commutator and influence suppliers; integrated anisotropic auxiliary-reference estimate under its explicit margin; the exact, still-unclosed actual join.

Not accepted or claimed: general-k reference admission from the original box, a reached-family integrated second-gradient bound, actual all-time response control, the original square-window comparison, removal of scalar drift, full P5, external novelty, thermal validity of numerical test fixtures, or formal verification. All arbitrary-state and full-filter requirements remain in force. The next master-facing task is the actual homogeneous term, not another substitution of reference contraction for actual evolution.
