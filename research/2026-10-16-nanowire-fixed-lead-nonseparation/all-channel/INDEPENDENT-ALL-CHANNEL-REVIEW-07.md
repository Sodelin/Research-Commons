# Independent hand review: all finite channel conductance region

17 October 2026, 01:11 UTC. dot (OpenAI), working with Nolan. Separate mathematical review of the complete candidate, without numerical execution or formal compilation.

## Exact object and verdict

Reviewed `ALL-CHANNEL-CONDUCTANCE-REGION-CANDIDATE-07.md`, SHA256 `a8a2fafe2a8acc613997284f345b97f9c5b36fd88b741539fe6b31b98c4470e5`.

**Scoped hand-proof PASS.** No blocking defect found in the all-N inequalities, entire algebraically attainable region, explicit extremizers, or stated margin/error compatibility rule. This accepts the declared contractive PHS matrix theorem. It does not accept physical realization of all those matrices by a fixed microscopic wire, historical novelty, experimental validity, or original-paper source-family admission.

## Checks

1. **Basis and normalization.** The displayed U is unitary and converts canonical PHS r into the stated real block matrix. Expanding the trace of its covariance's upper-right block gives ||A||_F²−||B||_F²; real cross terms cancel under trace. The fixed permutation to adjacent Majorana pairs makes J a direct sum of J₂ blocks with Pf(J)=1. Thus sum K_(2j−1,2j)=N−g, and Pf(K)=det(R)=det(r). The Frobenius inner-product factor is correct. Spin is counted in N and g uses e²/h; there is no extra Nambu factor.

2. **Covariance admission.** For a real contraction R, K=RJRᵀ is real antisymmetric with norm at most one. Its real orthogonal normal form has block parameters |λ_j|≤1, including singular and endpoint cases. The proof does not assume positive determinant or an orientation-preserving diagonalization.

3. **Explicit positive auxiliary state.** The Jordan–Wigner generators obey the Clifford relations and −ic_(2j−1)c_(2j)=Z_j. Rotated d generators obey the same relations. Their paired parity operators are commuting Hermitian involutions, so every factor I+λ_j Z′_j is positive and their product is positive. A nonempty even Clifford monomial has trace zero by conjugation with a generator inside it; a nonempty odd monomial has a generator outside it because the total dimension is even. The asserted trace orthogonality and normalization therefore hold, including the full-length product. Expansion gives each paired covariance λ_j and vanishing cross-pair expectations.

4. **Orientation and total parity.** The full Clifford product transforms by det(O), so product Z′_j=det(O) P. This gives EρP=det(O) product λ_j=Pf(K), with the same sign as the vacuum calibration. No unitary implementation of an orientation-reversing O is assumed or needed. The trace of the number operator is exactly g/2. The auxiliary density is only a proof construction and need not be the physical wire state.

5. **Inequalities for every finite N.** The commuting occupation projections have integer total eigenvalues k in [0,N], for which (−1)^k≥1−2k. The operator inequality can be averaged in any density, even one not commuting with occupation. Applying it to particle and hole number yields Q≥1−g and (−1)^N Q≥g−(2N−1). Bounds 0≤g≤2N and |Q|≤1 follow as stated. For N=1 these imply Q=1−g exactly; for N=2 they recover Q≥|g−2|−1. The parity-dependent high edge is essential.

6. **Endpoint constructions.** The one-mode r_s has eigenvalues 1,s and determinant s, and its direct conductance calculation gives 1−s. For the two-mode block, Pauli anticommutation gives r_θ²=I, while det(A+B)=det(A−B)=−1 gives determinant +1. Its conductance is 4 sin²θ. Direct sums add conductance and multiply determinant. Consequently the positive and negative flat edges and both sloping edges cover exactly the stated intervals. The no-two-mode-block cases N=1 and N=2 reduce to the specified singletons and cause no gap. Full electron/hole exchange has determinant (−1)^N and sends g to 2N−g.

7. **Every intermediate determinant.** At fixed g, the real antisymmetric operator-norm unit ball intersected with the displayed affine constraint is convex and compact. Its continuous scalar Pfaffian image is a compact interval. Crucially, this is not a relaxation: for every K in that slice, R=O direct-sum diag(λ_j,1) is contractive and satisfies RJRᵀ=K. Reversing the fixed basis change produces an actual PHS reflection contraction with that g and Q. The endpoint constructions therefore prove the entire claimed attainable region, not only outer bounds. No claim of microscopic realization follows.

8. **Optional full-scattering dilation.** The displayed block matrix is real orthogonal by the standard square-root intertwining identity, which also follows directly from singular-value decomposition. Replacing R by tR for t from zero to one gives a continuous orthogonal family. At zero the matrix exchanges two blocks of dimension 2N, hence determinant (−1)^(2N)=+1. This proves the stated full-determinant assertion. Nambu conversion on both leads supplies unitary PHS scattering but adds no locality, contact, fixed-hopping or multi-setting realization theorem.

9. **Margin compatibility and noisy reports.** Projecting the exact region onto g at Q≥m and Q≤−m gives precisely the table, for 0<m≤1. For even N the positive range is [0,2N], negative [1+m,2N−1−m]. For odd N they are [0,2N−1−m] and [1+m,2N]. This includes the N=1 excluded interval under the promise. Intersecting a closed error interval with these closed ranges handles equality correctly: one intersection certifies the promised label, two permit algebraic opposite-margin models, and neither is inconsistent with the combined premises. The source's margin promise must be independently established. This is distinct from unconditional numerical certification of Q≥m.

10. **Unknown finite channel count.** The universal lower edge does not depend on N. A consistent authenticated interval with upper endpoint u<1 implies Q≥1−u>0. Its interpretation still requires the same conductance and symmetry premises. High-edge inference needs channel count and parity.

## Strength, attribution and review boundary

The proof is self-contained finite-dimensional linear algebra and Clifford/occupation algebra. It explicitly attributes the covariance and parity ingredients and the unitary-reflection predecessor. This pass independently checked the displayed mathematics; it did not repeat a comprehensive literature search or independently re-audit every theorem in the external primary sources. The separate directed prior assessment remains the source for historical comparisons. No novelty conclusion follows from a bounded search.

Acceptance is an exact hand-proof review, not a Lean/kernel certificate, independent numerical implementation, laboratory test, or demonstration that a connected Rashba family fills the algebraic region. Finite-temperature, finite-bias and floating-condensate measurements, uncounted modes, and unmodeled errors require separate admission. Positive or negative finite reflection determinant is not by itself protected-Majorana or thermodynamic-phase certification.
