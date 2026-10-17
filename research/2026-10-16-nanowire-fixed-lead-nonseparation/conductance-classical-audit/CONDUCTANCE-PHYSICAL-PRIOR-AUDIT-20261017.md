# Physical-scattering prior audit of the all-channel conductance region

17 October 2026, 04:25 UTC. dot (OpenAI), working with Nolan.
Status: source-led assessment for coordinating review. No historical priority, exhaustive literature coverage, experimental validation or Lean verification is claimed.

## Assessment

The necessity inequalities should be described as a classical extension of established unitary-scattering bounds. The exact nonunitary one-electron-channel identity also has a direct published antecedent. The complete contractive feasible-region statement and its constructive filling were not located explicitly in the inspected physical-scattering sources. This bounded negative search does not establish novelty, especially because the mathematical covariance/convexity equivalents require their own audit.

Target: a canonical particle-hole-symmetric contraction r of size 2N, N>=1 electron channels including spin, at zero energy. In e²/h units, g=N-||r_ee||_F²+||r_he||_F² and Q=det r. Accepted packet07 states 0<=g<=2N, |Q|<=1, Q>=1-g, (-1)^N Q>=g-(2N-1), and exact abstract attainability. A reflection subblock can be nonunitary while its full two-terminal scattering matrix is unitary. Neither abstract attainability nor a unitary dilation proves realization in a fixed microscopic Rashba family.

## Exact source-to-result mapping

### Wimmer et al. 2011: arbitrary-channel unitary lower edge

[Quantum point contact as a probe of a topological superconductor](https://arxiv.org/pdf/1101.5795), v2, §II Eq.(3), Appendix B, and §IV. The published formula is g=1-Q+4 sum' R_n. Its nonnegative remainder immediately gives Q>=1-g for unitary reflection. Zero voltage and temperature are explicit; spin is included in the channel sum. Particle/hole exchange gives the opposite edge with determinant multiplier (-1)^N. This source already supplies the unitary all-N ancestor, not merely a qualitatively related transport observation. It does not directly allow |Q|<1.

### Beenakker et al. 2011: the full unitary boundary segments

[Random-matrix theory of Andreev reflection from a topological superconductor](https://arxiv.org/pdf/1012.0932), §III.A Eqs.(3.1)-(3.6). The class-D polar blocks parametrize unitary PHS reflection. For even N, Q=+1 permits g in [0,2N], while Q=-1 permits [2,2N-2]. For odd N, these ranges are [0,2N-2] and [2,2N]. At N=1 they reduce to isolated points. The continuous Andreev eigenvalue parameters establish attainment throughout each segment; endpoints follow by continuity. These are exactly the Q=±1 sections of packet07. The paper's probability distributions are not required for this implication. Its polar decomposition is unitary, so it cannot be applied unchanged to a lossy reflection block.

### Diez et al. 2012: parity-dependent unitary edges

[Andreev reflection from a topological superconductor with chiral symmetry](https://arxiv.org/pdf/1206.3079), §II Eqs.(9)-(10) and following paragraph. The principal BDI index is an integer, not our determinant. The authors explicitly extend their conductance bounds to class D with binary index q=0,1. Translate q=(1-Q)/2 and their G0=2e²/h. This recovers the unitary lower and parity-dependent upper edges. One must not identify their BDI Q with a continuous reflection determinant.

### Marciani, Schomerus and Beenakker 2015/2016: nonunitary N=1 identity

[Effect of a tunnel barrier on the scattering from a Majorana bound state in an Andreev billiard](https://arxiv.org/pdf/1506.05995), §VIII Eqs.(48)-(52), §IX. Their real 2x2 reflection r is a subblock of full orthogonal S in O(3). Eq.(48) gives g_A=(1/2)Tr(I-r tau_y r^T tau_y). The 2x2 determinant identity reduces this to g_A=1-det r; Eq.(52) displays g_A=1-cos(theta). Thus the nonunitary-reflection one-electron-channel result is already explicit through their parametrization. Their N counts Majorana channels; N1=2 corresponds to our N=1. The full-scattering determinant in §IX must not be confused with det r. This paper studies distributions and averages, not an inspected full arbitrary-channel contractive feasible-region theorem.

### Das Sarma, Nag and Sau 2016: visibility and dissipative conductance

[How to infer non-Abelian statistics and topological visibility...](https://arxiv.org/pdf/1603.00041), Appendix A Eqs.(A1)-(A8), §V and Fig.5 discussion. The source explicitly defines nonquantized Q=det r, gives the multichannel BTK conductance, and relates dissipative numerical visibility to conductance. Its approximately half-height diagnostic is a model-based conclusion, not the arbitrary-contraction necessity-and-attainability theorem. Our low-g positivity bound cannot be inverted into a universal high-g negative-sign rule. No paper-error inference is made.

### Later physical context, with bounded inspection

[Das Sarma and Pan 2023](https://arxiv.org/pdf/2305.06837), model/results/conclusion: local/nonlocal conductance, density of states and visibility are compared across disorder and length regimes. This is a microscopic diagnostic study, not an identified arbitrary-channel contractive region proof.

[Araya Day et al. 2025](https://arxiv.org/pdf/2504.01069), §3 and Appendix: lead self-energy and coupling-sensitive visibility are central. This supports caution about physical interpretation of Q and does not supply a universal conductance-to-protected-phase identification theorem. The earlier directed comparison already records the effective two-mode mechanism and its scope.

[Beenakker review](https://arxiv.org/pdf/1407.2131), class-D scattering and conductance sections, consolidates the orthogonal/unitary framework and established topological conductance lower bound. It is contextual corroboration, not an additional independent proof of the contractive extension.

## A precise implication beyond matching titles

The following is a mathematical comparison argument, not a claim that the cited authors wrote it. It reuses our previously recorded SVD/separate-affinity route.

Write the real Majorana contraction M=U diag(s) V^T, with U,V orthogonal and each s_i in [0,1]. For canonical real antisymmetric J, use

    g(M)=N-(1/2)Tr(J^T M J M^T).

Set A=U^T J U and B=V^T J V. Both are antisymmetric, so their diagonal entries vanish. The quadratic trace is a sum of coefficients times s_i s_j with i!=j. Therefore g(M), det M, and det M+g(M)-1 are separately affine in the coordinates s_i. Multilinear interpolation on [-1,1]^(2N) expresses (g(M),det M) as a convex combination of the same pair evaluated at U diag(epsilon) V^T, epsilon_i=±1. Every vertex is orthogonal and hence corresponds to unitary PHS reflection. Wimmer's inequality at all vertices proves the contractive lower edge; particle/hole exchange proves the upper edge.

The convex hull of the known unitary segments above is exactly the polygon described by packet07's inequalities. Thus necessity and the polygon shape are linked directly to established physics plus elementary matrix interpolation. This is stronger attribution than saying only that similar unitary bounds existed.

However, a convex combination of observable pairs does not automatically arise from one matrix, because the map M -> (g,Q) is nonlinear. A full attainability claim still requires a construction or a connected-fibre argument. Packet07 contains such an argument. This audit did not find it in the inspected scattering papers, and makes no assertion that it is historically new or absent elsewhere.

## Search coverage and practical interpretation

Fresh targeted queries covered conductance/determinant bounds, topological visibility inequalities, nonunitary/subunitary/contractive reflection, Marciani, and later 2023-2026 sources. Full relevant sections were read for the papers listed above; this was not a line-by-line audit of every cited work, supplement, thesis or later paper. An APS2021 fulltext request returned an internal retrieval error; no claim from that unread route is imported. The 2026-directed queries did not produce a verified exact full-region match. Search failure is not a priority certificate.

The useful contribution can be described conservatively as an explicit, reviewed contractive-scattering synthesis with complete abstract feasibility and calibrated abstention rules, built on established conductance, covariance and matrix methods. The most important remaining application work is independently justified energy-resolution, temperature, Hamiltonian-drift and measurement budgets; algebraic sharpness does not provide those device budgets.
