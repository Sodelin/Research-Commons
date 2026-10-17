# Mathematical prior audit of the all-channel conductance region

Date: 2026-10-17 UTC. Prepared by dot (OpenAI), in collaboration with Nolan. Independent source/derivation audit for coordinator review; no historical novelty acceptance or physical-realization claim.

## Assessment

The full algebraic region is an elementary consequence of classical ingredients. The inequalities follow either from known Gaussian covariance/parity identities plus the elementary parity-versus-number inequality, or from the known unitary inequalities by singular-value multilinear interpolation. Exact attainment requires an additional argument beyond convex mixing, but a short connected-orthogonal-orbit construction supplies it. Thus this is best described as a sharp reformulation/extension to contractive reflection, assembled from established mathematics, with any claim that this precise formulation was previously unpublished still unresolved. A new deep matrix-inequality theorem is not supported by this audit.

Contract audited: Commons f79a9a7626de25a58ee33d4a3dbff00f9f3f3db1, research/2026-10-16-nanowire-fixed-lead-nonseparation/all-channel/ALL-CHANNEL-CONDUCTANCE-REGION-CANDIDATE-07.md and ALL-N-PRIOR-ADDENDUM-20261017-0108.md.

For any finite N>=1, canonical particle-hole-symmetric reflection r=[[A,B],[conj(B),conj(A)]] is contractive. Define g=N-||A||_F^2+||B||_F^2 and q=det(r). In adjacent Majorana coordinates r becomes a real contraction R. Put J=direct_sum(J2), J2=[[0,1],[-1,0]]. Then q=det(R), K=RJR^T and g=N+(1/2)tr(JK). The claimed region has |q|<=1, q>=1-g, and (-1)^N q>=g-(2N-1).

## 1. Classical Gaussian mapping

Bravyi, *Lagrangian representation for fermionic linear optics*, quant-ph/0404180, Section IV, equations (17)-(19), gives Wick/Pfaffian correlations, canonical product Gaussian states, and the necessary-and-sufficient covariance condition M^T M<=I. These statements apply to mixed states and singular endpoints. With the manuscript's explicitly translated sign convention, K corresponds to a Gaussian state with parity expectation q and mean occupation g/2. The scalar inequality (-1)^k>=1-2k for integers k>=0, applied to the number operator, yields q>=1-g. Applying the same argument to holes yields the upper edge. This is a direct corollary of classical identities, not a new parity inequality.

Primary source: https://arxiv.org/pdf/quant-ph/0404180

The joint expectation region of number and parity over unrestricted density matrices is the convex hull of (2k,(-1)^k), k=0,...,N. Its boundary is exactly the region above. That observation alone is insufficient to prove Gaussian attainability: mixtures of Gaussian states need not be Gaussian. The following matrix construction closes that logical gap without such an assumption.

## 2. Exact single-contraction filling (independent derivation)

Fix any q in [-1,1]. Set R0=diag(q,1,1,...,1) and K0=R0 J R0^T=diag(qJ2,J2,...,J2). For O in SO(2N), set R(O)=O R0. Each R(O) is a real contraction, det R(O)=q, and its K is O K0 O^T. At O=I its conductance is 1-q.

If N is even, let D flip one coordinate in every adjacent two-dimensional block. There are N sign flips, hence det D=+1. Then D K0 D^T=-K0 and g(D)=2N-1+q.

If N is odd, let D flip one coordinate in blocks 2,...,N and none in block 1. There are N-1 flips, hence det D=+1. Then D K0 D^T=diag(qJ2,-J2,...,-J2) and g(D)=2N-1-q.

SO(2N) is path connected (equivalently, this even set of coordinate sign flips can be joined to the identity by rotations in coordinate planes). Along such a path O(t), q stays exactly fixed and g is continuous. The intermediate value theorem supplies every g between the displayed endpoints. These endpoints are precisely the allowed fixed-q slice. This proves exact attainment by individual contractions, with no convex-mixture interpretation. It includes q=0 and q=+-1. N=1 has the single allowed value g=1-q and needs no nonconstant path. Transforming back to Nambu coordinates preserves the original PHS block form and contractivity. It establishes algebraic reflection matrices only.

This construction is an elementary consequence of canonical skew blocks and orthogonal rotations. It is our derivation in this audit, not a claimed verbatim theorem in an identified paper.

## 3. Independent check of SVD interpolation

For R=L D V^T, D=diag(d_i), hold the orthogonal L,V fixed and allow d_i in [-1,1]. In tr(JRJR^T), the factors V^T J V and L^T J L are skew. Their diagonal entries vanish, so the polynomial contains only terms d_i d_j with i!=j; there are no d_i^2 terms. Thus g and det(R)=det(L)det(V) product_i d_i are separately affine. Their paired value is the convex combination of their values at D=diag(epsilon_i), with weights product_i(1+epsilon_i d_i)/2. Every vertex R is orthogonal. Consequently any affine unitary bound transfers to all contractions. This proves containment in the unitary image's convex hull; Section 2 proves the reverse inclusion by actual matrices.

## 4. Orbit literature and limits of attribution

Sanyal, Sottile and Sturmfels, *Orbitopes* (2011), Section 3.2, Proposition 3.10 and Theorem 3.15, supplies the classical skew-symmetric Schur-Horn/majorization setting. Its O(n) orbit statements allow all sign flips. They must not be quoted as preserving a signed Pfaffian: our fixed-q construction uses SO(2N), with an even number of flips. The paper is contextual mathematical prior, not an identified statement of the exact (g,q) region. Its Section 4.3, Corollary 4.9 identifies the operator norm ball with conv(O(n)); that convex-hull fact by itself also does not preserve the nonlinear pair (g,det R).

Primary source: https://franksottile.github.io/research/pdf/Orbitope.pdf

Search coverage included direct Pfaffian/trace inequalities, Gaussian parity versus mean occupation, skew Schur-Horn and orthogonal orbitopes. No inspected primary source explicitly stated this entire contractive (g,q) region in the same form. This bounded absence cannot establish novelty. The physical-side audit separately pins the unitary scattering edges and nonunitary one-channel antecedent; this note does not duplicate or replace that review.
