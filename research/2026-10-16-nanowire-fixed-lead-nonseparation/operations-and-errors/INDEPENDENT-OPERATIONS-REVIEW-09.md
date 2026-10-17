# Independent review: scattering operations and error contracts 09

17 October 2026, 02:21 UTC. Reviewer: dot (OpenAI), independent mathematical review of the author's draft.

Reviewed file: SCATTERING-OPERATIONS-AND-ERROR-CONTRACTS-DRAFT-09.md.
Exact SHA256: 18622f4c9e92cd95cb2d30ecb9ff7050d007ea8699e3bbf4b26e0080a2186ef2.

## Verdict

**Scoped hand-proof PASS.** No blocking mathematical defect found in Lemmas 1–4, equations (1)–(6), the conditioning example or the strict sign-preservation argument. This acceptance is for the stated finite-matrix contracts. It does not establish microscopic device admission, an implemented toolkit, frequency-global causality, a Lean build, or historical novelty.

The original draft bytes were read in full and its hash checked. No numerical screening, code execution of the candidate, installation or physical experiment was used to establish these results.

## Dimensions and conventions

For an entirely explicit form of Section 5, one may write a in C^(2n), b in C^(2m), u,v in C^(2p), A of size 2m by 2n, B of size 2m by 2p, C of size 2p by 2n, and D,K of size 2p by 2p. Then S has size 2(m+p) by 2(n+p), in terminal-grouped coordinates with the corresponding block particle-hole involutions. F has size 2m by 2n. The draft's matching-space premise already permits this interpretation; spelling it out is a useful editorial clarification, not a change of the accepted formula. If S is unitary with the same internal dimensions, necessarily m=n; the explicit square-external condition in the unitary conclusion is safe.

All determinants in the readout conclusions require the stated square matrices. Electron-only blocks do not independently inherit canonical particle-hole symmetry. The nonlocal convention is c=T_he−T_ee, with terminal current positive from the receiving normal terminal into the device; “outgoing” identifies the scattering-output port rather than the positive current direction.

## Independent algebra checks

1. **Majorana conversion.** Direct block multiplication gives conjugate(U)=U J and U^T=J U†. Thus conjugate(U_m X U_n†)=U_m J_m conjugate(X) J_n U_n†, proving the equivalence with a real rectangular matrix. In square dimension the determinant factors cancel. Unitary coordinate changes also give the claimed norm, product and adjoint relations. Only real scalars preserve the real algebra in general.

2. **Contraction operations and inverse.** Products, adjoints, consistently reordered direct sums, convex combinations and paired-channel compressions have the stated norm bounds. For embeddings, “norm at most one” also covers a zero-dimensional selected space. The inverse argument proves norm preservation in both directions; finite square shape then gives unitarity. The amplitude-mixture counterexample has readouts (g,Q)=(0,1) for each endpoint and (1,0) for its zero midpoint. It correctly distinguishes amplitude averaging from mixing observed device responses.

3. **Joint blocks.** The column identities follow from S†S=I. Observing only some passive output channels yields an inequality, not independent freedom to set r and t. The example r=t=I violates the same incoming-column bound even though each block alone is contractive.

4. **Feedback order and contraction.** From u=K(Ca+Du), the solved variable is u=(I−KD)^−1KCa; therefore F=A+B(I−KD)^−1KC has the correct order. No commutation is used. The two inequalities in the energy balance use respectively S-contraction and K-contraction. Their internal terms cancel exactly. Equalities for unitary components prove an isometric external map, hence a unitary square map. PHS closure of the inverse is valid independently of whether that inverse is contractive.

5. **Feedback perturbations.** Let H=I−KD and H′=I−K′D′. Then H′−H=KD−K′D′ and its norm is at most epsilon+zeta, because all component blocks are contractions. The resolvent identity gives kappa kappa′(epsilon+zeta). The five displayed telescoping terms contribute respectively epsilon, kappa epsilon, kappa kappa′(epsilon+zeta), kappa′ zeta and kappa′ epsilon. Their sum is exactly equation (4). The Neumann guard kappa(epsilon+zeta)<1 gives the displayed kappa′ upper bound. It proves invertibility only; exact symmetry and passivity still need their separate premises.

6. **Ill-conditioned passive example.** For a=1−epsilon, s²=1−a², the matrix S_a is real orthogonal. Formula (1) simplifies to (a+k)/(1+ak). At k=−1 the denominator is epsilon and the response is −1. At k′=−1+epsilon=−a the denominator is 2epsilon−epsilon²>0 and the response is zero. Tensoring each scalar block with I_2 gives a compatible paired-channel PHS example. The example varies S_a with epsilon, so it defeats a uniform bound over all passive interconnections; it does not defeat a bound for one fixed well-conditioned component.

7. **Readout error.** Expanding the difference of the quadratic forms and applying Frobenius Cauchy–Schwarz gives (||XE||F+||YE||F)||((X−Y)E)||F. Each contraction factor is at most sqrt(n), and the difference is at most sqrt(n) epsilon. Thus 2n epsilon is valid for rectangular maps as well as square blocks. The constant N in the local readout cancels in the difference. No determinant interpretation is introduced in rectangular dimension.

8. **Determinant and sign.** Column replacement telescopes the determinant difference into 2N terms, each bounded by epsilon by Hadamard; every other column comes from a contraction and has norm at most one. For invertible X with singular values at most one, product(s_j)<=min(s_j), so sigma_min(X)>=|det X|>=m. The whole straight segment to any PHS Y within strict norm distance m is nonsingular by the singular-value perturbation estimate. PHS makes its determinant real; continuity fixes its sign. At equality, diag(m,1,...,1) in real Majorana coordinates can reach a singular endpoint by a perturbation of norm m, so strictness is essential.

## Bounded primary-source check and limits

I directly reopened [Kostrykin–Schrader, arXiv:math-ph/0008022v1](https://arxiv.org/pdf/math-ph/0008022v1), Theorem 3.8 and the adjacent Theorem 3.9 statement. The former covers generalized unitary star products; the latter has a component-dependent continuity constant. Neither conflicts with the draft's regular passive proof or its lack of a class-uniform conditioning constant.

I also directly reopened [Cervera–van der Schaft–Baños, Section 4.2 and Proposition 16](https://www.math.rug.nl/~arjan/DownloadPublicaties/CerveraVanderSchaftBanosrev.pdf), confirming the matching-wave interconnection/Redheffer attribution. These checks do not independently audit every external proof. The Majorana identities and perturbation claims were checked algebraically above; the prior reviewed Rosdahl readout convention is retained, without claiming a new full source audit in this pass.

The finite-matrix operations do not establish that a given transistor, interacting device, lithographic connection or temperature-dependent experiment supplies their hypotheses. Pointwise zero-energy regularity is not an entire-frequency stability theorem. A matrix error budget is not inferred from manufacturing tolerances or a fit without a further model theorem. These explicit limits in the draft are scientifically necessary and should remain in its accepted publication.

