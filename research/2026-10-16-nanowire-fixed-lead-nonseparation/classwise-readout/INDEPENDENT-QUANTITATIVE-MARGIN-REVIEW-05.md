# Independent review of the quantitative local-conductance margin

**Date:** October 17, 2026, 01:00 UTC. **Reviewer:** dot, working with Nolan, in a separate review pass from the candidate's construction. **Verdict:** scoped hand/source review PASS. No blocking mathematical correction found. No numerical execution or Lean verification was performed for this review.

## Exact reviewed object

`QUANTITATIVE-MARGIN-ROOT-CANDIDATE-05.md`, SHA-256 `4e7e6952e175dd999b161dffe3ff38b45fde256d5d0d581fb5efe5d1c76c59cc`.

The claim concerns a 4 × 4 contractive reflection matrix with canonical zero-energy particle-hole symmetry

\[
r=\begin{pmatrix}A&B\\\overline B&\overline A\end{pmatrix},
\qquad g=2-\operatorname{tr}(AA^\dagger)+\operatorname{tr}(BB^\dagger),
\]

where A and B are 2 × 2. It concludes det r ≥ (1−g)^4 > 0 when g < 1, and det r ≥ (g−3)^4 > 0 when g > 3. The physical range is 0 ≤ g ≤ 4. Neither statement certifies a negative label or claims completeness.

## Algebra checked

1. **Row versus column contraction.** The proof legitimately uses rr† ≤ I: a square contraction has both row and column inequalities. Its upper-left block gives I−AA†−BB† ≥ 0. Therefore X = I−AA†+BB† is positive semidefinite and has trace g. It follows that X ≤ gI and AA†−BB† ≥ (1−g)I. This is not an inference from trace alone without positivity.

2. **Inverse order.** A is invertible and σ_min(A)^2 ≥ 1−g. Also AA† ≤ I. With C = A^−1 B, congruence of the previous inequality gives

\[
I-CC^\dagger\ge(1-g)A^{-1}(A^{-1})^\dagger\ge(1-g)I.
\]

The second inequality uses ||A|| ≤ 1. It does not incorrectly interchange A with B or their inverses. Thus ||C||² ≤ g, and entrywise conjugation preserves this norm.

3. **Schur factor and positive sign.** For the off-diagonal homotopy r_u, the lower Schur complement is

\[
\overline A-u^2\overline B A^{-1}B
 =\overline A\bigl(I-u^2\overline C C\bigr).
\]

Its second factor is invertible because ||u² conjugate(C)C|| ≤ g < 1. Every r_u preserves particle-hole symmetry, so its determinant is real. It is positive at u = 0 and cannot change sign without vanishing. The homotopy need not be a family of physically realized wires; it is used only to prove an algebraic sign statement.

4. **Quantitative determinant bound.** Both singular values of I−conjugate(C)C are at least 1−g, and both singular values of A are at least sqrt(1−g). Therefore |det A|² ≥ (1−g)² and |det(I−conjugate(C)C)| ≥ (1−g)². The established positive sign yields the advertised fourth-power bound. It is a sufficient conservative bound; sharpness is not established.

5. **High-conductance branch.** Right multiplication by the permutation P exchanging the full electron and hole sectors sends A to B and B to A. It preserves the canonical symmetry and contraction, and g becomes 4−g. For two electron channels det P = (−1)^2 = +1, so the original determinant is unchanged. The two-channel restriction matters here.

6. **Readout and numerical implication.** An authenticated interval [y−η,y+η] can be used monotonically as stated. It must contain a physically possible g; an inconsistent interval cannot certify a device. For the finite plus example, g < 1/250 gives det r > (249/250)^4 = 0.984095744256. This is weaker than its direct interval certificate det r > 0.996, but uses local conductance alone. The minus example's g near 1.209 lies outside the sufficient test.

## Source and physical binding checked

The primary [Beenakker et al., arXiv:1012.0932v3](https://arxiv.org/pdf/1012.0932), §II, Eqs. (2.1)–(2.3), uses the same canonical particle-hole block relations and counts spin in the channel number. Its reduction of conductance to twice the Andreev probability additionally assumes unitary reflection. Candidate 05 correctly retains only contractivity, allowing transmission to the other lead.

The primary [Rosdahl et al., PRB 97, 045421](https://pure.tudelft.nl/ws/portalfiles/portal/46877558/PhysRevB.97.045421.pdf), Eqs. (3)–(5), supplies the transport convention already audited in certificate 03. With current into the device, the local value is 2−R_ee+R_he. This is the candidate's g; there is no extra spin or Nambu factor.

The finite-pair packet uses electron indices (0,2) and hole indices (1,3). Its real particle-hole matrix J = σ_y τ_y maps e_0 to −h_3 and e_2 to h_1. Ordering the new basis as (old 0, old 2, −old 3, old 1) therefore gives the canonical swap symmetry. This is a simultaneous real orthogonal basis change of input and output channels. It preserves the determinant and sector-summed probabilities. The previously established full-scattering unitarity supplies reflection contractivity. These checks bind the theorem to every wire satisfying the declared loss-free zero-energy assumptions, not just to the rational finite pair.

No source theorem about protected Majorana states, thermodynamic topology or the original Taylor code is being imported. Finite-temperature averaging, nonzero-bias data, a floating condensate, missing modes, and unmodeled calibration or dissipation require a separate admission argument.

## Relation to companion candidate 04 and prior work

Candidate 05's clarification of candidate 04's algebraic ambiguity example is correct: take the right reflector to be a copy of the respective left reflector in each model. Then both full determinants are +1 and both aggregate conductance matrices agree. A single common right reflector would not give that total-determinant claim. This remains an algebraic scattering comparison; it is not a connected Rashba-chain realization or a multi-setting physical counterexample.

The matrix inequalities, Schur factorization, homotopy sign argument, Landauer–BdG formula and particle-hole relation are classical. This review checks the stated application and its source conventions. It is not an exhaustive historical-priority search and does not establish novelty. Acceptance is a scoped hand proof, not an execution result, formal kernel proof, experimental validation, or complete identification theorem.
