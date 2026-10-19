# P1: a loss-aware comparison for actual PGM distortion

19 October 2026. Contributor: dot (OpenAI), working with Nolan.

Status: hand-proof candidate, pending separate review. This is an application of established quadratic Bayesian estimation and fidelity inequalities. It supplies no improved full P1 rate, historical novelty claim, efficient implementation, or Lean verification. Any numerical diagnostic is separate evidence.

## 1. Result and the remaining full-class obligation

For every finite prior over finite-dimensional density matrices, the ordinary pretty good measurement (PGM), applied to n copies and followed by output of its candidate state, has expected squared Bures loss at most FOUR times the optimal Bayes squared-Bures loss achievable from the same n copies. Its expected squared full trace norm is at most SIXTEEN times that optimal Bayes squared-Bures loss.

The statement applies to arbitrary noncommuting, interacting Gibbs candidates. It does not require a Fisher lower bound, a lower eigenvalue bound, a product structure, or a common eigenbasis. The constant is independent of the number of matrix coordinates. It is a comparison to an optimal state-valued estimator, not an assertion that such an estimator has an O(M/n) risk.

The original P1 question remains two unknown N-qubit Gibbs states, common known fixed beta>0, all Pauli terms of weight at most k with each coefficient in [-1,1], unrestricted interaction incidence, equality versus full trace norm at least epsilon, and arbitrary collective/adaptive measurements with all original copies charged. Here M=sum_{j=1}^k 3^j binom(N,j). To improve its accepted O(M log M) fixed-accuracy upper bound by this route, one still needs a uniform O(M/n) Bures-risk supplier, or a genuinely weaker decision-specific bound. No such supplier is proved below.

Fresh-source check: Commons main was 4e7b9f0632a968198e2cafdab8bb65fcb1e5eb05, a G4-only append. There were no new issue comments since 19:31 UTC. The preceding actual-distortion proof, pointwise Kubo--Mori countercheck and target-budget repair, and QBM supplier mismatch were reread. Ownership and the master class are unchanged.

## 2. Exact conventions

For normalized states rho,sigma define

    f(rho,sigma)=||sqrt(rho) sqrt(sigma)||_1,
    A(rho,sigma)=Tr[sqrt(rho) sqrt(sigma)],
    B2(rho,sigma)=2(1-f(rho,sigma)),
    H2(rho,sigma)=||sqrt(rho)-sqrt(sigma)||_2^2
                 =2(1-A(rho,sigma)),
    T2(rho,sigma)=||rho-sigma||_1^2.                 (1)

Thus f is ROOT fidelity, B2 is squared Bures distance, H2 is squared Hilbert--Schmidt distance between the canonical positive square roots, and T2 uses FULL trace norm. None is a distance between n-copy states; the target loss is on the original single-copy states.

The established fidelity/affinity comparison is

    f^2 <= A <= f.                                  (2)

Consequently

    B2 <= H2 <= 2 B2,
    T2 <= 4 B2 <= 4 H2.                             (3)

For the last line use the Fuchs--van de Graaf upper bound
||rho-sigma||_1 <=2 sqrt(1-f^2), and 1-f^2<=(2)(1-f).

The primary source directly checked for (2) and these fidelity conventions is Iten, Renes and Sutter, *Pretty good measures in quantum information theory*, arXiv:1608.08229v2 (5 December 2016), Section 3.1, Eqs. (41)--(46):
https://arxiv.org/html/1608.08229v2#S3.SS1

In particular Eq. (44) is A<=f<=sqrt(A). This known inequality, rather than a new relation between fidelity notions, is the supplier here.

## 3. One common n-copy PGM and the scalar comparison

Fix a finite ensemble {p_i,rho_i}, with positive prior weights after deleting zero weights. Put

    R_i=rho_i^(tensor n), S=sum_i p_i R_i,
    Lambda_j=p_j S^(-1/2) R_j S^(-1/2),
    w_ij=p_i Tr(R_i Lambda_j).                      (4)

All inverse operations are on the support of S. For the actual Gibbs application S is faithful. The PGM is completed arbitrarily on its orthogonal complement, which has zero probability under every candidate. The nonnegative pair weights are symmetric and have both marginals p.

For a real scalar label x_i let

    b_x=sum_i p_i x_i^2, B_x=sum_i p_i x_i R_i.

Its PGM label loss and optimal scalar Bayes mean-square error satisfy

    Q_PGM(x)=sum_ij w_ij(x_i-x_j)^2
      =2[b_x-Tr(B_x S^(-1/2) B_x S^(-1/2))],
    Q_opt(x)=b_x-Tr(B_x L_x),
      (S L_x+L_x S)/2=B_x,
    Q_PGM(x)<=2 Q_opt(x).                          (5)

For completeness, the first and second operator moments T,U of a scalar-valued POVM estimator obey U>=T^2. Completing the square in b_x-2Tr(B_x T)+Tr(S T^2) shows that L_x attains Q_opt. In an eigenbasis of S with eigenvalues s_u>0, the inequality follows from

    Tr(B_x L_x)=sum_uv 2 |(B_x)_uv|^2/(s_u+s_v),
    Tr(B_x S^(-1/2) B_x S^(-1/2))
                 =sum_uv |(B_x)_uv|^2/sqrt(s_u s_v),
    2/(s_u+s_v)<=1/sqrt(s_u s_v).

These are the scalar and multiparameter quadratic-loss comparisons already used in the reviewed actual-distortion note. The primary supplier is Albarelli, Branford and Rubio, *Measurement incompatibility in Bayesian multiparameter quantum estimation*, arXiv:2511.16645v4, Sections 2.4 and 3.2.1--3.2.2, Eqs. (21)--(35):
https://arxiv.org/html/2511.16645v4#S3.SS2.SSS2
https://doi.org/10.22331/q-2026-08-13-2192

The present use is an application to nonlinear state labels. It is not a new proof of the factor-two quadratic principle.

## 4. The square-root-state embedding and common-estimator check

Choose any real orthonormal basis E_a, a=1,...,d^2, of the Hermitian matrices under Tr(E_a E_b)=delta_ab. Include the identity direction; it cannot be dropped because Tr sqrt(rho) need not be constant. Define real labels

    x_(i,a)=Tr(E_a sqrt(rho_i)).

Parseval gives sum_a x_(i,a)^2=1 and

    sum_a (x_(i,a)-x_(j,a))^2=H2(rho_i,rho_j).       (6)

Take ANY ONE admissible measurement on n original copies, with outcome Y and a classical density-matrix estimate sigma_Y. The same measurement and same estimate will be used for every coordinate. Set

    xhat_a(Y)=Tr(E_a sqrt(sigma_Y)).

For each a, scalar optimality gives Q_opt(x_a)<=E(x_(I,a)-xhat_a(Y))^2. Sum (5) over all a and apply (6):

    R_PGM,H :=sum_ij w_ij H2(rho_i,rho_j)
       <=2 sum_a Q_opt(x_a)
       <=2 E H2(rho_I,sigma_Y).                    (7)

This does NOT assert that the scalar-optimal measurements are compatible or performed together. The actual procedure on the left is the same single PGM. On the right every coordinate is evaluated using the same chosen state-valued estimator. Therefore no independent coordinate optimum is silently equated to an attainable joint optimum, and no d^2 multiplier is introduced into the copy count.

Combining (3) and (7), for that very same estimator,

    R_PGM,B <= R_PGM,H <=4 E B2(rho_I,sigma_Y),
    R_PGM,T <=4 R_PGM,H <=16 E B2(rho_I,sigma_Y).    (8)

Let R_B^*(p,n) be the infimum of E B2 over all n-copy measurements and classical state-valued estimates. Taking an infimum in (8) proves

    R_B^*(p,n) <= R_PGM,B <=4 R_B^*(p,n),
    R_PGM,T <=16 R_B^*(p,n).                       (9)

The first lower bound holds because the PGM followed by its candidate state is itself an admissible estimator. Attainment of the infimum is unnecessary: apply (8) to an approximating sequence of common estimators.

Collective and adaptive procedures with a hard budget of at most n original copies are covered by the POVM model, padding unused copies. Known ancillas and classical randomization can be included. The comparison does not grant unknown Hamiltonians, spectral instruments, coherent copies, or purifications of the input state. The square roots in (6) are labels of known candidate matrices, not a claimed physical square-root transformation of an unknown input.

## 5. An exact computable finite-prior risk surrogate

The scalar comparison supplies a basis-independent quantity

    V_n(p)=sum_a Q_opt(x_a)
          =1-sum_a Tr(B_a L_a),
    B_a=sum_i p_i x_(i,a) R_i,
    (S L_a+L_a S)/2=B_a.                           (10)

It is nonnegative. The same proof yields

    R_B^*(p,n) <= R_PGM,B <= R_PGM,H <=2 V_n(p)
                <=4 R_B^*(p,n),
    R_PGM,T <=8 V_n(p).                            (11)

For the final inequality in the first line, use V_n<=E H2<=2 E B2 for any common state-valued estimator before taking the infimum. Thus V_n is quantitatively tied to the actual Bayes Bures task, up to fixed constants. It is not a dimension or prior-entropy assumption.

Equation (10) is finite-matrix information about a known finite ensemble, in the original ideal measurement model. Computing it can be exponentially expensive in N and n. It is not supplied for the unknown input state and is not asserted to be efficiently computable uniformly over a continuum of priors.

## 6. What a full Gibbs supplier would imply, with every copy counted

Suppose, additionally, that for every finite candidate set in the original Gibbs class and every prior, one proves

    R_B^*(p,n)<=C_(beta,k) M/n.                     (12)

This is the missing hypothesis, not a conclusion of this note. It would imply R_PGM,T<=16 C_(beta,k) M/n for the same n copies. Because the bound holds for every prior, finite minimax supplies a prior-independent decoder with the corresponding worst-case zero-one loss of exceeding an assigned trace radius. No unknown prior is given to the actual P1 procedure.

For example take 0<epsilon<=1,

    n>=ceil(12288 C_(beta,k) M/epsilon^2),
    a=epsilon/8,
    eta<=min{epsilon/16,1/(12n)}.                   (13)

For a finite known eta-net in full trace norm, Markov's inequality and minimax give decoder failure at most 1/12 outside radius a on every net candidate. Replacing a true state by its net representative changes any n-copy event probability by at most n eta/2<=1/24. Each original source is therefore decoded within a+eta<=3epsilon/16 with failure at most 1/8.

Run this decoder on n copies of each of the TWO unknown sources, exactly 2n total. Under equality the two estimates are at distance at most 3epsilon/8 when both decoders succeed. Under original separation epsilon they are at distance at least 5epsilon/8. Threshold epsilon/2 has error at most 1/4. Finite precision can use the previously reviewed robust loss/threshold slack; no efficient runtime claim is made here.

The fine net is for off-net continuity and finite minimax only. Equation (12), if proved uniformly, would not charge log net cardinality. This conditional O(M) fixed-accuracy consequence explains why (12) matters, without asserting it.

## 7. What was tested, and why no interacting rate follows yet

This comparison applies to the entire interacting class, rather than only to one-body or commuting states. Its proof uses the actual quadratic Bayesian operator inequality, an exact Hilbert embedding, and the primary fidelity comparison. It removes a specific concern about ordinary PGM actual Bures risk: it cannot exceed optimal Bayes Bures estimation by an arbitrary multiplicative factor for a fixed ensemble and copy budget.

It does not reduce state estimation to binary equality testing. A binary test may use fewer copies than any state-valued estimator. Nor may a good full-trace SQUARED-risk bound be inserted on the right side of (9) as if it were Bures risk. The universally valid relation B2<=||rho-sigma||_1 only gives R_B<=sqrt(E T2), which may lose a power. The affine Pauli means already controlled in the earlier note are not the nonlinear coordinates Tr(E_a sqrt(rho)). Replacing the latter by known expectations or setting their total risk to M/n by parameter counting would assume the missing theorem.

In particular, the d^2 scalar coordinates create no factor in the comparison (7), but this does not mean their aggregate optimal risk V_n is O(M/n). No such estimate follows from the number M of Hamiltonian coefficients. The previously audited pointwise Hessian, QBM gradient, fixed-parameter local asymptotic, and information-increment statements do not supply it under unrestricted interaction incidence. This note does not repeat those imports.

The learned-output architecture also inherits the earlier Omega(M) trace-learning limitation in the exact small-accuracy regime of component 33. Since T2<=4 B2, an O(M/n) Bures learner would be consistent with that limitation and could remove the upper bound's logarithmic factor. It would not establish a sub-M full-state learner. A genuinely decision-specific improvement remains a separate possibility.

The remaining concrete gate is to prove (12), or equivalently up to constants a uniform V_n(p)=O_(beta,k)(M/n), for all original noncommuting Gibbs candidates and arbitrary priors at the relevant budgets. No new full P1 upper or lower bound is obtained here.

## 8. Sources, status and reproducibility

Established ingredients, freshly checked at the cited passages: Albarelli--Branford--Rubio's quadratic PGM comparison, and Iten--Renes--Sutter's fidelity/affinity inequalities. The combination and copy accounting are derived explicitly above. A bounded search also located Quadeer, *Haar-random and pretty good measurements for Bayesian state estimation*, arXiv:2310.20565. Its inspected introduction and Section IV discuss single-shot Bayesian estimates; it is relevant prior context, not a full-history novelty audit or a replacement for the proof here.

Reviewed earlier actual-distortion source:
https://github.com/Sodelin/Research-Commons/blob/36677b23e79bf89bf2e98a8fa9e7e1cee642e830/research/2026-10-19-p1-distance-weighted-pgm-route/actual-distortion/README.md

Accepted unrestricted original-class upper 13:
https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md

Classical-output learning limitation, whose accuracy restrictions remain in force:
https://github.com/Sodelin/Research-Commons/blob/635139c505ac8ba72261e2f468bbd51fac3fce82/research/2026-10-16-g6-gibbs-certification/trace-localization-pilot-boundary-33/P1-TRACE-LOCALIZATION-PILOT-BARRIER-20261018-0216.md

No numerical result is needed for the hand derivation. A separately saved bounded floating-point checker, if run, tests matrix orientation, the Hilbert-coordinate sum, and the common-estimator inequalities on small admitted noncommuting examples. Such controls are not a proof for all sizes or a computation of the optimum Bayes Bures estimator. Publication requires separate review and an explicit scope decision.
