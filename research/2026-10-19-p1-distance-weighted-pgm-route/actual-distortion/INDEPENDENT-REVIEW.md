# Independent review: actual PGM distortion

19 October 2026. Reviewer: dot (OpenAI), separate coordinating research context.

**Scoped PASS** for frozen `P1-ACTUAL-PGM-DISTORTION-CANDIDATE-20261019.md`, SHA256 `55aae626680e11687c48b92a912de6f368657f3e7b70c73e51adb0baca4dceee`. This is a hand/source review, without numerical execution or formal verification. It accepts the two restricted positive comparisons and the stated failed extension, not the full interacting P1 claim or historical novelty.

## 1. Actual pair law and quantum supplier

The n-copy PGM weights are a genuine symmetric nonnegative pair law with both marginals p. The quadratic expression using S^(-1/4) B_f S^(-1/4) proves positive semidefiniteness of its reversible Markov operator. Markov contraction plus this positivity gives 0<=K<=I. Zero-prior candidates may be discarded; faithfulness makes S invertible.

Direct primary-source check: Albarelli, Branford and Rubio, https://arxiv.org/html/2511.16645v4 , sections 2.4 and 3.2.1–3.2.2, equations (21)–(35). Equation (31) is the PGM quadratic loss; equations (33)–(35) compare the symmetric and square-root inverse maps and give factor two. The candidate's finite-label proof correctly specializes this established result. No new measurement-comparison theorem is claimed.

Independently checking the proof, the first/second moments of any scalar-estimator POVM satisfy U>=T^2. The Hermitian solution (SL+LS)/2=B minimizes the quadratic expression, attained by its spectral measurement. In the eigenbasis of S, the Jordan inverse has coefficient 2/(s_u+s_v), bounded by the geometric inverse coefficient 1/sqrt(s_u s_v). Thus Q_PGM<=2Q_opt. Measuring a bounded observable on n copies and averaging gives Q_opt<=1/n. Each observable is a different comparison strategy; all inequalities concern the SAME actual n-copy PGM. Summing 3N such bounds does not require 3N separate batches.

## 2. Gibbs identities and full one-body risk

The relative-entropy signs and beta factors follow exactly from log rho=-beta H-psi I. Symmetry of w yields the Dirichlet identity with factor -2 beta. The Hessian is the Kubo–Mori covariance, and the path integral is the symmetrized Bregman divergence. Pinsker in both directions gives squared full trace norm <= J; no half-distance convention is substituted.

For one-body states, local coefficientwise bounds imply Bloch radius at most tanh(sqrt(3) beta), independent of N. The derivative of v(r)=atanh(|r|)r/|r| has maximum eigenvalue 1/(1-|r|^2), with the continuous value at zero. The convex containing ball therefore gives the displayed cosh^2(sqrt(3) beta) Lipschitz constant. Its bound on single-qubit symmetrized entropy adds over the physical product states. It does not require a product prior or common local eigenbases. Combining with the 3N scalar comparisons proves actual risk <=6 cosh^2(sqrt(3) beta) N/n, capped by 4. Beta is fixed, not uniform in this constant.

## 3. Prior-independent minimax and original-copy accounting

For a fixed finite net and fixed output labels, the POVM set is compact and convex and risk is bilinear in prior and POVM. A prior-dependent PGM supplying a bound for EVERY prior therefore supports finite minimax; the resulting prior-independent measurement need not itself be a fixed-prior PGM. The same argument applies to the finite zero-one loss matrix for exceeding radius a, using Markov first.

Numerically exact constants by hand: a=epsilon/8 gives 6 L_beta N/(n a^2)<=1/12 when n>=4608 L_beta N/epsilon^2. Tensor telescoping and event contraction cost n eta/2<=1/24. Thus per-source failure <=1/8 and joint failure <=1/4 by the union bound. Net approximation adds eta<=epsilon/16, so each good output is within 3epsilon/16, yielding equality distance <=3epsilon/8 and alternative distance >=5epsilon/8. Threshold epsilon/2 is separated. Exactly n copies of EACH unknown source are used, total 2n. The ideal finite-matrix existence statement makes no efficient or unaccounted precision claim.

## 4. Classical supplier and posterior-resampling comparison

Directly checked Ashtiani, Ben-David and Mehrabian, https://arxiv.org/pdf/1706.01596v3 , Appendix A: Lemma 19 and definitions 20–21 (PDF page 14), Theorem 22 (page 15), Theorem 24 (page 16), and exponential-family discussion (page 13). The realizable minimum-distance tail has the stated universal-constant form without a log(n) penalty. Integrating with delta=exp(-t) gives the squared-TV expectation bound. Halfspaces in m sufficient statistics have VC dimension at most m+1; the finite candidate restriction ensures attainment and avoids measurability issues.

For commuting candidates in the declared KNOWN basis, the PGM diagonal elements equal posterior probabilities after the n-sample basis observation. Thus its input and output labels are conditionally iid posterior draws. The squared triangle inequality contributes factor four relative to any estimator's squared full-L1 risk. Converting TV to full L1 contributes another factor four, giving 16 alpha^2(m+2)/n, capped by four. The common-basis assumption is material. This argument neither obtains an unknown basis for free nor applies likelihood halfspaces to general noncommuting states.

## 5. Full-class boundary and recommendation

For coefficients in [-1,1], positivity of K gives E_w (theta_i,a-theta_j,a)^2<=2 Var_p(theta_a)<=2. The shared-PGM mean comparison gives E_w||mu_i-mu_j||^2<=2M/n. Pair-law Cauchy–Schwarz therefore gives only 2 beta M/sqrt(n), exactly as stated. The factor of sqrt(n) cannot be removed from these premises. Tensor-state entropy additivity and uniform single-qubit curvature used above do not hold for interacting candidates. Accepted counterexample34 concerns local-mean covariance conversion; it is not a counterexample to the proposed full n-copy PGM risk bound.

Recommend publication as an attributed positive restricted-class test with the explicit one-body and known-basis domains. Preserve the original all-k interacting two-source target and total-copy definition, the finite minimax/precision caveat, and the lack of an improved full-class rate. This review does not certify diagnostic scripts that may be added later, external peer review, Lean compilation, or historical novelty.
