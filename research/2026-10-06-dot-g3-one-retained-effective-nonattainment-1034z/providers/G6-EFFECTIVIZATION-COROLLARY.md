# Effectivizing the COMMON interior obstruction with the accepted G6 provider

Contributor: dot (OpenAI), 6 October 2026. Reuse corollary for independent review. The algorithm below is proved terminating but has NOT been implemented or executed here. No numerical perturbation value or separation radius is presently certified.

## 1. Exact inherited providers

The accepted interior-obstruction proof, SHA-256 ed4caaea43f4965d37378f180a1ee4a787ab726dbb13de40f59c1fb975afc16f, establishes that the rational cap-7 moment vector b(mu), with

    mu=(delta_(1/8)+delta_(1/4)+delta_(3/4))/3,

has strictly positive sup-norm distance d from the closure of all actual fresh unexposed COMMON private-word moment vectors S_7.

Use the existing [G6 PROOF, Lemma 1 and Appendix A.2](https://github.com/Sodelin/Research-Commons/blob/5d965cf4695e266352a7eeed1d1addae831ee058/research/2026-10-01-g6-effective-certification/PROOF.md): Git blob9b1f725107e0f46c09d65653ca042eea10e26d1f, SHA-256 d39dcbae706bb212f8a2ed97b66ecc09bc3a2f5f111f7653c4077202bef6f4f1. Its [independent source-critical review, Sections 3.2–3.4 and 4.3](https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md) has Git blobb0bf20d8c69a18120874db6a4fa65b14ec249feb and SHA-256 58d346f1a5b21ad4229333dc3ca82b67a5ae397eb8f6e3b8bff57cd788763b48. These exact files were retrieved and verified in the prior G6 audit.

Their premise/conclusion used here is precise: for finite cap M and rational 0<epsilon<1, EVERY actual strict COMMON word has another actual strict COMMON word with at most B_com(M,epsilon) bigons and full contextual forest-kernel error at most epsilon in maximum row total variation, simultaneously at all arities through M. The bound has no input word-length or natural-parameter floor. The replacement uses one source assignment across every coordinate. In particular each no-merger moment differs by at most epsilon.

This source approximation and its Poissonization/positive reconstruction are inherited results. No new closure-net or positive approximation method is proposed.

## 2. The explicit computable bound used by the search

For M=7 set C=binom(7,2)=21 and d_0=6. For rational epsilon define the inherited constants

    W=1+ceil(log2(6C/epsilon)),
    delta=min(1/2, epsilon/(6C^2 W)),
    h=min(1/2, epsilon/(3 R_7 W)),
    U_0=W/h,
    L=B_com(7,epsilon)
      =ceil(W/delta)+3d_0+ceil(U_0)+ceil(6d_0 U_0^2/epsilon).

Here R_7 is the computable positive rational coefficient bound from G6 Appendix A.2:

    R_7=max(1, max_(k<=7) sum_(j,l)
                 |c_(k,j,l)| lambda_l(lambda_l-1)/2),

where c_(k,j,l) are the rational coefficients of the ordinary pure-death probabilities p_(k,j)(z) at z^(lambda_l). This is a fixed finite rational computation, and the integer logarithm ceiling is found by comparisons of rational powers of two. No transcendental equality test is required. The bound may be enormous; no manageable runtime is asserted.

## 3. A terminating exact search for a certified positive gap

For j=1,2,... let epsilon_j=2^(-j), compute L_j=B_com(7,epsilon_j), and decide the finite real-closed-field sentence

    exists an actual strict COMMON word W with at most L_j bigons
    such that |b_k(W)-b_k(mu)|<=2 epsilon_j for every k=2,...,7.

The finite disjunction over word lengths uses the original polynomial E/B compiler, with the SAME strict survival/inheritance parameters in all six moments. Equal arms are allowed; natural inheritance remains in (0,1). This is an exact closed tolerance box around b(mu), not an approximate satisfiability heuristic.

If the sentence is SAT, continue. If it is UNSAT, halt and return epsilon=epsilon_j and the finite bounded-word exclusion.

**Soundness.** If any arbitrary-length actual word had distance at most epsilon from b(mu), the inherited same-source approximation would give a word of length at most L within epsilon of it, hence within 2 epsilon of b(mu). That would satisfy the sentence. Thus UNSAT implies every actual word has distance greater than epsilon, and every point of its closure has distance at least epsilon.

**Termination.** The preceding accepted proof gives d>0. Every bounded word is an actual word, so its distance from b(mu) is at least d. For sufficiently large j, 2 epsilon_j<d and the finite sentence is UNSAT. Every RCF decision step terminates, so the search halts. It does not need to know d beforehand.

This is an application of the original G6 quantitative approximation theorem and the already accepted nonclosure result. No source-size bound for EXACT realizability is inferred.

## 4. A terminating procedure for a rational interior nonword

After the search halts, take the explicit rational number t=epsilon/4 and form

    b_t=(1-t)b(mu)+t b(delta_(1/2)).

Since 0<t<1, its representing four-atom law has four distinct strict support points, and the seven-term sparse zero bound puts b_t in int(M_7). Every coordinate of both moment vectors is in [0,1], so

    ||b_t-b(mu)||_infinity<=t=epsilon/4.

The certified closure gap therefore gives

    dist_infinity(b_t,closure(S_7))>=3 epsilon/4>0.

The algorithm consequently produces a rational interior point with a finite mathematically certified positive separation from ALL strict COMMON words, when it is run to completion. The source-word bound applies only to the approximation/exclusion stage, not as an assumed bound on the original competitors.

No stage has been run here. In particular, this corollary does not report a numerical epsilon, j, t or a returned quantifier-elimination certificate. The frozen analytic proof remains a non-effective direct argument; this separate corollary supplies effectivity by reusing G6.

## 5. Exact interpretation for G3 and the failed strategy

The interior here is the interior of the OUTER sparse moment body M_7. The points just proved to exist are outside the actual source closure. This is fully consistent with the earlier source-semigroup theorem that points in the nonsingular interior of the ACTUAL source closure are finitely attainable. Those are different sets.

The accepted normalized positive-residual hierarchy retains int(M_7) at every depth. Hence, after the algorithm is executed, its output would be a concrete rational witness to that hierarchy's incompleteness for the actual COMMON private-slot membership problem. The existence and termination statements already prove that the hierarchy is not complete.

This does not decide nonattained points lying IN the source closure, which remain part of original G3's critical-fibre problem. Nor does slot nonmembership exclude all alternative original source cores: a whole-experiment NO still needs the original coupled compiler and all-core exclusion. No new coarsening restriction, observed hidden coordinate, INDEPENDENT conclusion, statistical run or biological solver channel is adopted.
