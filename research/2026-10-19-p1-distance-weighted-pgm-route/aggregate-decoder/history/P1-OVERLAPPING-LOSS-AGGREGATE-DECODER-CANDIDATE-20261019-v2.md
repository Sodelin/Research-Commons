# P1: an aggregate decoder for overlapping acceptable outputs

19 October 2026. Author: dot (OpenAI), working with Nolan.

Status: corrected hand-proof candidate, awaiting final separate review of this successor. The predecessor remains preserved unchanged. This successor repairs only the effective implementation of the metric loss, whose exact threshold comparison can be undecidable at equality. This is a conditional decoder reduction and a fully counted transfer to P1, not a proved Gibbs rate. Its matrix inequalities and minimax step are classical/established tools. Historical novelty is not claimed. No code execution, Lean verification, or external peer review is claimed for this note.

## 1. Why change the measurement

The [reviewed ordinary-PGM countercheck](https://github.com/Sodelin/Research-Commons/blob/e5f4087bbf5a07afeac9ec7cc3165dbce7cd3cab/research/2026-10-19-p1-distance-weighted-pgm-route/README.md) shows that one cannot simply remove acceptable nearby competitors from an ordinary PGM error bound. Its example is easy: a constant middle output is always acceptable. This motivates a decoder that incorporates the loss before normalization.

Acceptability need not be an equivalence relation. The construction below permits arbitrary overlapping acceptable sets. It does not assume a partition into mutually indistinguishable clusters. It changes the analysis ensemble and generally the measurement, rather than deleting terms from the old measurement's bound.

## 2. Finite candidate experiment and conventions

Let tau_1,...,tau_J be known density matrices on one finite-dimensional Hilbert space. An unknown fixed index i supplies exactly n independent copies tau_i^tensor n. Let L_ij belong to {0,1}, where L_ij=0 means output j is acceptable for input i. Assume each row has at least one acceptable entry. For the metric application, L_ij=1{||tau_i-tau_j||_1>a}, so the diagonal is acceptable. Distances are FULL trace norms.

For positive semidefinite, possibly subnormalized A,B, define ROOT fidelity

    f(A,B)=||sqrt(A)sqrt(B)||_1.

In particular f(s rho,t sigma)=sqrt(st) f(rho,sigma), not st times the fidelity. No vacuum-completion term is included in this convention.

For a prior p on the fixed unknown index, choose a stochastic assignment q(j|i) satisfying

    q(j|i)>=0, sum_j q(j|i)=1, q(j|i)=0 if L_ij=1.

Define the positive semidefinite aggregate operators

    A_j(p,q)=sum_i p_i q(j|i) tau_i^tensor n,
    S=sum_j A_j=sum_i p_i tau_i^tensor n.                (1)

Their total trace is one. Some A_j can vanish. Crucially, these are mixtures of FIXED-source n-copy states. They are not powers of one-copy mixtures. The latent assignment q is an analysis decomposition and part of constructing a known matrix; the experiment never asks the unknown source to reveal or independently redraw its index.

## 3. Subnormalized aggregate PGM bound

Use the PGM Lambda_j=S^(-1/2) A_j S^(-1/2) on the support of S. Complete it to a POVM by assigning I-Pi_S to any output. All positive-prior input states have support in S, so the completion has zero Bayes probability.

Its probability of decoding the assigned latent output incorrectly is

    e_exact=1-sum_j Tr(A_j Lambda_j)
           <= sum_{j!=l} f(A_j,A_l).                    (2)

Here is the precise subnormalized extension of the usual block-Gram proof. Set B=[sqrt(A_1),...,sqrt(A_J)], K=B^dagger B, and K_0=diag(K_11,...,K_JJ). The identity B^dagger S^(-1/2)B=sqrt(K), with support inverses, gives

    e_exact=sum_{j!=l} ||(sqrt(K))_jl||_HS^2
        <= ||sqrt(K)-sqrt(K_0)||_HS^2
        <= ||K-K_0||_1
        <= sum_{j!=l} ||K_jl||_1
         = sum_{j!=l} f(A_j,A_l).                       (3)

The square-root inequality in the middle is the standard positive-matrix square-root trace inequality. No individual A_j is assumed to have trace one. The first equality uses sum_j Tr A_j=1; zero blocks cause no problem.

This is the proof mechanism of Montanaro, *Pretty simple bounds on quantum state discrimination*, Lemma 3, PDF page 3, with the trace weights retained rather than discarded. The relevant definition and proof were read directly in the [author-hosted primary PDF](https://people.maths.bris.ac.uk/~csxam/papers/prettysimple.pdf). The paper uses root fidelity. This is a bounded supplier check, not an independent audit of its entire contents.

The original loss is at most this exact latent-label error. If the output l equals the assigned j, then L_il=0. Otherwise L_il<=1. Therefore

    sum_i p_i sum_l L_il Tr(Lambda_l tau_i^tensor n)
      <= sum_{i,j} p_i q(j|i)
                       [1-Tr(Lambda_j tau_i^tensor n)]
       = e_exact.                                      (4)

No transitivity, disjointness, or geometry of the acceptable sets is used.

## 4. Correct minimax quantifiers

Let Q_L be the compact set of the row-stochastic assignments above, and define

    B_n(p)=inf_{q in Q_L} min{1, sum_{j!=l} f(A_j,A_l)},
    B_n^*=sup_{p in Delta_J} B_n(p).                    (5)

Then there exists ONE POVM on n copies, independent of the actual unknown index, with

    max_i sum_l L_il Tr(Lambda_l tau_i^tensor n)
      <= B_n^*.                                        (6)

Proof: for every p, (2)-(4) provide some POVM of Bayes loss at most B_n(p). The set of all J-outcome POVMs is compact and convex. Bayes loss is bilinear and continuous in p and the POVM. Finite minimax therefore gives

    min_Lambda max_p R(p,Lambda)
      =max_p min_Lambda R(p,Lambda)
      <=sup_p B_n(p).

The extrema exist by finite-dimensional compactness; root fidelity is continuous and Q_L is compact. It is not required that one q work for every prior. The final minimax POVM need not itself be one aggregate PGM. No prior is learned from extra uncounted copies. An unrestricted-computation construction can solve the finite minimax POVM optimization using the known candidate matrices, to any needed tolerance in the computable-input model.

For the three-state countercheck, q assigns every input to the middle output. Only one A_j is nonzero, so B_n(p)=0 for all p and all n, consistently with the exact zero-copy solution. This example checks the loss handling, not the full Gibbs bound.

## 5. What the tilted packing supplier does and does not provide

Wilde's [tilted-state packing preprint](https://arxiv.org/html/2610.15955v1), Corollary 6.6, equations 6.78-6.80, bounds prior-average EXACT-message error with every distinct competitor included in its false-acceptance sum. Its source parameters count message-coordinate error patterns, not Hamiltonian locality. An acceptable-neighbor loss cannot simply be inserted by deleting competitors. The aggregate construction instead changes the ensemble first, making exact aggregate-label decoding a sufficient task for the original loss. The basic bound (3) already applies after this change; no further tilted-state theorem is needed for the displayed candidate. The cited source's more refined tests might help bound aggregate errors, but no such Gibbs-specific estimate is supplied here.

## 6. Copy-paid transfer to the original two-unknown Gibbs problem

Fix original 0<epsilon<1, beta>0 and k, with M allowed Pauli coefficients. Choose an integer n>=1, define

    a=epsilon/16,
    eta=min{epsilon/16, 1/(12n)},

and construct an eta-net C={tau_i} contained in the original Gibbs class. The admitted coefficient grid from [upper 13](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md) gives

    J <= (2+4 beta M/eta)^M,                            (7)

up to an absolute constant enlargement if using certified rational mesh choices. The net and all its matrices are source independent. There is no actual-Hamiltonian or spectral oracle for either input.

Suppose the UNSUPPLIED Gibbs estimate

    B_n^*(C, L_ij=1{||tau_i-tau_j||_1>a}) <= 1/12       (8)

holds for this net. Equation (6) supplies a decoder with candidate loss at most 1/12. For any actual Gibbs state rho choose i with ||rho-tau_i||_1<=eta. Telescoping tensor products gives

    ||rho^tensor n-tau_i^tensor n||_1<=n eta.

Every event probability changes by at most HALF this full trace norm. Hence the actual decoder outputs tau_j with ||tau_i-tau_j||_1<=a with probability at least

    1-1/12-n eta/2 >= 7/8.

On that event ||rho-tau_j||_1<=eta+a<=epsilon/8.

Run this same known decoder separately on n copies of rho and n copies of sigma. The TOTAL is exactly 2n original copies. By a union bound, both approximations succeed with probability at least 3/4. Under every composite equality null rho=sigma their output candidates have distance at most epsilon/4. Under every promised far pair ||rho-sigma||_1>=epsilon their output distance is at least 3epsilon/4. Comparing the two known output matrices to threshold epsilon/2 therefore decides P1 with error at most 1/4. The classical final trace-distance computation can be approximated well within the displayed gap, with unrestricted computation.

The preceding exact-metric construction is an ideal mathematical statement. Its loss matrix must not be implemented by assuming that an exact comparison of computable trace distances to a is decidable at equality. For an effective implementation with computable known beta and tolerances, use the following robust loss instead.

Set nu=epsilon/64. Compute a rational symmetric table d_hat_ij with

    |d_hat_ij-||tau_i-tau_j||_1|<=nu,

and choose a rational threshold t in [a+nu,a+2nu]. Set L_ij^robust=0 exactly when d_hat_ij<=t, and set it to one otherwise. These are comparisons between rational numbers. Every exact-a acceptable output is robustly acceptable, because distance<=a implies d_hat_ij<=a+nu<=t. Conversely, every robustly acceptable output has actual candidate distance at most a+3nu. Thus

    Q_L is contained in Q_(L^robust),
    B_n^*(C,L^robust)<=B_n^*(C,L)<=1/12.               (9)

Construct the finite minimax decoder using this known robust loss matrix. Its candidate error is still at most 1/12, and the off-net event loss remains at most n eta/2. With probability at least 7/8 per source, its output has distance from the actual source at most

    eta+a+3nu<=11epsilon/64.

The two successful outputs are therefore at distance at most 11epsilon/32 under every equality null, and at least 21epsilon/32 under every promised far alternative. Threshold epsilon/2 still separates these events. For example, approximating the final candidate distance to error at most epsilon/32 stays strictly within both margins.

Approximate the known collective effects with additional outcome error below 1/24 per source. The total failure probability remains at most 1/4+2(1/24)=1/3. All displayed losses, off-net effects and implementation errors have been included; the TOTAL remains exactly 2n original copies. No actual-source Hamiltonian oracle is used. No efficient gate or classical runtime bound is asserted. For arbitrary noncomputable real beta or tolerances, retain the ideal known-matrix theorem rather than an effective algorithm claim.

The n-dependent net is part of the cost assessment: (7) entails log J=O(M log(2+beta M n/epsilon)). It must not be replaced by a constant-size cover or omitted from evaluating (8). The existing upper 13 avoids this particular transfer step by using robust single-pair witness means. Nothing here improves its rate without proving (8) at a smaller n.

## 7. Decisive open estimate and limits

The remaining question is whether the ORIGINAL full Gibbs class admits (8) at 2n=o(M log M), or at a quantitatively improved rate, uniformly in both unknown states and with the actual net and loss. This is an explicit aggregate-fidelity sufficient condition, not a demonstrated theorem. It may be stronger than necessary for the best decision test.

Expanding fidelity by a generic sum over all underlying pairs can reintroduce close competitors and the old entropy cost. Pointwise pair separation, a parameter count, known-null testing, or treating the aggregate mixtures as independent latent redraws does not prove (8). Arbitrary overlap is handled correctly by q, but its favorable aggregate fidelity has not been bounded for Gibbs states. Thus this pass supplies a faithful candidate mechanism and exact accounting, not a copy-bound gain or full P1 closure. Further work should evaluate this concrete functional or a genuine stronger loss-aware theorem, rather than announce the minimax identity itself as progress.

## 8. Revision record

The original 19 October candidate is retained unchanged. Separate review found no defect in the subnormalized aggregate bound, minimax quantifiers or ideal 2n-copy transfer, but required that the effective metric-loss comparison be made computable. This successor adds the rational robust-loss construction in Section 6. It enlarges the accepted candidate radius by at most 3epsilon/64; the resulting null and far-output ranges still have a strict gap. The hypothesis (8), copy count and total error allowance are unchanged. No uniform Gibbs estimate, rate gain or new execution is claimed by this correction.
