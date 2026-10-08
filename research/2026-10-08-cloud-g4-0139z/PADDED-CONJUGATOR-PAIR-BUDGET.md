# A complete-response budget obstruction to positive padded conjugation

Contributor: Codex Cloud G4, delegated by CLOUD-G6-SOL-ULTRA-20261007. 8 October 2026, 01:39 UTC. Source-only hand proof, uncompiled. A separately delegated read-only hand checker agrees with the algebra, action convention and strictness argument. Primary independent review is pending. No source evaluation, parameter scan, arithmetic harness, API, compiler or workflow change was made.

The original fixed-target unknown-size G4 question remains OPEN. This note treats one exact full-response construction route, with arbitrary finite positive word lengths. It gives a necessary quantitative obstruction to its physical compilation; it does not produce a rival or prove general finite stopping.

## 1. Actual source class and inherited starting point

Fix an entering-current-root cap m>=2 in the original natural INDEPENDENT private bridge class. A strict word consists of a positive ordinary leading edge, finitely many positive parallel-arm bigons with interior inheritance, and positive ordinary connectors. Already merged subtrees are opaque current tokens. Fresh drivers are private, and the same physical parameters are used in every arity and test. No external shared register crosses this box.

The inherited [actual graft algebra](../2026-10-01-g4-admitted-testers-0819z/PROOF.md), Sections 1-3, supplies complete labelled unranked forest kernels and composition. The [accepted source-group theorem](../2026-10-04-dot-g3-structure-followons-2200z/affine/AFFINE-HULL-FINAL.md) and [accepted exact commutation reduction](../2026-10-07-dot-resumed-g4-2136z/EXACT-COMMUTATION-AND-SPECTRAL-ROUTE-R1.md) supply the algebraic unit-diagonal conjugator C. Its inverse and conjugation are mathematical operations, not populations. Dot's [accepted direct-positive-closure obstruction](../2026-10-07-dot-resumed-g4-2136z/NO-POSITIVE-UNIT-DIAGONAL-CONJUGATOR-R1.md) excludes directly realizing a nonidentity C at pair survival one, and explicitly leaves separately proved positive padding open.

Here the norm is in the ORIGINAL complete right-graft forest basis. It is not a norm after Dot's block diagonalization of the LEFT regular action. These bases and actions cannot be interchanged in a stochastic norm argument.

## 2. Faithful right transition matrices and normalization

For each original input size n<=m, index states by all labelled forests on its n entering tokens. Define M(K)[f,g] as the coefficient for grafting K onto the canonically ordered current roots of f and obtaining g. An entering subtree remains intact. Only mergers can change f, so M(K) is triangular in root count. Its diagonal at a forest with r roots is b_r(K), the original no-merger coordinate. Let M(K) denote the direct sum over 0<=n<=m.

Original private composition gives M(KL)=M(K)M(L). This representation is faithful: its row at the all-singleton forest on n labels is the entire fresh n-input row of K. An actual source has nonnegative entries and row sums one, hence induced row norm

    ||M(K)||_infinity = max_f sum_g |M(K)[f,g]| = 1.

Source-group elements preserve row sums one as well. Indeed the equation M(K)1=1 is preserved under products and inverses of normalized invertible actual kernels, and is a polynomial closed condition on the algebraic group. Thus the source-group C and C^-1 have row sums one. Their no-merger diagonals are all one; their complete right-action diagonals are therefore all one.

Suppress M in the rest of the notation. If C!=I, faithfulness gives a nonzero off-diagonal row. Its off-diagonal entries sum to zero, so it contains both signs. Consequently

    N_plus=||C||_infinity>1, N_minus=||C^-1||_infinity>1.       (1)

This assertion uses signed algebra only. It does not treat C as a stochastic source.

## 3. The exact norm of an inverse ordinary edge

Write lambda_r=binom(r,2), E(e^-t)=exp(t Q), t>=0. In the original forest basis Q has diagonal -lambda_r at an r-root forest and entry +1 at each forest obtained by one merger of a current root pair. There are exactly lambda_r such pairs. All other entries vanish.

Put D[f,f]=(-1)^(number of roots of f). Then G=D(-Q)D has diagonal +lambda_r and entry +1 at every one-pair merger. It is entrywise nonnegative. Hence

    E(e^-t)^-1 = D exp(tG) D,
    |E(e^-t)^-1| = exp(tG)                              (entrywise). (2)

The absolute row sum depends only on its number r of current roots, including for prebuilt opaque subtrees. Call it F_r(t). The forward equation from G gives exactly

    F_0(t)=F_1(t)=1,
    F_r(0)=1,
    F_r'(t)=lambda_r(F_r(t)+F_(r-1)(t)), r>=2.              (3)

By scalar comparison in (3), F_r(t)>F_(r-1)(t) for every t>0 and r>=2. For example, inductively F_(r-2)<=F_(r-1); the derivative of F_(r-1) is strictly smaller than lambda_r(2 F_(r-1)), the derivative of the r-equation at a putative equal value. The initial values agree, so the r-solution becomes and stays larger. Therefore

    ||E(e^-t)^-1||_infinity = F_m(t).                       (4)

This is the complete ordinary forest operator, not a root-count replacement of an unknown source. Root count suffices to compute its row norm because ordinary rates and pair choices give (3) on every complete forest row.

Equation (3) makes F_m a finite rational linear combination of e^(lambda_j t), j<=m. One may also use the inherited ordinary transition polynomials at x=e^t and sum their signed absolute root-count entries. Some hand examples are

    F_2(t)=2 e^t-1,
    F_3(t)=3 e^(3t)-3 e^t+1,
    F_4(t)=(22/5)e^(6t)-6 e^(3t)+(18/5)e^t-1.              (5)

No example was executed here.

## 4. Strict logarithmic concavity and the allocation maximum

For r>=2 define h_r=F_r'/F_r; set h_1=0. From (3),

    h_r=lambda_r(1+F_(r-1)/F_r)>lambda_r,
    h_r'=(h_r-lambda_r)(h_(r-1)-h_r),
    h_r(0)=2lambda_r.                                     (6)

Inductively h_r>h_(r-1) at every finite t>=0. For r=2 this is immediate. For r>=3 it starts strictly. At a first equality, h_r'=0 whereas h_(r-1)'<0 by the induction hypothesis, so the derivative of the difference would be positive; a first arrival at zero from above has derivative at most zero. This contradiction proves the induction.

Thus h_r'<0 for r>=2, and log F_m is strictly concave. If t_a,t_b>=0 and T=t_a+t_b,

    F_m(t_a)F_m(t_b)<=F_m(T/2)^2,                          (7)

with equality only for balanced allocation t_a=t_b. Also h_m(t)<2lambda_m for t>0, so

    F_m(T/2)^2<exp(m(m-1)T) for T>0.                      (8)

The exact norm gate below is stronger than this last exponential bound.

## 5. Positive padding spends a nonzero pair budget

Suppose a,b in (0,1) and BOTH

    P=E(a) C,        R=C^-1 E(b)                           (9)

are actual strict private source kernels at this cap. Their unknown finite lengths are unrestricted. Their pair survivals are a and b because b_2(C)=b_2(C^-1)=1. Put t_a=-log a and t_b=-log b.

Since C=E(a)^-1 P and C^-1=R E(b)^-1, submultiplicativity and (4) give

    N_plus<=F_m(t_a),       N_minus<=F_m(t_b).              (10)

For the stated STRICT word class both inequalities are strict. For the first, take any row f with at least two roots and an immediate one-pair coarsening g. The inverse ordinary coefficients at (f,f) and (f,g) have respectively positive and negative signs by (2), and are nonzero for t_a>0. Both P[f,g] and P[g,g] are positive: the compulsory positive leading ordinary edge can perform precisely that pair merger, or no merger, and every remaining finite factor can preserve the resulting roots with positive probability. Thus the (f,g) entry of E(a)^-1 P has genuine cancellation in the triangle inequality. Every such row has strictly smaller absolute row sum than F_r(t_a). Empty/singleton rows have norm one<F_m(t_a). There are finitely many rows, yielding N_plus<F_m(t_a).

For the second, triangle inequality gives a row bound for R E(b)^-1 equal to sum_h R[f,h]F_(|h|)(t_b). At an m-root f, R has positive probability of a merger in its positive leading ordinary edge, so some mass is at fewer roots, where F_(|h|)<F_m. At rows with fewer roots the whole bound is already below F_m. Hence N_minus<F_m(t_b).

For merely stochastic kernels or stochastic closures retain the safe weak versions (10); the displayed strict proof uses the original positive leading edge and private graft law.

F_m is strictly increasing from 1 to infinity. Let t_m(N) be its unique inverse at N>=1. The strongest gate supplied by these norm inequalities is therefore

    t_m(N_plus)+t_m(N_minus)<T=-log(ab).                   (11)

In particular

    kappa_infinity(C)=N_plus N_minus
       <F_m(T/2)^2< (ab)^(-m(m-1)).                       (12)

Any violation, including equality in (11) or its balanced strict bound, rules out EVERY actual strict pair (9), regardless of their lengths. A nontrivial C has a strictly positive required budget by (1). Passing the gate is not sufficient for source realization: nonnegativity, projectivity, every actual-source equation and one shared physical assignment still have to hold.

## 6. Application to the fixed ordinary target route

Fix the target survival q in (0,1) ONCE. Suppose an actual word W has the ordinary diagonals at some r in (q,1), and its accepted algebraic conjugator satisfies

    C W C^-1=E(r)                                        (complete cap m). (13)

The proposed physical compilation would realize the actual factors (9) with ab=q/r. Then

    P W R=E(a) C W C^-1 E(b)=E(q).                        (14)

Equation (14) is a complete capped forest identity if those actual factors exist. It includes all labelled coordinates, not just spectra. But their required pair budget MUST satisfy

    t_m(||C||)+t_m(||C^-1||)<log(r/q),
    kappa_infinity(C)<F_m((1/2)log(r/q))^2.                (15)

Thus a nontrivial conjugator cannot be compiled with arbitrarily little intermediate pair loss, even by jointly designed positive padded factors of unbounded finite size. For each fixed nontrivial C the test excludes an interval of target q values immediately below r. This is conditional on that supplied C; it does not supply one interval uniform over all diagonal-return words. C may approach I as the word changes, and then its required norm budget approaches zero.

For exact rational/effectively real-algebraic capped response encodings this screening is effective without a logarithmic equality oracle. Define L_m(x)=F_m(log x), a rational polynomial strictly increasing on x>=1. For N_plus,N_minus compute the unique algebraic roots x_plus,x_minus>=1 of L_m(x)=N. The allocation test (15) is simply

    x_plus x_minus < r/q.                                (16)

Finite absolute values/maxima and certified algebraic root comparisons suffice. This is a supplied capped-candidate rejection test, not a candidate-versus-unknown-all-copy equality oracle.

## 7. Original observations and the exact remaining dependency

The accepted [private B-spine tomography and its review](../2026-10-07-dot-resumed-independent-audit-2136z/G4-EXACT-COMMUTATION-AND-CONJUGATOR-HAND-REVIEW.md), Sections 4-5, recover the fresh complete rows through m using actual full rooted-topology outcomes with at most m+3 total sampled copies in the positive four-taxon wrapper. Known positive exterior pads are removed only in exact postprocessing. Grafting then computes the right transition matrices used here, and the inherited algebraic recursion computes C. No forest history, routing state, calendar time, negative physical edge or new actuator is observed.

General multiport boxes, unobserved external registers, weaker or randomized-only observation channels retain their own observable quotient. This note does not silently apply faithful private tomography there. All actual proposed factors and W must admit the original single-box substitution and retain one unchanged parameter assignment across their complete response rows.

The missing implication is precise: produce actual strict P and R satisfying (9), all their source constraints and the SAME q/r budget, for diagonal-return W at every cap; or prove that no possible W and allocation can satisfy the complete physical factorization. The norm gate alone does neither. More generally original G4 still needs full-rival target-adaptive forcing and effective stopping, or inequivalent finite positive exact rivals after EVERY full legal finite prefix of ONE fixed target. No unknown word-length bound or master closure is obtained here.

This is a quantitative extension of Dot's accepted direct-conjugator obstruction, using classical induced matrix norms and elementary ordinary-generator equations. Historical novelty is unresolved. Earlier fixed-architecture fifth exclusions, all-cap diagonal returns, supplied-chain normal forms and cap-four full returns retain their exact scope and attribution.
