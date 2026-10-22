# G3 transcendence-method admission: UNREVIEWED hand candidates

Status: preserved on 22 October 2026 for independent mathematical review. Publication is not acceptance. No new mathematical runtime, solver, numerical experiment or formal verification was executed. The original General G3 terminating recognizer remains open.

# The original five-log branch has no direct multiplicative-grid certificate

22 October 2026. dot (OpenAI-assisted research), prepared for Nolan.

**Candidate hand argument for independent review.** No computation, compiler, QE, or arithmetic equality oracle was run. This excludes a precisely defined transcendence-theorem import; it does not solve General G3, rule out the surviving rank-five branch, or assert historical novelty.

## Why this is the master-facing arithmetic target

The accepted two-sided logarithmic-cone reduction takes five positive effectively algebraic b_n, n in {3,6,10,15,21}, with the promise that ell=(log b_n) is a nonzero finite cone combination of D_n(r)=n-(1+r+...+r^(n-1)) on a supplied compact J_j subset (0,1). It effectively constructs an original eight-row COMMON input. A pure ray is equivalent to NO against every admitted finite strict COMMON source, including all rival cores; nonpurity is equivalent to actual finite-source YES. This is an inherited source equivalence, not a consequence proved here.

The subsequent three-log refinement has a scoped independent PASS, despite its preserved draft header. It reduces purity on that full five-coordinate promise to one fixed degree-eight homogeneous polynomial equality in the first three logarithms. The zero test remains open. The present attempt asks whether unconditional six-exponentials or logarithm-matrix-rank theorems can exclude the unresolved transcendental-node branch.

Sources:
- https://github.com/Sodelin/Research-Commons/blob/d47787d8f4f9a91a4d66dbc5769a4358d0383c0d/research/2026-10-09-dot-log-cone-recognition-reduction-1508z/LOG-CONE-PURITY-TO-ORIGINAL-RECOGNITION.md
- https://github.com/Sodelin/Research-Commons/blob/8621b94a30e12794fafbf34c721a7d583a984fd0/research/2026-10-10-dot-g3-three-log-purity-1210z/README.md
- https://github.com/Sodelin/Research-Commons/blob/8621b94a30e12794fafbf34c721a7d583a984fd0/research/2026-10-10-dot-g3-three-log-purity-1210z/INDEPENDENT-THREE-LOG-REVIEW.md

## 1. A polynomial-space calculation

Write D_n(X)=(1-X)T_n(X), where

    T_n(X)=sum_{k=0}^{n-2}(n-1-k)X^k.

Let W be the rational span of T_3,T_6,T_10,T_15,T_21 in Q[X]. Their respective degrees are

    E={1,4,8,13,19}.

Every nonzero element of W has degree in E: a nonzero rational combination has a unique highest-degree contributing basis polynomial.

The ten positive pairwise degree differences are

    3,7,12,18,4,9,15,5,11,6,

all distinct. Equivalently, the fifteen unordered pair sums, including repeated indices, are all distinct:

    2,5,9,14,20,8,12,17,23,16,21,27,26,32,38.

It follows that the fifteen polynomials T_i T_j, i<=j, are linearly independent over Q, simply by their distinct leading degrees. Consequently no nonzero homogeneous quadratic polynomial over Q vanishes on the five-coordinate polynomial parametrization T(X). At a transcendental real q, evaluation Q[X] -> R is injective, so this remains true for T(q).

For a pure profile ell_n=w D_n(q), w>0, multiplication by the common nonzero scalar w(1-q) does not alter homogeneous quadratic relations. Thus, **conditional on q being transcendental**, the five logarithms have no nonzero homogeneous quadratic rational relation. This statement does not assert existence of an algebraic-input pure profile with transcendental q.

## 2. Stronger quotient form of the same obstruction

For any nonconstant f in Q(X), define

    U_f={u in W : f*u is in W}.

Then dim_Q U_f <=1.

Proof. If deg(f)!=0, set g=f. If deg(f)=0, subtract its rational leading coefficient c and set g=f-c; because f is nonconstant, g!=0 and deg(g)<0. In either case deg(g)=delta is a nonzero integer, and g*u lies in W for every u in U_f.

If U_f had dimension at least two, Gaussian elimination by leading coefficient gives two elements u,v with different degrees d,e in E. Then deg(g*u)=d+delta and deg(g*v)=e+delta also lie in E. These give two distinct ordered pairs of elements of E with the same nonzero difference delta, contradicting the displayed difference list. This uses the usual degree of a rational function (numerator degree minus denominator degree); degree is additive on nonzero products even when cancellation occurs. QED.

Now fix transcendental q and nonzero real s, and put L=s W(q). There do not exist real x_1,x_2 linearly independent over Q and real y_1,y_2 linearly independent over Q with all four products x_i*y_j in L.

Indeed write x_1*y_j=s*u_j(q) and x_2*y_j=s*v_j(q) with u_j,v_j in W. Neither x_1 nor y_j is zero. The ratio x_2/x_1 is the value at q of f=v_1/u_1 in Q(X). Since x_2/x_1 is irrational, f is nonconstant. The equality v_j(q)=f(q)u_j(q), cleared of denominators, is a polynomial identity because q is transcendental. Hence u_1,u_2 lie in U_f. They are Q-linearly independent because y_1,y_2 are, contradicting dim U_f<=1. QED.

This rules out a 2-by-3 grid as well. It is stronger than checking one guessed arrangement of the five input numbers.

## 3. Why algebraic linear coefficients do not evade the gate

Let ell_1,...,ell_5 be the five real logarithms under a hypothetical algebraic-input pure transcendental-node profile. They are Q-linearly independent: a linear relation would give a zero polynomial in W at q. Baker's theorem makes them Qbar-linearly independent.

Let gamma be a real number in span_Qbar{ell_i}, and suppose exp(gamma) is algebraic. Then gamma belongs to span_Q{ell_i}.

To prove this, suppose gamma did not belong to the rational span. The six real logarithms ell_1,...,ell_5,gamma would be Q-linearly independent, hence Qbar-linearly independent by Baker. But gamma was an algebraic linear combination of the first five, a contradiction. Thus the rational span is already the full set of logarithms of positive algebraic numbers lying in the algebraic linear span of these data.

Accordingly, allowing algebraic-coefficient linear preprocessing, while still requiring the resulting entries to be real logarithms of algebraic numbers, does not create an eligible multiplicative grid. This does not cover nonlinear transformations, additional logarithms from outside this span, or arbitrary transcendental coefficients.

Primary theorem statement: Dasgupta, *Ranks of matrices of logarithms of algebraic numbers I*, Theorem 1.2:
https://arxiv.org/html/2303.02037v1

## 4. What the six-exponentials theorem does and does not give

The six-exponentials theorem requires two Q-independent x values and three Q-independent y values. If all six exp(x_i*y_j) were algebraic, it would yield a contradiction. Our proposed approach was to construct those six logarithms from the five original input logs by rational combinations, which preserve algebraicity of exponentials. Sections 1–3 show this is impossible on the hypothetical surviving branch, even before invoking that theorem.

This is a **method-admission failure**, not a counterexample to the six-exponentials theorem and not a proof that the original pure profile exists. It prevents claiming that “five independent algebraic logarithms on one polynomial curve” automatically supplies the rectangular rank-one arrangement demanded by that theorem.

Primary statement and attribution: Waldschmidt, *Linear Independence of Logarithms of Algebraic Numbers*, Theorem 1.7, printed introduction page 1-7 (PDF page 10):
https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/LIL.pdf

## 5. Remaining stronger attempt

The Waldschmidt–Masser theorem is stronger than this rank-one grid criterion. Its unconditional conclusion applies when a logarithm matrix has rank below mn/(m+n), and gives a large rational zero-block after invertible rational row/column transformations. It is not the full Structural Rank Conjecture. The latter is equivalent to the algebraic independence conjecture for Q-independent algebraic logarithms, by the Roy theorem described in the same primary source. No conjecture is assumed here.

A next potentially decisive arithmetic construction would have to produce a suitable higher-rank matrix from these exact five logs, prove the required numerical rank defect on the pure curve, and exclude the theorem's rational zero-block alternative. This note does not yet provide such a matrix or prove none can exist. The absence of quadratic relations only excludes the direct rank-one grid route; it does not settle higher-degree determinantal identities.

The original five-coordinate cone promise, original algebraic input, all-core reduction, one shared physical source bank and strict finite-source semantics are unchanged. Even excluding this exceptional COMMON branch would not alone finish hidden finite heads, coupled interfaces or INDEPENDENT/BOTH recognition. The general terminating recognizer and complete NO side remain open.

Evidence: hand proof and explicit finite degree lists only. No new execution receipts, public peer review, formal verification or master-completeness claim.

## 6. The square determinant-linearization shortcut also fails

This is a second candidate hand argument, using the accepted simple-root certificate rather than a new transcendence assumption.

Let u=ell_3>0, v=ell_6 and z=ell_10, and let Phi(u,v,z)=u^8 P(v/u,z/u) be the accepted homogeneous degree-eight polynomial. On the physical pure branch, P_y is nonzero because the quartic's physical root is simple. Thus

    partial_z Phi = u^7 P_y(v/u,z/u) != 0.

Suppose an s-by-s matrix N(u,v,z) has affine-linear rational entries and

    det N = R(u,v,z) Phi(u,v,z),

where R is a polynomial nonzero at the pure point. If rank N were at most s-2 there, every cofactor would vanish. Differentiating the determinant with respect to u,v,z would then give zero gradient. But the displayed determinant identity gives gradient R times gradient Phi at that point, which is nonzero. Therefore rank N=s-1.

The polynomial degree of det N is at most s and is at least eight, so s>=8. The unconditional square Waldschmidt–Masser hypothesis is rank N<s/2. A corank-one representation cannot satisfy it. In addition, affine entries containing nonzero rational constants are not automatically logarithms of algebraic numbers, so those entries need a separate admission argument; the rank obstruction already applies even if that issue is repaired.

More generally, suppose det N=R Phi^k, with integer k>=1 and R nonzero at the point. Along a rational or real direction transverse to Phi=0, this determinant vanishes to order exactly k. If N has corank c, every term in the determinant of N(point)+t*dN(direction) vanishes to order at least c, as seen after invertible constant row/column changes putting N(point) in rank normal form. Hence c<=k. Degree comparison gives s>=8k, so

    rank N >= s-k >= 7s/8 > s/2.

This covers determinant-power constructions and direct-sum repetitions whenever the stated polynomial identity holds. Tensoring numerical matrices can reduce a rank ratio, but its entries become products of logarithms; algebraicity of their exponentials is not supplied by the original data or by Baker's linear theorem. Therefore that operation cannot silently remain inside the logarithm-matrix theorem's hypotheses.

This result does NOT exclude a different rectangular or higher-corank construction using all five coordinates and independent polynomial relations. It identifies the exact next required bridge: enough rank collapse inside the admitted logarithm entry class, with the rational zero-block alternative excluded, not merely a determinant vanishing at the degree-eight equality.


# Exact next arithmetic target: a simultaneous matrix-pencil obstruction

22 October 2026. dot (OpenAI-assisted research), prepared for Nolan. Source/theoretical protocol only; no search or solver was run.

The preceding SIX-EXPONENTIALS-GATE.md excludes direct rank-one grids and determinant-power linearizations of the accepted three-log polynomial. It does not close the stronger Waldschmidt–Masser route. The remaining construction can be stated entirely in rational polynomial linear algebra, with a sufficient simultaneous zero-block exclusion that does not presume a rational-solvability oracle.

## Desired certificate

Choose positive integers m,n, rational m-by-n matrices A_3,A_6,A_10,A_15,A_21, and an integer r. Form

    M(X)=sum_{j in {3,6,10,15,21}} T_j(X) A_j,
    T_j(X)=sum_{k=0}^{j-2}(j-1-k) X^k.

Supply proofs of:

1. rank over Q(X) of M(X) is at most r, for example exact vanishing of every (r+1)-minor.
2. r < mn/(m+n).
3. For every integers a<=m,b<=n with a/m+b/n>1, there are no simultaneous subspaces U subset R^m and V subset R^n of dimensions a,b such that u^T A_j v=0 for every u in U, v in V and every j.

Condition 3 is deliberately stronger than excluding only rational subspaces, which is all the transcendence theorem needs. It is a finite RCF sentence for each (a,b): use full-column-rank bases P,Q and equations P^T A_j Q=0, with rank expressed by a nonzero maximal minor. This is a theoretical decidability statement, not a QE run or a promise that a useful certificate exists.

## Why such a certificate would settle the exceptional pure branch

Suppose there were a promised pure profile with transcendental q and all five b_j positive algebraic. The actual log matrix would be

    L=sum_j (log b_j) A_j = w(1-q) M(q).

Its rank is at most r. Apply the complex Waldschmidt–Masser theorem to L; its entries are real logarithms of algebraic numbers because they are rational combinations of the log b_j. The theorem yields rational invertible row/column transformations with a zero a-by-b block satisfying a/m+b/n>1.

Each entry of that block is a rational linear combination of the five log b_j. The latter are Q-linearly independent when q is transcendental, since their distinct-degree polynomials evaluated at q are independent. Therefore every coefficient vanishes separately. The same block is zero for every transformed A_j. The corresponding rational row/column subspaces contradict condition 3. Hence no such exceptional pure profile can exist.

This is an unconditional *sufficient construction target*, not a claim that a certificate has been found. It attacks the accepted source-faithful arithmetic branch, not an unrelated matrix problem. The original cone promise is used by the inherited equivalence; the argument does not create a converse from arbitrary triples or arbitrary matrices to G3.

## What the present results remove from this search

- Rank-one grids cannot supply the desired certificate from the five-log span; the degree-difference argument is independent of the chosen rational preprocessing.
- Square determinant-power representations of the degree-eight Phi cannot cross the required rank threshold, even if all their entries are correctly admitted logarithms.
- Affine constant entries, nonlinear products of logs, or fresh external logarithms are not part of the above admitted pencil class.
- An exact check of a finite unsuccessful collection would not show that no pencil exists. No arbitrary finite search cutoff is a general negative certificate.

## Remaining master bridge

A successful pencil would eliminate the transcendental pure-node branch of the inherited cone-promised COMMON reduction. It would not by itself classify every original G3 input, hidden finite heads, coupled/protected interfaces, or INDEPENDENT/BOTH chronological words. Those still require a total source-faithful negative-completeness or effective witness-bound theorem. Conversely, failure to construct the pencil does not prove the pure branch exists or that G3 is undecidable.

Primary theorem: Dasgupta, *Ranks of matrices of logarithms of algebraic numbers I*, Theorem 1.6 (complex statement), https://arxiv.org/html/2303.02037v1 . The paper separately labels the stronger Structural Rank assertion a conjecture; it is not used here.


## Prior-work and handoff notes

The polynomial-space mechanism is related to the established notion of a Sidon space: Roth, Raviv and Tamo, *Construction of Sidon spaces with applications to coding*, https://arxiv.org/abs/1705.04560 . That paper treats finite extension fields; the present elementary degree proof is supplied directly in Q(X). No novelty claim for the general mechanism is made.

The newer Dasgupta–Kakde paper, *Ranks of matrices of logarithms of algebraic numbers II: The Matrix Coefficient Conjecture*, https://arxiv.org/abs/2408.08178 , explicitly presents its stronger matrix-coefficient conclusion as a conjecture. Its introduction leaves an implication in the proposed strategy open. It is not used as an unconditional supplier here. The published article is DOI https://doi.org/10.1016/j.aim.2025.110753 .

In Section 6, dN(direction) denotes the linear directional derivative of the affine pencil, not its affine evaluation. This notation preserves the stated order-of-vanishing argument.

Exact inherited three-log proof: https://github.com/Sodelin/Research-Commons/blob/8621b94a30e12794fafbf34c721a7d583a984fd0/research/2026-10-10-dot-g3-three-log-purity-1210z/THREE-LOG-PURITY-REDUCTION.md . Its scoped acceptance is recorded in the README and independent review linked above; it does not transfer acceptance to these new arguments.

The next unresolved arithmetic statement is the existence or exclusion of a higher-rank admitted logarithm pencil meeting the three conditions above. No such pencil has been supplied. The master remains stronger: total source-faithful recognition for all admitted finite rational/effectively algebraic original observations, one shared strict positive finite physical source of unbounded size, original IDs and chronology, and terminating NO including unattained zero-distance inputs. Neither new candidate is a proof of that statement or of its impossibility.
