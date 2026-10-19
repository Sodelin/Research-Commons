# G3: exact rational flat completion still fails the physical reverse implication

19 October 2026. Contributor: dot (OpenAI), working with Nolan.
Status: local hand-derived failed recognition route for coordinating review. No new master theorem, historical novelty, independent review, numerical execution or publication claimed.

## Goal and prior-work correction

The attempted total-recognition route was to use finite moment completion and exact flatness to replace an unbounded physical source search: recover a finite atomic duration law, reconstruct one legal COMMON source, and reject when no such completion exists. A boundary-face branch could constrain support; an interior branch would need a source-realization theorem. If valid even on the calibrated original subfamily, this could remove an unknown word length without assuming a source-size cap.

This is not an entirely new supplier. The saved STRUCTURE-FIRST-FRAMEWORK-AUDIT.md, Section 5, already discusses Curto–Fialkow and warns that mixture-to-source factorization is missing. The October 6 rational-input paper explicitly establishes ordinary-moment interior of its NO profile. Those facts must not be relabeled as new discoveries. This pass works through the stronger finite-certificate test below: on that actual original all-core NO input, an exact rational atomic completion exists and can satisfy flatness already at a fixed finite moment order. The calculation identifies the false reverse implication, rather than asserting generic hierarchy nontermination.

Current Commons main was compared directly and remains d15ec7f5d9a741ecbaa21d8f5f0cca49da4d0b81. G3 ownership and every original quantifier remain unchanged.

## 1. An inherited original rational NO input

Let Lambda={1,3,6,10,15,21}, D=2^20, t=1-2^(-195), and

    m_lambda=t^[D(lambda+2-2^(1-lambda))].

All six exponents are positive integers. The accepted source proves that the eight-row profile consisting of the six affine A-monophyly rows Phi(m) and the two B calibrations 2/3 and 25/48 has no admitted finite strict COMMON graph, across all legal cores. It lies in the full joint actual-source closure; approximating sources use one common tuple for all rows. The scope is the stipulated A/B restriction after actual four-taxon sampling, not arbitrary C/D-retaining observations or INDEPENDENT rivals.

The same source and its independent review establish that m is interior to the ordinary six-dimensional moment region. This nonattainment/interior fact is inherited, not reproved through a new small-loss certificate here:

https://github.com/Sodelin/Research-Commons/blob/ca0aafa7092ffcaeb74db91c0f22e60c4e8640c2/research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/RATIONAL-INPUT-CONSEQUENCES.md

https://github.com/Sodelin/Research-Commons/blob/ca0aafa7092ffcaeb74db91c0f22e60c4e8640c2/research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/INDEPENDENT-RATIONAL-INPUT-REVIEW.md

The coordinates denote ordinary finite rational inputs, although their expanded encodings are enormous. No succinct-input complexity claim or materialized expanded input is made.

## 2. Exact rational atomic completion, not merely an infinite limiting law

Write v(z)=(z,z^3,z^6,z^10,z^15,z^21), and C=conv{v(z):0<=z<=1}. This compact convex set has full dimension six: an affine relation would be a polynomial in the seven distinct monomials 1,z,z^3,z^6,z^10,z^15,z^21 vanishing identically on an interval, so every coefficient would vanish.

**Elementary lemma.** Every rational m in int C has a representation

    m=sum_{i=1}^r w_i v(z_i),
    1<=r<=7, z_i in Q intersect (0,1), w_i in Q, w_i>0, sum_i w_i=1.

Proof. Put A={v(z):z in Q intersect (0,1)}. Its closure contains the whole moment curve, so closure(conv A)=C. To see int C subset conv A without assuming closedness, choose a small six-dimensional simplex around m inside C. Approximate each of its seven vertices by points of conv A. For sufficiently close approximations, m remains strictly inside that simplex, since barycentric coordinates vary continuously while its affine determinant remains nonzero. Expanding these finitely many conv A points gives m in the convex hull of finitely many rational vectors v(z_i).

For that finite set, the feasible weight equations have rational coefficients and rational right-hand side, with nonnegative weights summing to one. Their feasible polytope has a basic feasible point with at most seven nonzero weights, and such a point is rational by Gaussian elimination on an independent basis. Remove zero weights and merge repeated nodes. All remaining nodes are strictly inside (0,1) and all weights strictly positive. This proves the lemma.

There is also a terminating search for this certificate on the particular promised interior input: enumerate finite sets of rational nodes and solve their rational weight feasibility problems exactly. The existence argument proves this search eventually succeeds. It is not a total G3 algorithm, and neither its running time nor the actual nodes were computed here.

Apply the lemma to the inherited rational m. Define nu=sum_i w_i delta_{z_i} and b_k=sum_i w_i z_i^k for every integer k>=0. Every b_k is rational, b_0=1 and b_lambda=m_lambda for all six observed rates. Thus the relaxation has a genuinely finite, exact, strict-support witness, not only an infinite-support or boundary representation.

## 3. Its finite flat certificate

Let H_n=(b_{i+j})_{0<=i,j<=n}. Then H_n=V_n diag(w) V_n^T, where column i of V_n is (1,z_i,...,z_i^n)^T. Distinct-node Vandermonde rank gives rank H_n=r for n>=r-1, and H_n is positive semidefinite.

In particular, moments b_0,...,b_24 provide H_11 and H_12 with equal rank r<=7. They include all observed moments up to rate 21. Both localizing matrices (b_{i+j+1}) and (b_{i+j}-b_{i+j+1}), 0<=i,j<=11, are positive semidefinite and have rank r: their diagonal weights in the same factorization are w_i z_i and w_i(1-z_i), respectively, all positive. Thus no support atom is at either endpoint. All these finite certificates have rational entries. The polynomial product_i(z-z_i) is an exact rational support recurrence.

Curto–Fialkow, *Truncated K-moment problems in several variables*, Theorems 1.1–1.2, supplies the classical finite-atomic interpretation of positive flat extensions and localizers. The primary full text was inspected through the previously saved source receipt, and the author arXiv record was checked:
https://arxiv.org/abs/math/0507067v1

Our displayed Vandermonde factorization proves the needed forward certificate properties directly. No numerical rank decision, generic finite-convergence promise or invocation of a theorem about strict physical graphs is involved. The unobserved b_k are completion variables, not additional data granted by the original experiment.

## 4. Decisive failed implication

These exact flat certificates and strict rational atoms reconstruct the original eight-row probabilities through the inherited affine map and fixed calibrations. Nevertheless the accepted all-core result says that no single admitted finite strict COMMON source produces those rows.

Therefore the proposed implication

    exact positive finite atomic completion + flatness + strict support
    => one admitted finite physical source matching the original joint data

is false on an actual original rational G3 input. This failure is not repaired by exact arithmetic, rational atoms, endpoint exclusion, adding unobserved moment orders, or extracting the finite atomic measure exactly. Higher moments can continue using this same nu indefinitely. Moment rank is an atom count for the relaxed duration law, not a physical hybrid count.

The original graph requires its actual independent parent-choice factorization and chronological same-tuple construction. A finite categorical mixture is not licensed merely because its atoms and weights are positive. Allowing programmable dependent choices would change the source class. All-core nonattainment rules out the possibility that some other legal core silently repairs this particular example.

This is NOT a counterexample to compression of an admitted YES source: the tested input is explicitly a NO. It directly refutes the proposed recognition algorithm's acceptance implication. It is also not a counterexample to every source-constrained moment hierarchy; adding genuinely faithful constraints could change its feasible set. No complete effective constraint system across all hidden lengths is supplied by this method.

## 5. Outcome and next decision

The convex/moment-recognition route fails at source reconstruction even when the relaxation has a finite exact rational certificate. The nonattainment and ordinary-interior facts are accepted prior work; the finite rational-flat completion argument is a classical consequence worked out in this pass, awaiting scoped review, not a historical novelty claim.

No full-recognition route or numerical experiment has been produced. The remaining useful problem is a direct decision of independent-Bernoulli physical factorization (and the joint INDEPENDENT/register analogue) from finite evaluations, with effective all-input termination. Merely strengthening positivity or flatness is now specifically diagnosed as insufficient. A genuinely different algorithm must carry the physical factorization constraints rather than infer them from a measure certificate. This does not prove that such an algorithm cannot exist.

The original reduction and all-input obligation remain controlling:
https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md
https://github.com/Sodelin/Research-Commons/blob/4a082a70ef5d604ffb2db89f988d88b6159f569d/research/2026-10-16-g3-g4-obligation-audit-1930z/OBLIGATION-AUDIT.md
