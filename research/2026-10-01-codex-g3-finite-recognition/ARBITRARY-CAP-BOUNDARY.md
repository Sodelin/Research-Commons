# G3 common-chain arbitrary-cap boundary recognition

Session: CODEX-G3-FINITE-RECOGNITION-20261001.
Contributor/publisher: Codex.
Status: submitted hand proof and exact rational boundary controls; independent review pending.
Master: general finite-input, all-cap, both-mechanism recognition remains OPEN.

## 0. Decision brief

For a typed COMMON serial two-port chain at ANY supplied finite copy cap M, the part of exact recognition lying on the exposed boundary of the sparse moment body is decidable. The algorithm computes an exposing polynomial, recovers a unique finite algebraic atom law, and invokes the complete finite-atomic binary-factor test. Positive boundary laws have at most floor((M-1)/2) atoms and need at most floor((M-3)/2) unequal bigons if they are source-realizable.

This is a source-preserving exact classification of a nontrivial arbitrary-cap regime. Interior points of the ordinary moment body are not thereby classified, because serial binary-source realizability is a smaller condition than arbitrary positive-mixture realization.

## 1. Contract and provenance

Input: a full typed common forest kernel at finite cap M, or its exact algebraic sparse signature m=(1,m2,...,mM), exponents lambda_j=j(j-1)/2. First check the inherited exact linear forest/moment correspondence. No independent inheritance, metric law, control response family or unrelated whole-network marginal is identified with this typed signature.

Dependencies: joint-law common signature theorem and G3 ATOMIC-AND-CONTROL.md, Section 1 (complete finite-atomic chain recognition). The latter's atom-ratio factor algorithm is reused with attribution, not claimed as new. The contribution here is effective boundary detection/recovery from a FINITE MOMENT VECTOR and a cap-dependent positive source bound, rather than assuming the full atom law is already supplied.

## 2. Finite algebraic recognition of the ordinary sparse moment body

Define H_M as all vectors (1,E[X],E[X^3],...,E[X^lambda_M]) of probability measures on [0,1].

A finite formula decides H_M membership. By finite-dimensional convex Caratheodory representation, at most M atoms suffice. Decide
    exists x_1,...,x_M,w_1,...,w_M:
    0<=x_i<=1, w_i>=0, sum w_i=1,
    sum_i w_i*x_i^lambda_j=m_j for j=2,...,M.
Zero weights and repeated atoms are allowed in this TEST. They do not become source permission for zero/infinite population lengths.

If this formula is false, no positive common chain realizes m. The procedure terminates by real-closed-field decision.

## 3. Effective exposed-boundary detection

For a feasible normalized moment vector, decide whether coefficients c_1,...,c_M exist with
    sum c_j^2=1,
    sum c_j*m_j=0,
    forall x in [0,1], P(x)=sum c_j*x^lambda_j>=0.

This is a finite ordered-field formula with algebraic coefficients. Quantifier elimination decides it and yields algebraic c_j if true.

The condition holds precisely on the relative boundary of the normalized moment body. A supporting affine hyperplane can be converted to P by its constant coefficient, and conversely zero expectation of a nonzero nonnegative P places the vector on a supporting hyperplane. H_M has full affine dimension M-1 because the distinct monomials are independent on [0,1]; P cannot be identically zero.

If no such P exists, the input is ordinary-moment INTERIOR. This is a terminating geometric classification, not a terminal source YES.

## 4. Unique algebraic atom recovery

If the boundary test succeeds, isolate all real roots of P in [0,1]. Their distinct set Z is finite and algebraic.

Any probability measure representing m must be supported on Z, since it has zero expectation of nonnegative P. The weights solve the finite linear system
    sum_(z in Z) w_z*z^lambda_j=m_j, j=1,...,M.

That system has at most one solution. The generalized Vandermonde columns for distinct positive nodes are independent by the Chebyshev/Descartes zero-count argument. If zero is a node, separate its column using the constant coordinate; the remaining positive-node generalized Vandermonde remains full rank.

There are at most M-1 distinct roots in [0,1]. If the constant term is nonzero, zero is not a root and Descartes bounds positive roots by M-1. If it vanishes, the remaining polynomial has at most M-1 nonzero monomials and at most M-2 positive roots, plus possibly zero. Thus the weight recovery is determined by the supplied coordinates.

Delete zero-weight nodes. If a positive-weight atom is zero or one, reject for actual positive common-chain realization: every finite positive chain's total survival lies strictly in (0,1). This is a source rejection, even though the input belongs to the ordinary compact moment body.

For a potentially source-realizable boundary law all s atoms are interior. Each is a double or higher even-multiplicity positive root of nonnegative P. Descartes therefore gives
    2s<=M-1, hence s<=floor((M-1)/2).

## 5. Complete finite binary-factor recognition

For the recovered positive atom law (x_j,w_j), set A=max_j x_j. Its unique law is source-realizable if and only if it has a factorization
    X=A product_(i=1)^L q_i^B_i,
    0<q_i<1, 0<p_i<1,
    B_i independent Bernoulli(p_i), L<=s-1.

Every q_i must equal x_j/A for some nonmaximum atom: choosing only that factor has positive weight and contributes an actual support atom. Every factorization's support contains the L+1 strictly decreasing prefix products, giving L<=s-1. These are the inherited finite-atomic necessity arguments.

Algorithm: enumerate multisets of at most s-1 ratios from the finite algebraic list x_j/A. Compute all subset products exactly, coalescing equal values. Discard supports different from the recovered support. For each remaining ratio list, solve the polynomial equations matching each coalesced atom weight, with all p_i strictly interior. Return YES with a witness if any test is feasible, and otherwise NO after the finite list is exhausted.

Every enumeration and exact algebraic test terminates. The unique representing measure ensures that rejecting its binary factorization excludes EVERY common serial chain fitting the original moment vector, not only the recovered representation.

For an affirmative factorization, realize its positive baseline and all bigons by the inherited explicit construction. For L>=1 set c=1-(1-A)/(4L+1). Use entering connector A/c^(2L), arms c and c*q_i for bigon i, and a following connector c for each bigon. The resulting baseline is A and all survivals are strictly interior because c^(2L)>A. For L=0 use an ordinary edge with survival A.

Combining the atom and factor bounds gives
    L<=floor((M-3)/2)
for any positive boundary chain at M>=3. This is a bound on unequal stochastic bigons; ordinary deterministic equal-arm pieces can be absorbed.

## 6. Correctness and maximal scope of this component

- Outside H_M: NO.
- Boundary with endpoint atom: NO.
- Positive boundary with feasible binary factorization: YES and actual source.
- Positive boundary with no feasible factorization: NO for every serial common source.
- Ordinary moment INTERIOR: not resolved by this theorem.

The moment-space boundary is not necessarily the boundary of the actual source-image closure. A point can lie inside H_M while still being outside the actual serial-source closure. Therefore recognizing H_M, or proving interior attainment for the ACTUAL source semigroup, does not close this last branch without recognizing that actual closure.

This is a general-M necessary-and-sufficient boundary algorithm. It does not quietly relabel itself a general all-input algorithm.

## 7. Exact controls

The accompanying boundary_checks.py constructs nonnegative exposing polynomials in span(1,x,x^3,x^6,x^10,x^15,x^21) with double zeros at:
- (1/4,1/2,3/4), weights (1/3,1/3,1/3): exact common-chain rejection, because three-point binary support must be geometric.
- (1/8,1/4,1/2), weights (1/4,1/2,1/4): exact attainment by baseline 1/2 and two independent Bernoulli factors of ratio 1/2, weight 1/2 each.

Each degree-21 exposing polynomial was divided EXACTLY by the six-degree squared-root factor. Both quotient polynomials have 16 strictly positive rational coefficients. This certifies nonnegativity on [0,1] and that the interior zeros are precisely the supplied three atoms. Zero expectations and atom weights were checked by Fraction arithmetic.

This replays and generalizes the detection route of the existing G3 atom obstruction; the obstruction itself retains its original attribution. No universal QE implementation, arbitrary-cap source catalogue or independent review was executed here.

## 8. Remaining general attack

The unresolved branch is exact membership of higher-cap actual source kernels at ordinary-moment-interior points, especially nonattained boundary points of the actual SOURCE closure. For independent inheritance, the full noncommuting capped forest matrix must be retained; the common scalar moment test cannot substitute for it.

A full solution needs either a computable exact finite-factor/source-size bound or a valid finite-input impossibility reduction inside the biological source class. The published all-cap computability reduction and artificial semigroup examples do neither.

## 9. Glossary

Exposing polynomial: a nonzero polynomial nonnegative on the allowed survival interval whose zero expectation forces all mass onto its roots.
Ordinary moment body: signatures of arbitrary positive mixtures, including endpoint limits.
Actual source image: signatures generated by finite positive serial biological chains with independent natural coins.

## 10. Bibliography

Classical finite-dimensional convex representation, polynomial root isolation and real-closed-field quantifier elimination. See the Basu reference and checked Chebyshev principal-representation source in PROOFS.md and COMMON-CAP-FOUR.md.
Biological signature/factor premises: attributed Commons joint-law and G3 finite-atomic packets.

## 11. Process-integrity assessment

The algorithm distinguishes algebraic atom recovery from a supplied atom-law assumption; support uniqueness is proved rather than presumed. Effective enumeration is finite at every step. The inherited common-kernel compiler and finite-atomic source construction remain source-critical dependencies. This is not a systematic review.

## 12. Robustness assessment

The result fails if moments do not determine the declared whole capped kernel, if independent routing is substituted, or if the interface is an untyped whole-network marginal. Endpoint zeros are retained until their weights are checked. No empirical tolerance is used to certify a zero expectation. The source-interior branch stays open explicitly.

## 13. Zotero/Obsidian integration

Tag G3, arbitrary-cap, common-chain, exposed-boundary, finite-algebraic-input. Link the previous ATOMIC-AND-CONTROL theorem as its finite-factor dependency and the cap-four result as a separately closed branch. Do not label either as master G3 closure.

## 14. Publication/verification boundary

Hand proofs, two exact rational exposing-polynomial controls, and binary-law reconstruction are supplied. No independent acceptance or proof-assistant verification is claimed. Publishing this packet does not establish peer receipt or background execution.
