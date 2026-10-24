# No mixed normalized linear square decoder at any finite cap

Stable key G3-NORMALIZED-MIXED-LINEAR-SQUARE-ADMISSION-01.
Existing G3 owner, 24 October 2026 UTC. PROVED BY HAND at the exact scope
below; author self-review complete. Independent correctness review and Lean
formalization have not been performed. No source, tuple, coefficient,
symbolic/numerical control, model, solver or native execution is used.

This closes the MIXED-BLOCK limitation explicitly left by the preceding
single-cell square theorem. It is a supporting exclusion, not a replacement
full G3 attack, an AG-Pair refutation or original recognition/NO closure.

## 1. Actual source and exact theorem

Let B(q,q,g) be ONE unmarked private natural-INDEPENDENT cell, with strict
equal arm survivals 0<q<1 and parent0 probability 0<g<1. Native parent1
gamma=1-g and the original ordered parent IDs are retained. Each entering
CURRENT ROOT routes once independently. The two ordinary arm processes
are pooled afterward; old opaque trees are grafted intact. This is the
retained smaller private forest operator, not a full population/register
Code law or a resampled/exposed COMMON bank.

Write v=g(1-g), lambda_r=r(r-1)/2, and use the SAME cell at every probe cap:

    z=b2=q+2v(1-q),       tau=-log z,
    C=exp(-tau Q) B,
    A=3p7(2,2,1,1,1)-2p7(3,1,1,1,1),
    J=z^(-21) A.

Each p is the probability of ONE specified set partition, not orbit mass.
Q is the ordinary current-root coalescent generator on the applicable
complete finite forest carrier. The exponential with negative duration is
algebraic normalization only; it is not a positive physical source factor.

Allow ANY constant real linear functional L on ANY finite collection of
complete C kernels at arbitrary finite root caps and arbitrary opaque input
forests. Fixed bookends/readouts and a fixed reference-basis change may be
absorbed into L. Its coefficients may depend arbitrarily on a fixed reference
h; they cannot depend on the unknown q or g. In particular L may mix ALL
ordinary-Q spectral blocks and may select blocks in a reference eigenbasis.

For EVERY nonzero constant c, there is NO identity

    L(C(q,g))=c J(q,g)^2                              (1)

on a nonempty OPEN TWO-DIMENSIONAL strict source domain. Equivalently use
(q,v) with 0<v<1/4. The conclusion applies to arbitrarily weak open source
regions. Unlike the raw/single-block predecessor, this mixed-block theorem
does not assert nonexistence on the FAIR LINE ALONE, a one-dimensional set.

## 2. Predecessor/successor comparison

The COMPLETE nearest predecessor is
[SINGLE-CELL-MODE-PRODUCT-OBSTRUCTION.md](https://github.com/Sodelin/Research-Commons/blob/0f0113be1cc3bf860e0ba235819688c4e92057d5/research/2026-10-24-g3-asymptotic-root-grid/SINGLE-CELL-MODE-PRODUCT-OBSTRUCTION.md),
8784B/SHA256 8ef47cd473b18c9746277eec77ee149d941400c93dd5403a630b7f172fde7d91.
It proves the raw all-cap exclusion and ONE ordinary-Q normalized-block
exclusion. It expressly leaves mixed normalized/reference-frame responses
outside its conclusion. Those earlier proofs remain unchanged and reused.

The COMPLETE reused history source is
[FULL-SEVEN-BAND-ORIENTATION.md](https://github.com/Sodelin/Research-Commons/blob/a0606d481186c000b106ee717a572e1e7e724743/research/2026-10-24-g3-asymptotic-root-grid/FULL-SEVEN-BAND-ORIENTATION.md),
14246B/SHA256 00332ce1296773cbc59566e511502f0851fa61bc593bb8312e3a9a5086aa56ee.
Its exact ordinary-arm lowest-mode coefficient and fair q4 coefficients
are OLD/REUSE. Its full heterogeneous band condition, recent biased source
branch and bounded-Psi exclusion do not assert (1).

The current projective spectral theorem supplies the retained complete
current-root carrier and ordinary semisimplicity context. Root-count
triangularity and the exact coloured lift B=J_route exp(uG)D_pool are OLD.
The notation J_route here is unrelated to the scalar J above.

The pre-write comparison is retained in G3-MIXED-SQUARE-PREFLIGHT-20261024.md.
Relevant current lookup/audit/G4 pole, degree, mixed-square and mode aliases
were searched, and COMPLETE assembly171 was read as attributed package
evidence. This is bounded source comparison, not exhaustive corpus absence
or a historical novelty claim. The new implication below is the exclusion
of arbitrary finite MIXTURES by their joint pole/coin-degree restrictions.

## 3. Root-count support bounds the coin degree of each block

On a finite current-root forest carrier let P_r=P_r(Q) be the ordinary
spectral projector for eigenvalue -lambda_r. The ordinary generator only
merges roots; its k-root diagonal block is -lambda_k times the identity.
Its root-count annihilator is square-free, as already proved/reused.

Every ROW of P_r has support only on states with AT MOST r current roots.
Indeed that row is a left eigenvector of Q. If its highest nonzero root
stratum were k>r, the eigenvector equation in that stratum would be

    -lambda_k w_k=-lambda_r w_k.

No higher stratum can contribute to it. Distinct lambda_k force w_k=0,
a contradiction. Descending through the finite strata gives the claim.
An optional isolated empty-input identity has no effect on any pole below.

Given k entering CURRENT roots, the bare B routing probabilities are
polynomials in g of degree at most k. Ordinary arm kernels do not depend
on g. Equal arms and pooled UNMARKED exits make the whole response invariant
under g -> 1-g. A symmetric polynomial of degree at most k is a polynomial
in v=g(1-g) of degree at most floor(k/2): use g=(1+w)/2, so symmetry means
an even polynomial in w and w^2=1-4v.

The OLD two-arm spectral lift makes each bare response polynomial in q,
with powers lambda_a+lambda_b. Consequently, for EVERY finite L,

    L(C)=sum_r z^(-lambda_r) T_r(q,v),                (2)
    T_r is polynomial in q,v,
    degree_v T_r <= floor(r/2).                      (3)

The sum is finite; aggregate equal r across different probe caps. Equations
(2)--(3) hold even when L uses an arbitrary fixed reference basis. A fixed
linear change of basis does not change the source-degree statement. No
assumption of a shared eigenbasis for different source kernels is used.

## 4. Exact all-coin leading coefficient of the OLD seven-root contrast

For an ordinary arm whose specified output blocks have sizes a_i and count
k, the OLD lowest-mode q^(lambda_k) coefficient is

    (2k-1)! product_i(a_i!)/(n_arm+k-1)!.             (4)

Five output blocks require at least a 2+3 split between the two arms, so
the least possible exponent is lambda_2+lambda_3=4. There are no q5 terms:
5 is absent from the OLD two-arm mode set {lambda_a+lambda_b}.

Here is the finite routing calculation for q4 at arbitrary g. Choose the
TWO final blocks assigned to one arm and include its reversed three-block
allocation. If their total initial-token weight is w, their joint routing
weight is

    g^w(1-g)^(7-w)+g^(7-w)(1-g)^w.

For w=3 or4 this is v^3; for w=2 it is v^2(1-3v). Formula (4) gives:

| specified partition | w | number of two-block choices | arm-product coefficient per choice |
| --- | ---: | ---: | ---: |
| (2,2,1,1,1) | 4 | 1 | 1/5 |
| (2,2,1,1,1) | 3 | 6 | 1/6 |
| (2,2,1,1,1) | 2 | 3 | 2/21 |
| (3,1,1,1,1) | 4 | 4 | 3/10 |
| (3,1,1,1,1) | 2 | 6 | 1/7 |

Each unordered bipartition is counted once by its two-block side; its two
ordered-arm choices are already in the displayed routing weight. Hence

    [q4]p22=(2/7)v^2+(12/35)v^3,
    [q4]p3 =(6/7)v^2-(48/35)v^3,
    [q4]A  =-(6/7)v^2+(132/35)v^3.                   (5)

At v=1/4 these reduce to the OLD 13/560, 9/280 and 3/560 coefficients.
This is hand use of (4), not a replay of a source/coefficient producer.

At v=0 the cell is one deterministic ordinary arm. For the two specified
five-block partitions the compatible two-merger history counts are 2 and
3; their common holding-time factor cancels in 3p22-2p3. Thus A(q,0)=0
identically. Since A is polynomial, it is divisible by v. Together with
the missing modes and degree_v A<=3 this proves the exact polynomial form

    A(q,v)=q^4[-(6/7)v^2+(132/35)v^3]+q^6 v R(q,v),  (6)

for a polynomial R. This includes ALL higher q modes, not a fitted jet.

## 5. A pole and a missing numerator coefficient exclude EVERY mixture

Make the invertible rational coordinate change over the field R(q):

    v=(z-q)/(2(1-q)).

Write A(q,z)=a0(q)+a1(q)z+a2(q)z^2+a3(q)z^3. Formula (6) gives

    a0(q)=-(3/14)q^6+O(q^7),
    a2(q)=-(3/14)q^4+O(q^5),
    a3(q)= (33/70)q^4+O(q^5).                        (7)

In particular a0 is NONZERO in R(q), so c*z^(-42)*A^2 has EXACT pole
order42 at z=0. Also

    [z5]A^2=2*a2*a3=-(99/490)q^8+O(q^9) !=0.        (8)

By (3), each transformed T_r is polynomial in z of degree at most
floor(r/2), with coefficients in R(q). If T_r is nonzero, the pole order
of z^(-lambda_r) T_r therefore lies in

    [lambda_r-floor(r/2), lambda_r].                 (9)

For r>=3 its lower endpoint is STRICTLY greater than lambda_(r-1),
because r-1>floor(r/2). Thus the largest nonzero r in (2) cannot have
its pole canceled by any lower block. This remains true at arbitrarily
large finite caps; a larger cap cannot supply a hidden cancelling pole.

If the largest r is at most9, its pole is at most lambda_9=36, less than42.
If r>=11, its pole is at least lambda_11-floor(11/2)=50, greater than42.
Therefore a putative identity (1) MUST have largest nonzero r=10.

Multiply it by z^45, since lambda_10=45:

    T10 + sum_(r<=9) z^(45-lambda_r) T_r
       = c*z^3*A(q,z)^2.                            (10)

The left side has z8 coefficient ZERO: degree_z T10<=5, while EVERY lower
block starts at degree at least45-lambda_9=9. The right side's z8
coefficient is c*[z5]A^2, NONZERO by (8). Contradiction.

Equality on an actual open two-dimensional strict source set implies
rational identity, which justifies all coefficient comparisons. The formal
points q=0 or z=0, including negative v in the latter coordinate chart,
are NOT admitted physical tuples. No boundary source is used as a witness.
The proof needs the independent q,v variables, so it does not silently
extend this mixed-block conclusion to the fair line alone.

## 6. Changed frontier, self-review and original acceptance

The raw and one-ordinary-Q-block predecessor remains PROVED. Its explicit
mixed-block loophole is now closed on open two-parameter source domains,
including fixed reference eigenframe combinations, at EVERY finite cap.
No higher-cap mixed linear square factory is warranted for identity (1).
The same conclusion holds for (J/15)^2 after rescaling c.

Self-review checked: chronological row orientation of the projector support;
CURRENT-root rather than old-leaf coin degree; ordered-arm reversal exactly
once; all-coin q4 coefficients; absence of q5; deterministic-arm v factor;
the exact pole42 and only possible r10; the nonzero z8 coefficient; and
the distinction between a two-dimensional open set and a fair interval.

It remains valid to square a supplied probability by NONLINEAR arithmetic.
This theorem does not identify or exclude a nonlinear whole-word observable,
source-dependent coefficients with a genuine composition law, inequalities
with extra costs, an identity only on a constrained return fibre, independent
operator tensor copies, or a joint cross-cell transport mechanism. An
arbitrary fixed reference basis is covered; a source-dependent basis change
without its retained derivative/composition law is not admitted as L.

No full-endpoint non-descent, positive word factorization, action upper,
variance/index estimate, ONE-witness bound or all-input terminating NO has
been acquired. Original G3 remains ACTIVE. Completed hand suppliers remain
PROVED, with independent review, Lean, source execution, publication and
recipient reading/adoption separate. No new original observation, clock,
fresh-position tie, COMMON refresh or smaller completion standard is added.

One existing next action is the genuinely JOINT nonlinear source/word
implication, using completed suppliers and this exact excluded receiver
class, or a superseding source-complete result after predecessor/successor
comparison. All owners, no-local-Git/no-worker rules, pending hold-scope
clarification, native controller UNBOUND and held/USED/UNKNOWN history stay.
