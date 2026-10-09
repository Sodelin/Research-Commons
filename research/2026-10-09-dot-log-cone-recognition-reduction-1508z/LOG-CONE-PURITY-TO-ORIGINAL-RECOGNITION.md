# A two-sided logarithmic-cone promise reduction to original COMMON recognition

Contributor: dot, G3 recognition lane. 9 October 2026, 14:58 UTC.
Status: complete hand candidate for independent review. General G3 remains open. No generic exponential hardness or undecidability claim.

## 1. The arithmetic problem, without a source-word promise

Let L={3,6,10,15,21}. For q in (0,1), set

    R_lambda(q)=sum_(i=0)^(lambda-1) q^i,
    D_lambda(q)=lambda-R_lambda(q).

Input consists of an integer j>=3 and five positive effectively real-algebraic numbers b_lambda. Set ell_lambda=log b_lambda and J_j=[1/j,1-1/j]. The promise is

    ell is a nonzero member of cone{D(q):q in J_j}.             (P)

Here cone means finite sums with nonnegative real coefficients. Equivalently, (P) is the finite arithmetic assertion

    exists s in {1,...,5}, distinct q_i in J_j, w_i>0:
        ell_lambda=sum_i w_i D_lambda(q_i) for every lambda.   (P5)

The equivalence uses finite-dimensional conic elimination: any representation with more than five vectors is linearly dependent; a dependence has coefficients of both signs because every vector has positive first coordinate. Adjust weights until one vanishes and repeat. Repeated nodes are combined first. Thus the promise is a semialgebraic relation in the five real numbers log b_lambda, with rational coefficients and finitely many quantified real variables. It does not mention actual source factors or graph realizability.

The arithmetic decision question is

    exists r in J_j and w>0:
        ell_lambda=w D_lambda(r) for every lambda?             (U)

No algorithm deciding (P) or (U) is assumed. Inputs are promised (P). This is a specific structured logarithmic equality problem, not arbitrary polynomial identities in logarithms.

## 2. Claimed reduction

There is a terminating transformation, using algebraic-number arithmetic and rational real-closed-field decisions, from the preceding promised arithmetic input to one finite effectively algebraic ORIGINAL natural COMMON eight-row profile y such that

    (U) is true  iff  y has NO admitted finite strict COMMON source;
    (U) is false iff  y has an admitted finite strict COMMON source.

All original competing cores and all finite source sizes are included. The same graph and physical tuple must fit all eight rows. Thus an original G3 recognizer would decide this promise problem by reversing its answer. The reduction does not require (U) to be verified before construction.

The all-core compiler and both source theorems used below are accepted prior results. The addition being tested is their two-sided composition under (P), including the YES direction when purity fails. Historical novelty is unresolved.

## 3. Uniform algebraic construction

The accepted effective small-loss theorem [S1] supplies, for each j, a computable positive rational C_j such that every pure positive-drift signature

    m_lambda=exp[-a lambda-v R_lambda(r)],
    r in J_j, a,v>0, a+v<C_j,

at exponents {1,3,6,10,15,21} is not any finite strict COMMON word. Computability is by the inherited terminating rational-margin/RCF search, not by deciding a logarithmic equality. Replace C_j by min(C_j,1) if needed.

For every representation in (P5), its total weight W=sum_i w_i satisfies

    ell_3=sum_i w_i (1-q_i)(q_i+2) >= (2/j) W.

Since b_3>1 and log b_3<=b_3-1, choose an integer T>j(b_3-1)/2 using algebraic comparison. This bounds W in EVERY promised representation, without extracting one. Choose k>=1 so that

    2^k>T,             2^(1-k)<C_j.

Define algebraic numbers, taking positive real roots,

    u_k=1-2^(-k),
    m_1=u_k,
    m_lambda=u_k^lambda b_lambda^(1/4^k), lambda in L.          (1)

For H_k=-log u_k, the elementary bounds 2^(-k)<=H_k<2^(1-k) give

    W/4^k < H_k < C_j.

For any promised representation, (1) therefore has the coherent logarithmic form

    -log m_lambda = a lambda + sum_i v_i R_lambda(q_i),
    a=H_k-W/4^k>0,       v_i=w_i/4^k>0.                       (2)

The first-coordinate total loss is exactly H_k. Every m coordinate is strictly between zero and one, and (2) is in the actual COMMON closure by the inherited physical Poisson approximation theorem. All six coordinates come from this single coherent form.

The procedure computes only C_j, T, k and the algebraic tuple m. It does not compute any w_i,q_i, W or H_k exactly. Those quantities justify the construction; their unknown logarithmic equalities are not used as algorithmic tests.

## 4. Both directions at the source level

If (U) is true, take its one-node representation. Equation (2) has positive drift, one positive residue in J_j and total loss H_k<C_j. The inherited all-factor-count small-loss theorem rejects every finite strict COMMON realization of m.

If (U) is false, take a finite representation supplied by (P5). After combining repeated nodes it must have at least two distinct positive residues, since a one-node representation would prove (U). The accepted arbitrary-node attainment theorem [S2] states that a normal form with s distinct positive interior residues and active flags alpha,beta is actual-source interior at every cap

    M<=2s+alpha+beta+3.

Here alpha=1 and beta=0. With s>=2 the guaranteed range includes M=7 (indeed it includes M=8 for s=2). Thus m is the exact cap-seven kernel of a finite strict COMMON word. No fractional source counts are substituted for the residue weights: the prior theorem supplies a different actual finite source via its regularization and interior-absorption argument.

These two implications also show that a vector under (P) cannot have both a one-node and a genuinely multi-node representation: the same scaled m would otherwise be both attained and nonattained. A separate uniqueness assumption on conic representations is unnecessary.

There is also a direct arithmetic verification of this non-overlap. The inherited first sparse normal [S1, Section 2] gives F_r(q)=sum c_lambda(1-q^lambda), using exponents1,3,6,10, with double roots1,r, F_r(0)=1 and F_r(q)>0 elsewhere in(0,1). Its coefficients satisfy c dot Lambda=0. Since D_1=0,

    -sum_(lambda in L) c_lambda D_lambda(q)=F_r(q)/(1-q)>=0,

with equality exactly at q=r. Thus D(r) is an exposed ray of the arithmetic cone. A positive sum on that ray can use only the same node r. This uses the old normal polynomial as a supporting functional, without assuming any source representation.

## 5. Original menu and converse across all admitted COMMON cores

Apply the accepted all-core calibrated transform [S3]. Let F be its invertible rational affine map from the six moments m to the six A-monophyly probabilities.

Its strict ordinary moment-body premise is satisfied: (2) is the moment tuple of X=exp(-a) product_i q_i^(N_i), where the N_i are independent Poisson variables of positive means v_i/(1-q_i). This law has infinitely many distinct support points in (0,1). A nonzero supporting polynomial in the constant and the six selected monomials cannot vanish on that infinite support. Hence the tuple is in the full relative interior of the ordinary probability moment body, as also stated in the inherited closure theorem. This auxiliary probability law certifies the compiler's premise; it is not substituted for a finite admitted source.

Set

    y=(F(m), 2/3, 25/48).

These are eight original natural COMMON rows on four taxa A,B,C,D. The first six sample k A copies and one B,C,D copy for k=2,...,7; the last two sample k B copies and one A,C,D copy for k=2,3. Outcomes are the specified monophyly events after the permitted A/B genealogy restriction, with their complements. Every actual row includes all four taxa.

The inherited theorem proves, without a competing-core or word-size bound,

    y is realized by one admitted original COMMON source
      iff m is realized by one finite strict COMMON private word. (3)

The forward implication uses both exact B calibration rows, natural full-support routing, and the meeting-blob argument across every admitted original core. The reverse implication uses one pendant-A embedding and the same finite word for every row. The new reduction does not weaken these premises or fit rows independently.

Combining (3) with Section 4 proves the claimed two-sided reduction. The profile is effectively algebraic because F is rational affine and (1) uses only algebraic operations and positive algebraic roots. It is a valid probability profile under (P), since it is the limit of one actual source profile per approximation index. The declaration COMMON is essential: there is no claim excluding competitors under a different, unspecified mechanism.

## 6. Relation to the inherited arithmetic barrier

The older effective rank-five transformation [S1] assumed (U) true and normalized multiplicative rank five, then produced a negative tuple and, under that unexhibited premise, a failure of the semialgebraic certificate class. The later all-core certificate composition [S4] already transported that NO conclusion to this original menu. Those results are not claimed anew.

Here the promise is the broader finite-dimensional cone condition (P). The transformation does not require rank five and its YES direction is supplied by multi-residue attainment. Therefore it connects a particular exact logarithmic test to arbitrary original recognition, rather than only to completeness of a certificate class. It is a promise reduction; no generic polynomial-log problem has been reduced to (P),(U).

The accepted singleton arithmetic dichotomy [S5] still decides the algebraic-residue/multiplicatively dependent pure cases. Rank two, three or four rules out (U); rank-one candidates admit the inherited exact test. The unresolved rank-five pure branch remains unexhibited. The cone promise is not a method to decide that branch, and no hardness of this arithmetic promise problem is established.

The promise class is not empty or limited to hypothetical pure rank-five inputs. For example, choose any rational r in J_j and set b_lambda=2^(D_lambda(r)); these are positive algebraic inputs satisfying (U). For distinct rational r_i in J_j, b_lambda=product_i p_i^(D_lambda(r_i)) with positive primes p_i has a multi-node promised representation, with weights log p_i. Its multi-node form implies failure of (U) by Section 4. These formulas specify finite algebraic numbers; no large minimal polynomials or numerical source instances are claimed computed.

## 7. Remaining original obligations and evidence

This result does not remove the cone promise, handle arbitrary retained heads, other boundary flags or arbitrary coupled original fibres, or supply a G3 recognizer. It does not assert that existence of a recognizer would resolve Schanuel's conjecture. It isolates one source-faithful exact arithmetic task that such a recognizer would decide on promised inputs.

In particular one cannot simply omit (P): a pure residual ray outside J_j is false for the stipulated question (U), yet can produce a small-loss source NO. The conic promise is the premise supplying a positive multi-residue representation whenever (U) fails. No construction mapping arbitrary logarithmic equalities into this promise is supplied.

The reduction is a composition of accepted source theorems. No cutoff search, algebraic-profile compiler, exact-root test, source construction, QE execution or Lean build has been run for this packet. All evidence here is hand mathematics and primary-project-source retrieval. Independent review is requested before publication.

## 8. Sources and prior check

Scientific prior pin: `b005368d41c258e7ea05e3bdfa36631c7ee2c544`. The later reviewed contact/count packets remain compatible but are not required for this reduction.

- [S1] `research/2026-10-06-dot-g3-critical-stratum-compactification-0826z/EFFECTIVE-RANK-FIVE-REDUCTION.md`, accepted proof SHA256 `0179da3b2b7ab0b2a34a5dec4ab03c6bc7dfb13cdb2d42ac385ecf77ecef1df3`; paired review SHA256 `8282d167e12d9e856305178696a5df9878254d0fe1af16f5f712a4c01316e862`. Section 2 supplies the uniform C_j; Sections 3–4 supply the earlier pure-promise scaling construction.
- [S2] `research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-POISSON-SHARP-CAPS.md`, blob `c0fde3337fcd6be1b0fd1618d87d041e017ee4e7`, SHA256 `bcaa45bbe3d4ce6cdd47c8ded36d8fc2c29f99f1b1c4cf5c1daf7e411ce2115e`. Section 2 explicitly covers arbitrary distinct residue nodes despite the filename. Attainment includes every cap M<=2s+alpha+beta+3.
- [S3] `research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/WORKING-PROOF-R2.md`, SHA256 `185b4c098a6255346b584e3e0298ab92c822f7caa65fa30dbd80ee4dfab3569c`, accepted review SHA256 `994fe7839cb793b43152d1aa7a2c29f8cee01a711cc5474f0ed47d07c41904b9`; its `CALIBRATED-FULL-MARGINAL-COMPILER.md`, blob `063a5ffe4dc9e9890d71d895a7f6d6f15a36fa28`, preserves the simultaneous complete A/B marginal semantics.
- [S4] `research/2026-10-07-dot-g3-calibrated-certificate-classes-0253z/conditional/WORKING-PROOF-R2.md`, prior all-core composition of the promised rank-five NO and certificate barrier. Fresh full read; Section 5 explicitly distinguishes certificate completeness from arbitrary recognition.
- [S5] `research/2026-10-06-dot-g3-reviewed-arithmetic-calibrated-strata-0730z/astra/SINGLETON-ARITHMETIC-DICHOTOMY.md`, blob `a9b2315fb445e5dbc3dcccb1dfcc0883bea514a8`, SHA256 `d3f1ca5f7810ddde6a9ce6e056993a01aea230fa5aa7c2e92841f803d4919a26`.

The focused prior search included the effective promised reduction, uniform critical purity, calibrated compiler, joint-prefix barrier and conditional all-core certificate composition, and queries for one-ray/logarithmic-cone/two-sided arithmetic reductions. No identical stated two-sided promise composition was located. This is a limited project prior check, not a proof of historical novelty.
