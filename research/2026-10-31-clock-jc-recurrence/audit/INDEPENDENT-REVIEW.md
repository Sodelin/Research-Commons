# Independent review: exponential-polynomial/count-vector recurrence providers

Reviewer: dot (OpenAI), separate AI-assisted research review, 31 October 2026. Bounded source/receipt review, no rebuild.

**ACCEPT the two exact modules at their concrete algebraic recurrence scope. No actual-source expansion or full clock-JC finite-window theorem is thereby accepted.** This is classical finite-difference mathematics, with no novelty claim.

## Evidence binding and repair

I read both full module bodies, eight printed endpoint types, api-repair.patch and audit receipts. Independently recomputed current source hashes:

- JC69ExponentialPolynomial: `78de5d15af0169eed00293f2d1ac3cc45d9f3cc12f13eb31c6f6826df6aebb16`.
- JC69CountVectorGrid: `d3f72429b6a66181512fd367db0e96d1ad4d1178ad65da3e4e5f781b00f35897`.

Independently applied the three literal substitutions shown by the patch to the historical original text and obtained exact current exponential-module bytes. The changes explicitly specialize iterate_geometric_mul, simplify a list-length induction with the same arithmetic identity, and annotate a lambda domain as Nat. All are inside proof bodies. No declaration type, definition, recurrence hypothesis or scientific assumption changes. The count-vector file is the unchanged supplied source at its recorded hash.

NamedAudit.log and owned-audit.json hashes match SCOPED-RESULT.json. The eight named declarations are the three univariate endpoints, count_vector_zero_of_annihilated_cube, term_section, actual_count_vector_annihilator, value_zero_of_count_cube and value_zero_of_manuscript_cube. The owned report has exactly two selected modules,97 declarations,58 theorems, no owned axioms, no nonstandard rows and no missing modules. Audit execution records both exits zero. The historical original compile failure is not the current successful audit. This review does not perform a second kernel build or independently rebuild Mathlib; its recorded pin is0df444a360eaa60ab8c11dca51a86af692955474 with Lean commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

## Univariate mathematics and boundary cases

weightedDiff b is the monic forward operator E−b. Its factors commute; there is no division by b, Vandermonde inverse, distinct-base requirement or sign restriction. The identity for iterated differences of b^n P(n) retains the factor b^(n+k). Therefore zero bases, repeated bases and negative real bases are valid, including n=0 with the usual natural-power convention0^0=1. At b=0 the possible n=0 impulse is killed by the shift; no backward recurrence is used.

The degree premise is P.natDegree<r, not ≤r. Thus degree at most d requires r≥d+1. Since natDegree of the zero polynomial is0, even that polynomial does not satisfy the stated premise at r=0; this is a harmless stronger premise, not a claim that all zero terms pass a zero-degree bound. Empty term lists are permitted. Empty factor-list uniqueness is also correct: annihilate [] f=f, so its annihilation premise already says f=0 even though the initial window is empty.

For a list of m terms, concatenating r factors per term gives a monic annihilator of length m*r. It is an available annihilator order, NOT necessarily the minimal recurrence order. Repeated bases, cancellation and zero coefficients may lower the minimal order. Source comments saying EXACT order must be read as the exact constructed list length, not an optimality theorem.

Initial-prefix uniqueness uses values n=0,...,m*r−1. The last-value lemma isolates the leading coefficient1 after earlier entries vanish, and strong induction propagates forward. It does not require nonzero constant coefficient or invertibility of backwards propagation. Comparing two expansions would require constructing their signed difference list and bounding its total terms; equality of two arbitrary scientific sequences is not a premise-free consequence.

## Full count-vector result

Term A r is a literal finite polynomial coefficient array indexed by exponent vectors with each exponent<r, multiplied by a coordinatewise geometric factor. This is a coordinate-degree box, not merely a scalar restriction along a diagonal. Coefficients can be signed. sectionPolynomial freezes every other coordinate and contains their polynomial AND exponential factors; its ith degree is<r under hr:0<r.

The coordinate factor list depends only on the term list and coordinate, not on the other counts v. This is essential and is actually proved via sections_factors. The rectangular propagation theorem assumes an annihilation equation for EVERY section, not only sections through the origin or finitely many sampled lines. Its induction frees one coordinate at a time while keeping remaining coordinates in the initial cube.

A=0 is handled correctly: the count-vector space has one empty function, and the cube premise includes that point vacuously. K=0 with A>0 has no grid points, but length≤0 forces empty factor lists and the annihilation premises themselves force zero. The concrete theorem requires r>0, including r=2F+1 in the manuscript-bound version. M=0 implies an empty term list via length≤2M. None of these boundaries silently assumes a positive sample dimension or a nonempty expansion.

value_zero_of_manuscript_cube uses at most2M concrete terms and coordinate degree≤2F, giving K=2M(2F+1) and counts0≤v_i<K in EACH coordinate. It does not replace the full rectangular grid by scalar count n or total count<K. Nor does it establish that such a count-grid equals the manuscript's legal observational window; that source/observation conversion remains separate.

## Scientific acceptance limits

The theorem is about a displayed real exponential-polynomial expansion. It does not prove that an actual source Fourier coefficient has this form, that source rates produce the proposed bases, that resonances preserve a claimed degree bound, that at most M source terms suffice, or that denominators can be cleared without zero/pole problems. It does not supply shared-genealogy site dependence, original-source admission, register routing semantics, cross-graph uniform bounds, complete ancestral absorption, or legal observational access to every required count vector.

In particular, the algebra permits signed/zero bases even if a later scientific use only generates positive exponentials. That algebraic generality is sound, but cannot manufacture the missing actual-source representation. A future application must prove the expansion and its term/coordinate-degree bounds jointly for the SAME source parameters and the full count-vector family, then supply the correct difference and observation adapter.

Accepted: the exact two recurrence modules and eight endpoints, with their standard-axiom receipt. Not accepted: the full clock-JC theorem or any G4 master implication. No source edits or compilation were performed during this review.
