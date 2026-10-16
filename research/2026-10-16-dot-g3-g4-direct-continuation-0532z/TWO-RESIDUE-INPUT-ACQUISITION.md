# Finite input-only acquisition for the two-residue small-loss templates

Contributor: dot, 16 October 2026. Status: proposed hand adapter, dependent on the accompanying two-residue coverage proof. No solver run, cutoff computation, whole G3 decision, or independent novelty claim.

## Endpoint

For twelve positive effectively real-algebraic coordinates m_lambda in (0,1), Lambda=(1,3,6,10,15,21,28,36,45,55,66,78), there is a terminating finite-template procedure returning either an exact ordinary-versus-impossible certificate for strict COMMON private chains or TEMPLATE_UNAVAILABLE. No residue nodes, cutoff, factor count, or Poisson decomposition are supplied. The procedure acquires its own nodes and inequalities. On the accepted calibrated fourteen-row original COMMON menu the same certificate excludes every original rival through the inherited simultaneous compiler. Additional retained observation channels cannot be discarded.

The procedure is complete for its explicit finite certificate predicate. In particular, for every fixed pair of algebraic nodes 0<v<u<1 it covers all sufficiently small-loss algebraic observations of the positive-drift, two-positive-residue form in the accompanying theorem. It does not claim a single cutoff uniform over those nodes or complete recognition outside these templates.

## 1. Reused arithmetic and four-normal adapter

Compute the integer multiplicative-relation lattice L(m) of the twelve positive algebraic numbers. This is established effective algebraic-number theory. Require every certificate normal row to belong to span_R L(m). Such a row annihilates h=-log m exactly. Baker's algebraic-linear independence theorem ensures that every algebraic row annihilating h lies in the algebraic span of L(m). Thus no arbitrary polynomial-logarithm zero test is introduced.

CUBE-CONTACT-INPUT-ACQUISITION describes the complete RCF margin predicate for the {r,r^3} four-normal template. Reuse it for that contact case. For the {r^2,r^3} case substitute the root sets and local order table of TWO-RESIDUE-SMALL-LOSS-COVERAGE. The same four inequalities and explicit cutoff constraints are valid because its last budget is stronger. All exponents remain fixed natural integers, all normal rows have twelve entries, and all quantified variable lists are finite. The unchanged four-normal cutoff constraints, with K=H^2, are

0<C<=1, 2C<=(1-Q)p0, 1576 C H^18<=1-Q, 2(1-m_1)<C.

The resulting finite disjunction searches both contacts without being given r.

## 2. The cube-separated predicate

Add a third branch with variables 0<v<u<1 and

Q0={u,v}, T={u,v,u^2,v^2}, u^3,v^3 outside T.

Split this branch into v=u^2 and v!=u^2. These are the only possible collisions among the four listed elements. Accordingly T has three or four distinct elements. This finite split prevents duplicated neighborhoods from being counted as distinct physical factors.

Construct F0 from the first six exponents with double roots at 1,u,v and F0(0)=1. Construct F1 from the first 2|T|+2 exponents with double roots at 1 and every point of T, F1(0)=1. Zero-pad to twelve coordinates. Impose that both rows lie in span_R L(m). The accepted sparse Descartes argument proves positivity off the prescribed roots and exact double multiplicities. All equations are polynomial in u,v and row coefficients.

Choose pairwise disjoint intervals around the distinct elements of T, an endpoint Q<1 above them, and a common small-p bound p0. The same rational second-derivative endpoint inequality used in the effective four-normal proof certifies positivity near q=1 for every strict p. Finite polynomial quotient bounds at the double roots and compact-complement bounds certify:

- near either original node, L1>=p^3/H and L0>=-H p^2;
- near any auxiliary node in T minus Q0, L0>=p/H and L1>=-H p^2;
- outside these intervals, L0 is positive and L1 nonnegative.

Here H>=1 is a quantified bound. At an original node F1(q)=F1(q^2)=0 and F1(q^3)>0, so the first retained order is +3. At an auxiliary node the generic lower bound -H p^2 follows from F1>=0 and the absolutely convergent series remainder; it does not require its square to be absent from T. The retained drift is annihilated by both rows. All estimates are verified by the same finite rational/polynomial denominator-clearing and geometric-tail inequalities as the effective-cutoff supplier. None asks a solver to reason about a logarithm.

For exactness of the finite predicate, one may use the explicit bounds of the existing input-acquisition note with k=3 at original nodes. At auxiliary nodes use the even-order bound H>=8B, since for z<=1/2 the terms of order at least two have absolute sum at most 2Bz^2<=8Bp^2. The positive nonroot bounds are H delta>=2. Compact complements are subsets of [0,Q], so they exclude the endpoint root at 1.

If U_j=sum p_i^j over the two original neighborhoods and P is the sum p_i over all auxiliary neighborhoods, the two zero equations give

P<=H^2 U_2, U_3<=H^2 P^2.

Writing K=H^2 and W=U_1+P, finite-sum Cauchy gives U_2^2<=U_1 U_3<=W U_3. Hence

U_3<=K^3 W U_3.

Choose C with

0<C<=1, 2C<=(1-Q)p0, 4 C H^6<=1-Q, 2(1-m_1)<C.

Then h_1=-log m_1<C and W<=h_1/(1-Q)<1/(4K^3), so U_3=0. The first budget gives P=0; strict positivity of L0 elsewhere removes every other factor. The observed signature is necessarily ordinary. This proof is the already accepted two-normal budget, now encoded as a finite acquisition branch.

## 3. Decision, completeness, and exact boundary

Take the disjunction of the two cube-separated collision subcases and the two contact templates. Decide this single finite real-closed-field formula over the input's real-algebraic coefficient field. If satisfiable, sample algebraic witnesses and verify the inequalities. All coefficient rows annihilate the actual logarithmic observations by their lattice-span constraints. The respective budget proof forces every strict Bernoulli factor to disappear in any realization. Source membership on this branch is therefore exactly

m_lambda=m_1^lambda for every supplied coordinate.

Those are algebraic equality tests, and m_1 in (0,1) supplies a strict ordinary witness when they hold. A failed equality proves absence of every finite strict private-chain realization. If the disjunction is false, return TEMPLATE_UNAVAILABLE with no membership inference.

For a fixed algebraic residue pair, the two-residue theorem supplies the appropriate normal rows and positive local/endpoint margins. All rows are algebraic. If the observed tuple is algebraic and has that representation, Baker places these rows in the computed lattice span. Rational margin choices exist by strictness, and sufficiently small first-coordinate loss satisfies the final gate. This proves the advertised fixed-pair coverage without a supplied node. It does not prove coverage for a representation with transcendental nodes, even when its evaluated observations are algebraic.

The relation lattice depends on the exact input. This is not one fixed semialgebraic subset of the raw observation coordinates and does not contradict previous fixed-classifier obstructions. It also cannot strip a supplied retained head: the established interior absorption int(S)+closure(S) subset int(S) shows that an interior finite head can turn a nonattained closure tail into an attained total signature. The normal equations must apply to the complete observed signature.

## Sources and status

- TWO-RESIDUE-SMALL-LOSS-COVERAGE.md in this packet: candidate coverage proof, including the exhaustive contact classification and the new {r^2,r^3} table.
- CUBE-CONTACT-INPUT-ACQUISITION.md in this packet: complete classical arithmetic and four-normal finite RCF adapter; still a hand candidate.
- [Accepted squared-node theorem, Section 8](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-POISSON-SHARP-CAPS.md).
- [Effective four-normal cutoff](https://github.com/Sodelin/Research-Commons/blob/dd02cfb5067a3b9e7d7d445a886bec4d6224ee96/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/CUBE-CONTACT-EFFECTIVE-CUTOFF.md).
- [Original calibrated COMMON transfer](https://github.com/Sodelin/Research-Commons/blob/c708447f4b64b318b49460b682cc5ab771b9494d/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/CUBE-CONTACT-ORIGINAL-COMMON-BRANCH.md).
- Sertoz, Ouaknine, Worrell, [Computing transcendence and linear relations of 1-periods](https://people.mpi-sws.org/~joel/publications/1-periods25.pdf), author-hosted version, Lemma 8.8.61, supplies effective multiplicative-relation background. Classical linear logarithm arithmetic is reused, not claimed as a new theorem.

General G3 OPEN. General G4 OPEN. Finite retained multiplicity, arbitrary-loss singular attainment, and complete original-source acquisition remain unresolved. No solver or certificate extraction was executed for this note.
