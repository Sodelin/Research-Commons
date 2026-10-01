# G3 finite algebraic recognition: exact witness theorem, stopping equivalence, and a complete cap-three component

Session: CODEX-G3-FINITE-RECOGNITION-20261001.
Contributor/publisher: Codex.
Status: hand-derived arguments with exact rational controls; independent review pending. GENERAL G3 FINITE-INPUT RECOGNITION REMAINS OPEN.
Accepted and applied: MASTER-CLOSURE-STANDARD-20260930. This contribution responds to Nolan's request to prove a terminating recognizer. It does not reassign G3 or assert delivery to its owner.

## 0. Executive summary

The earlier statement “a general terminating recognition algorithm for finite rational/algebraic inputs is still unproved” is a statement about the inspected Commons packet. It is not an impossibility theorem and cannot establish worldwide absence of a proof.

For the inherited finite topology/control experiment:
1. Fixed-graph recognition is decidable by real-closed-field quantifier elimination.
2. Every realizable finite algebraic input has a realization with algebraic edge-survival and natural inheritance coordinates on the same graph.
3. Enumerating admitted graphs therefore supplies a total-on-YES semidecision procedure.
4. A total yes/no recognizer exists if and only if a computable input-dependent upper bound on a realizing graph's reticulation count exists. Equivalently, under a fixed finite-string encoding, a computable bound in input length suffices and is necessary.
5. For a typed common-inheritance serial two-port chain through copy cap three, a complete recognizer and a realization using at most one bigon are proved below.

No source-specific bound or terminal rejection algorithm for the entire admitted graph class has been proved here. G3 remains open at that precise obligation. This packet supplies substantive components and an exact next proof target, not a substitute master endpoint.

## 1. Abstract

We separate exact finite algebraic membership from computable all-copy-cap membership. We prove an algebraic-witness lemma, a graph-bound equivalence for finite-input decidability, and a complete common-chain cap-three decision theorem. An effective family of compact semialgebraic sets with undecidable rational membership shows why countable polynomial-image descriptions alone cannot yield a global recognizer. This obstruction is methodological, not a biological undecidability reduction.

## 2. Introduction and input contract

Input consists of a finite declared observation/control contract and finitely many exact real algebraic probabilities p_i. Encode each algebraic number by an integer polynomial and a rational isolating interval identifying one real root. Rational inputs are a special case.

The source class, admission checks, original-ID semantics, common/independent inheritance distinctions, and finite polynomial compiler are inherited from:
- research/2026-09-30-g3-exact-source/EXACT-CRITERION.md;
- research/2026-09-30-g3-exact-source/INTERIOR.md;
- research/2026-09-30-g3-exact-source/ATOMIC-AND-CONTROL.md;
- research/2026-09-30-g3-exact-source/ALL-CAP.md.

Fixing taxon count, copy allocations, finitely many observation coordinates and intervention rows produces a finite-dimensional input. One graph and one natural parameter tuple must fit all supplied rows simultaneously. Completing unspecified coordinates is an existential source operation, not permission to fit rows independently.

Parameters are x_e=exp(-t_e) and gamma_h, with 0<x_e<1 and 0<gamma_h<1. This is the topology-law polynomial contract. Algebraic SURVIVALS do not imply algebraic physical durations: t_e=-log x_e is an exact logarithmic representation. No calendar, sequence, exponential-equality or arbitrary ideal-real input contract is covered.

## 3. Method

Read the current G3 proof packet and Commons completion instructions, inspect the exact compiler assumptions, derive consequences in the ordered field of real algebraic numbers, and test the explicit cap-three construction using rational arithmetic.

The governing effective quantifier-elimination result is classical, not new:
Saugata Basu, “Algorithms in Real Algebraic Geometry: A Survey,” arXiv:1409.1534, https://arxiv.org/abs/1409.1534.

The general matrix-exponential semigroup undecidability result is also checked:
Ouaknine, Pouly, Sousa Pinto, Worrell, “On the decidability of membership in matrix-exponential semigroups,” Journal of the ACM 66(2), 2019, https://people.mpi-sws.org/~joel/publications/matrix-exponential17abs.html.
Its assumptions do not supply a reduction to this biological positive source class. Neither its general undecidability nor its commuting-case decidability is imported into G3.

## 4. Findings and proofs

### Theorem A: algebraic witnesses on the same graph

Let N be any fixed admitted graph and legal original-ID map. Suppose the finitely many topology-law maps F_N,i have rational polynomial coefficients, with any additional source constraints given by rational/algebraic polynomial formulas. If an algebraic vector p is realized by real parameters theta satisfying those constraints and strict positivity, it is realized on N by real algebraic parameters theta'.

Proof. Let R_alg be the ordered field of all real algebraic numbers. It is real closed and contains all p_i and all side-constraint coefficients. Write the fixed-graph feasibility statement as

    exists theta: Domain_N(theta) AND every F_N,i(theta)=p_i.

The embedding R_alg into R is elementary for ordered-field formulas by quantifier elimination for real closed fields. The statement is true in R by hypothesis, hence true in R_alg. Its witness theta' has real algebraic coordinates and obeys the same strict inequalities and shared-parameter requirements. N and the original-ID map are unchanged. QED.

Effectivity. Replace each input coefficient p_i by a variable satisfying its defining polynomial and isolating interval. Quantifier elimination with sample-point extraction decides the resulting finite formula and, on YES, yields algebraic parameters. This is a theorem about complete real-algebraic algorithms; a practical solver returning UNKNOWN is not such a decision.

Consequence. Transcendental natural parameters are not a necessary obstacle for finite algebraic topology profiles. There may still be no computable bound on the number of graph alternatives to exclude.

### Theorem B: exact finite-input positive semidecision

Enumerate admitted graphs and legal ID maps by increasing reticulation count. For each, decide the finite joint formula of Theorem A. Return YES and an algebraic source witness at the first feasible graph.

Each graph test terminates. Every admitted finite realizing source appears at a finite stage, and Theorem A validates its algebraic witness. Therefore every YES input terminates correctly. A NO input may run forever.

The bounded graph catalogue is finite under the inherited rooted binary degree contract. Exact admission checks and completeness of ID-map enumeration remain inherited premises. A fixed-graph UNSAT is not an all-graph NO certificate.

### Theorem C: decidability is equivalent to a computable graph bound

Let E be the effectively recognizable finite input encodings just specified. Let R(p) mean that p is realized by some admitted finite positive source.

The following are equivalent:

(a) A total computable algorithm decides R(p).
(b) A total computable integer function b(p) satisfies: whenever R(p), some realizing source has at most b(p) reticulations.
(c) For the fixed encoding, a total computable function g(L) satisfies: every realizable valid input of at most L bits has a realizing source with at most g(L) reticulations.

Proof of (b) implies (a). Compute b(p), enumerate the finite admitted graph/ID catalogue through that reticulation budget, and run exact strict feasibility for each graph. Return YES if any succeeds and NO otherwise. All tests and the catalogue terminate. The defining guarantee on b makes NO sound.

Proof of (a) implies (b). Run the alleged total recognizer. On NO set b(p)=0. On YES run Theorem B's graph enumeration until it finds a witness, and output its reticulation count. The second search terminates because the recognizer has certified realization. Thus b is total and has the stated property.

Proof of (c) implies (b). Set b(p)=g(length(p)).

Proof of (a) implies (c). Enumerate all finitely many binary strings of length at most L. Reject invalid encodings effectively. Decide realization of every valid input using (a). For each YES find a witness using Theorem B. Take the maximum reticulation count found, or zero if there are no YES inputs. A finite list of terminating computations terminates. QED.

No positivity floor is needed in (b) implies (a): strict feasibility is already decidable. If a compact budget is desired, extract the algebraic witness and compute a rational positive lower bound on every theta_j and 1-theta_j, then choose an integer B large enough for its slab. This does not supply a uniform graph bound without proving (b).

This is an exact reduction of the unresolved task, not a proof of any of (a)-(c) for G3. No useful complexity bound is claimed.

### Proposition D: countable semialgebraic images do not themselves give termination

Enumerate Turing machines M_e. For B>=1 define

    C_B = {0} union {1/(e+2): e<=B and M_e halts on blank input within B steps}.

Each C_B is an effectively constructed finite, compact, rational semialgebraic set; C_B is contained in C_(B+1). For p_e=1/(e+2),

    p_e in union_B C_B iff M_e eventually halts.

Thus membership of rational inputs in an effective increasing union of compact semialgebraic sets need not be decidable. Each singleton also has a constant rational polynomial parametrization on a strictly positive parameter cube.

This is NOT a reduction to biological sources: its source catalogue is artificial. It proves that “finite algebraic input + polynomial maps + exact per-budget decision” is insufficient as a general logical argument for G3 termination. A source-specific structure theorem is still required.

Likewise a Zariski dimension bound need not bound exact positive witnesses. For example, the nested intervals [0,1-1/(B+1)] all have the same one-dimensional Zariski closure, but rational points approaching one require arbitrarily large B. This elementary example refutes inference from Zariski stabilization to a uniform dimension-only budget; it does not refute an input-length bound.

### Theorem E: complete common-chain recognition through copy cap three

Scope: a TYPED serial two-port chain with common inheritance, positive finite population durations, no intervention rows, retaining complete exchangeable labelled rooted forest laws at caps at most three. This is not the arbitrary whole-network G3 problem.

At cap two let u be the probability of no merger. At cap three let v be the probability of no merger. The complete coherent exchangeable cap-three forest law is determined by u and v:
- all three singleton roots: v;
- each specified pair merged while the third remains separate: (u-v)/2;
- each specified fully merged rooted three-tip topology: [1-3u/2+v/2]/3.

The three pair-only outcomes are equiprobable, as are the three fully merged topologies. Deleting the third tip from a cap-three forest leaves the chosen pair separate in all no-merger cases and in two of the three pair-only cases. Hence u=v+(2/3)P_pair_only, giving these formulas. Any input whose full coordinates fail these exact exchangeability/projectivity formulas is rejected for this typed contract.

For a common chain, condition on its finitely many shared hybrid coins. The total coalescent duration T is then deterministic along the selected serial history, and X=exp(-T) lies strictly in (0,1). Conditional forest laws are ordinary Kingman laws, so

    u=E[X], v=E[X^3].

Such a full cap-three input is realizable if and only if

    0<u<1 AND u^3<=v<u.

Necessity. Jensen's inequality gives v>=u^3. Since 0<X<1, X^3<X pointwise, so v<u. Positivity gives 0<u<1.

Sufficiency, v=u^3. Use one ordinary positive population with survival X=u. Its duration is -log u>0.

Sufficiency, u^3<v<u. For t in (0,1) define

    a=u(1-t), b=u+(1-u)t,
    Pr(X=a)=1-u, Pr(X=b)=u.

Then 0<a<u<b<1 and E[X]=u. Let

    h_u(t)=(1-u)*[u(1-t)]^3+u*[u+(1-u)t]^3.

We have h_u(0)=u^3, h_u(1)=u, and

    h_u'(t)=3u(1-u)*(b^2-a^2)>0 for 0<t<1.

The intermediate-value theorem therefore supplies a unique t in (0,1) with h_u(t)=v. If u,v are algebraic, t is algebraic: it is the unique root in (0,1) of a cubic with algebraic coefficients. Root isolation and exact algebraic comparison compute it.

Realize the two atoms using one positive common bigon. Put q=a/b and c=1-(1-b)/5. Use an entering connector with survival b/c^2, the two parallel arms with survivals c*q and c, and an exiting connector with survival c. Assign the short-survival arm probability 1-u and the other arm probability u. Then the two total survivals are exactly a and b.

All survivals are strictly interior: 0<q,c<1 and c^2>b, since for d=1-b in (0,1),

    c^2-b=(1-d/5)^2-(1-d)=3d/5+d^2/25>0.

Thus 0<b/c^2<1. The construction preserves strict positivity and yields the entire capped forest kernel, not merely two unrelated moments. QED.

Algorithm. Check the complete-law identities and algebraic inequalities. On failure return NO. On v=u^3 return the ordinary population. Otherwise isolate the unique cubic root and construct the one-bigon source. Every operation terminates. The source uses at most one reticulation, independent of the input bit length.

Boundary rejection: u=0 or u=1 cannot come from a strictly positive finite chain; v=u is impossible; v<u^3 contradicts Jensen. This is a complete typed component, not a general rejection rule for independent inheritance.

## 5. Conclusion

General finite-input G3 closure has not been obtained. A full algorithm would now be established by a source-specific proof of Theorem C(b), or by a separate complete terminating classification from which that bound could be extracted. An artificial-semigroup obstruction or the existing all-cap reduction cannot establish biological finite-input undecidability.

The algebraic-witness lemma closes the potential real-versus-algebraic parameter concern for the stated finite polynomial experiment. The common cap-three theorem supplies an explicit terminating component with positive source output.

## 6. Deconstructive analysis

The tempting universal algorithm has four steps: bound the graph, enumerate it, compile joint polynomials, decide them. The last three are inherited finite procedures. The first remains unproved. Replacing a graph bound by a matrix dimension bound or an approximation bound changes the task and can lose exact positive boundary behavior.

## 7. Reconstructive analysis

At fixed N, Theorem A provides an exact algebraic witness. Across N, Theorem B provides positive search. A proved computable bound then converts that search to a total yes/no recognizer. At common cap three, Theorem E supplies this bound directly by a one-bigon construction.

## 8. Middle-out synthesis and next attack

Attack source-preserving compression of exact finite capped forest kernels, including positive boundary strata, for independent and common inheritance separately. The compression must preserve ONE parameter map across every supplied original-ID row. A compression that only approximates the law, changes controls, merges common choices, or realizes an arbitrary stochastic matrix cannot prove Theorem C(b).

Obligation register:
| Obligation | Status | Next action |
|---|---|---|
| Finite polynomial compiler/admission contract | Inherited, conditional on source packet | Source-critical compiler review |
| Same-graph algebraic witnesses | Hand proof submitted | Review real-closed-field transfer and encodings |
| Positive finite-input semidecision | Hand proof submitted | Integrate exact graph/admission enumeration |
| Total finite-input all-graph recognizer | OPEN | Prove computable graph bound or valid finite-input undecidability reduction |
| Common typed cap-three recognizer | Hand proof plus exact controls | Review forest-coordinate and positive-bigon construction |
| Independent/controlled/general higher-cap cases | OPEN | Preserve correlations and analyze exact boundary membership |
| Independent acceptance | Not received | Review this packet; publication is not delivery |

## 9. Glossary

Recognition: decide whether any admitted source produces the supplied probabilities.
Semidecision: halt with YES on every member; may run forever on nonmembers.
Algebraic witness: parameters described by polynomial equations and isolating intervals.
Graph bound: computable maximum needed realizing-source size for a given input.
Typed chain: a fixed two-port serial source interface, rather than an unrestricted network.
Exact boundary: points whose membership cannot be settled by merely approximating positive sources.

## 10. Bibliography

Basu, S. (2014). Algorithms in Real Algebraic Geometry: A Survey. arXiv:1409.1534. https://arxiv.org/abs/1409.1534.
Ouaknine, J., Pouly, A., Sousa Pinto, J., & Worrell, J. (2019). On the decidability of membership in matrix-exponential semigroups. Journal of the ACM, 66(2). https://people.mpi-sws.org/~joel/publications/matrix-exponential17abs.html.
Attributed Commons G3 manuscripts listed in Section 2 are unpublished research dependencies, not independent validation.

## 11. Process-integrity assessment

This is a proof audit and derivation, not a systematic review; PRISMA/AMSTAR-2 scores are inapplicable. Inspected the actual source statements instead of relying on the previous summary. The finite-input and all-cap encodings are kept separate. No claim of exhaustive literature search, historical novelty, independent acceptance or formal verification is made. Main residual process risk: inherited compiler/admission assumptions were read, not fully reimplemented.

## 12. Robustness assessment

No statistical pooling, effect sizes or heterogeneity estimates apply. Theorems A-C depend on effective finite graph enumeration and polynomial source constraints. A metric experiment involving unrestricted exponentials would require another decision theorem. Theorem E depends on common serial-chain inheritance; independent routing invalidates the random-total-duration representation. A counterexample must satisfy those actual contracts. General closure would change upon a reviewed constructive source-size bound or an actual reduction using admitted biological sources and finite algebraic outputs.

## 13. Zotero and Obsidian integration

Store this as an unpublished proof note, tags: G3, finite-input, real-algebraic-geometry, semidecision, exact-realization, common-inheritance. Link it to EXACT-CRITERION and INTERIOR as dependencies, and to the primary quantifier-elimination reference as prior work. Record Theorems A-C as a computational reduction and Theorem E as a typed component. Keep the open-master claim separate from tested examples.

## 14. Appendix: verification and evidence limits

The accompanying exact_checks.py verifies the cap-three complete forest formulas, deletion consistency, cubic derivative/endpoints, two-atom moments, and strictly positive one-bigon survivals across a rational grid. Its negative controls check common/independent separation and boundary exclusions. It uses only Python's Fraction arithmetic. It does not implement arbitrary algebraic root isolation, quantifier elimination, unrestricted graph enumeration, or a full G3 recognizer.

Finite checks support implementation algebra; the arbitrary-input claims rest on the hand proofs. Independent review and formal proof-assistant verification remain pending.
