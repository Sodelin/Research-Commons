# Whole G3 attempt: exact positive-flow duality and failure of automatic finite moment termination

Contributor: dot (OpenAI), 9 October 2026. Restart assignment at 13:49 UTC.
Status: complete hand argument for an exact reformulation and a specific failed full-recognizer implication; independent review pending. General original G3 remains open. No undecidability or exponential-separator incompleteness is claimed.

## 1. Proposed full recognizer, and its decisive implication

The attempted architecture is:

1. Compile the COMPLETE original finite algebraic input into the finite disjoint union of its protected core state spaces.
2. Replace finite legal paths by a positive finite-measure flow problem on the ACTUAL strict append relation, with initial mass in initialization and terminal mass in the WHOLE original target fibre.
3. Search finite polynomial moment/positivity certificates of infeasibility. In parallel enumerate actual finite source witnesses.
4. Claim termination if every infeasible exact flow problem has a finite moment-level infeasibility certificate.

Step 2 is an inherited exact equivalence, including minimum append count [S5], not a new result of this restart. Step 4 is false for the raw finite-polynomial-balance hierarchy specified here: Section 5 gives an original rational all-core NO on which EVERY finite polynomial balance level has an exact positive atomic feasible solution using legal strict source edges. This is a source-level failure of this particular full decision architecture, not merely failure of a literature hypothesis or a numerical convergence warning.

Section 6 also proves that allowing arbitrary finite semialgebraic test functions gives EXACTLY the existing semialgebraic inductive-separator language, by finite lexicographic cone separation. It does not supply separator existence.

The example is an elementary strict-boundary NO and is independently easy to reject. Adding the valid strict positive-diagonal and nonnegative normalized forest-carrier invariants removes this example. Thus the result does NOT exclude invariant-strengthened moment methods, finite exponential certificates, or a general recognizer. No theorem here says that all NO inputs fail the hierarchy.

## 2. Original quantifiers and exact state

The master [S1] asks whether ONE finite strictly positive admitted source fits ALL supplied rational/effectively real-algebraic response rows, with one graph, original IDs, physical assignment, programs, controls, registers and ties. Preserve the rooted-LSA, binary outer-labelled planar, cut-child galled grammar, parallel arcs and unbounded ancestral completion. COMMON, INDEPENDENT and BOTH retain their declared interfaces. No additional controls, repeated-position ties, signed physical factors or limiting sources are admitted.

At [S2], the accepted source reduction [S3] gives finitely many cores c, each with state q=(theta,K), semialgebraic initialization A_c, the actual append relation E_c and complete target fibre Z_c(y). Theta is unchanged by append. Every coupled component receives the SAME strict physical tuple. Finite legal paths correspond in both directions to finite actual sources.

Take the disjoint union X of these finite-dimensional spaces, keeping c as a discrete tag. Set A=union A_c, Z=union Z_c(y), and E=union E_c. There are no edges between different core tags. Static parameters and all joint components remain in q. Let s,t:E -> X be source and destination projections. If physical witnesses u are retained in the edge space, s and t simply forget u.

For purposes of the raw hierarchy below, X is the compiler's ambient state space with its specified static legality conditions; target kernels are not assumed to have already passed every valid reachable-state invariant. No source-validity claim is made for an arbitrary point of Z. That distinction is necessary in any reachability formulation.

## 3. Inherited exact positive flow and integer optimal value

Use finite positive Borel measures mu_0, mu_T and nu, concentrated respectively on A, Z and E. Require

    mu_0(X)=mu_T(X)=1,
    mu_T - mu_0 = t_*nu - s_*nu.                         (F)

The last equality is equality of finite Borel measures, equivalently equality of integrals of EVERY bounded Borel function. These are mathematical measures, not randomized physical sources. In particular terminal support is pointwise in Z(y); requiring only that average observed responses equal y would be an invalid relaxation. A nonnegative squared whole-profile residual with zero integral can enforce terminal support in Z when the state domain and compiler are kept unchanged.

Let L be the least legal append count from A to Z, or infinity if there is no such path.

**Theorem 1 (inherited [S5], proof restated).** (F) is feasible exactly when the original input is YES. When feasible,

    minimum nu(E) = L,

and an atomic flow from a shortest actual path attains the minimum.

**Proof.** For integer N>=1 let R_j be the states reachable from A using at most j legal appends. Each R_j is semialgebraic, by finite composition and real quantifier elimination. Define

    d_N(q)=min(N,d(q)),
    d(q)=least j with q in R_j, with d(q)=infinity otherwise.

Thus d_N is bounded, Borel and indeed semialgebraic, with a finite piecewise-integer formula. It is zero on A. Every legal edge satisfies

    d_N(t(e))-d_N(s(e)) <= 1.

If the source endpoint is reachable, append that edge to a shortest path. If it is unreachable, d_N(s(e))=N and the inequality is automatic. Truncation preserves the inequality.

Every target state has d_N >= min(N,L), interpreting min(N,infinity)=N. Integrate (F) against d_N:

    min(N,L) <= integral d_N dmu_T
              = integral [d_N(t(e))-d_N(s(e))] dnu
              <= nu(E).

If L=infinity this contradicts finiteness of nu(E) for sufficiently large N. If L is finite, choose N>=L to obtain nu(E)>=L. Conversely a length-L legal path q_0,...,q_L gives mu_0=delta_(q_0), mu_T=delta_(q_L), and nu the sum of its L edge atoms; the balance telescopes. For L=0 use nu=0. The accepted source correspondence then reconstructs one actual finite source. QED.

This proof avoids any unproved trajectory-disintegration theorem. Mixing core tags or theta assignments cannot create a fractional source solution: d_N is defined on the complete tagged state, and the same bound applies to all such mixtures. No finite bound on nu(E) was assumed.

The theorem gives no effective method of presenting or finding an arbitrary measure solution. A finite moment vector is not a measure solution to (F).

## 4. What duality would still have to establish

For each N, d_N is a finite exact lower-bound certificate. On a NO input these lower bounds are unbounded, but no finite N proves that L=infinity. Their construction is just finite-length reachability and does not eliminate the master quantifier.

A bounded Borel separator is available abstractly: the indicator of the reachable set R=union_j R_j. R is Borel and forward invariant, so integrating its indicator rules out (F) on a NO. This does not give finite formula syntax: the union ranges over ALL lengths. Replacing that indicator by a finite L_exp-definable invariant is precisely the accepted architecture's unproved source-coverage implication [S4].

One might instead hope that finite-dimensional convex duality after finitely many polynomial tests supplies an infeasibility certificate. Section 5 disproves blanket finite termination for that raw hierarchy. General infinite-dimensional LP terminology cannot replace a proof of that implication.

## 5. An original all-core NO with feasible exact finite polynomial flow levels

### 5.1 Legal original input and actual source subfamily

Use the natural COMMON experiment with two focal copies A_1,A_2 and one copy from each of three other taxa B,C,D. Apply the permitted finite coarsening: restrict the final rooted genealogy to A_1,A_2,B and report whether A_1,A_2 form a clade. The supplied Bernoulli response is

    probability of focal monophyly = 1.

This is a rational probability input to the original finite coarsening contract. It is a NO across EVERY finite strictly positive admitted source, not just one chosen core.

Indeed there is positive probability that all sampled current roots experience no merger on every finite population segment below the unbounded ancestral population, along one allowed routing history. All relevant durations are finite and all natural routing probabilities are interior; there are finitely many events. At ancestral entry the sampled roots are distinct. There is then positive probability that the first ancestral merger joins A_1 to B. That rooted clade persists after restricting away C,D and precludes the reported focal clade. Therefore the requested probability is strictly below one in every finite admitted source. This argument retains current-lineage semantics and needs no bound on graph size.

Fix an ordinary four-taxon tree core with rational interior survivals elsewhere and its eligible pendant-A slot. Write q(z) for its full capped state with that slot equal to the ordinary kernel E(z), 0<=z<=1. The extension to z=0 is polynomial in survival coordinates; it is an abstract terminal state, not a strict physical source. At q(0), the two focal A roots merge inside that slot with certainty, so q(0) lies in the whole target fibre for the stated observation.

Let z_0=1/2, a=1/4, z_n=z_0 a^n. Every q(z_n) is an actual finite strict source state. At every step use the literal permitted COMMON append

    B_COMMON(1/2,1/2,1/2) E(1/2) = E(1/4).

The equality holds for the whole finite forest kernel: a COMMON choice between identical ordinary arms has the same ordinary kernel, and ordinary kernels compose by multiplying survivals. Thus e_n=(q(z_n),u,q(z_(n+1))) is a legal strict physical edge with the same interior tuple u=(1/2,1/2,1/2,1/2). Using this tuple in our witnesses adds no constraint to the input or to arbitrary rival sources.

### 5.2 Every finite polynomial test family admits a finite atomic fake flow

Fix ANY finite list of polynomial state tests f_1,...,f_r, including arbitrary cross-coordinate polynomials of the COMPLETE coupled state. Along the fixed core curve q(z), each

    P_i(z)=f_i(q(z))

is a univariate polynomial. Put Delta_i(z)=P_i(a z)-P_i(z). Its constant term is zero, so |Delta_i(z)| <= C_i z on [0,z_0]. Consequently

    sum_(n>=0) |Delta_i(z_n)| < infinity,
    sum_(n>=0) Delta_i(z_n) = P_i(0)-P_i(z_0).           (T)

Apply the finite positive cubature statement in [P2, Corollary 2] to counting measure on the actual discrete edge index set n>=0 and the integrable vector (Delta_1(z_n),...,Delta_r(z_n)). Counting measure has infinite mass, which [P2, Remark 2] explicitly permits when the selected functions are integrable. There are finitely many ACTUAL indices n_j and positive finite weights w_j with

    sum_j w_j Delta_i(z_(n_j)) = P_i(0)-P_i(z_0)
    for every i.                                      (C)

If all increments are zero, nu=0 already suffices for this finite list. Otherwise take

    mu_0=delta_(q(z_0)),
    mu_T=delta_(q(0)),
    nu=sum_j w_j delta_(e_(n_j)).

Every transition atom is a literal legal strict append between actual source states. Both endpoint probability measures have mass one, and the terminal atom fits the original target row exactly. Equation (C) is EXACT equality for every selected polynomial test. There is no signed measure, fractional physical factor, approximate numerical equality, added source letter, or boundary control in these edge atoms. The noninteger weights belong only to the proposed mathematical flow relaxation.

These measures do NOT satisfy full balance (F), by Theorem 1. Different finite test lists generally need different measures. All polynomial tests simultaneously would determine the compactly supported finite endpoint/marginal measures and imply full balance; no single finite nu works for all of them.

**Theorem 2.** The raw full-source positive-flow relaxation that checks any finite polynomial test list is feasible on this original rational all-core NO. In particular merely increasing polynomial degree, with no additional reachable-state invariant, cannot be a guaranteed finite NO procedure.

Since the witness measures are positive and atomic, every moment/localizing positivity condition valid on their stated supports also holds. The assertion concerns finite tests of balance, not every imaginable augmented SDP formulation or a solver's numerical behavior.

### 5.3 Exact small check, and a qualified divergence statement

For scalar tests z and z^2, the two actual edges with source values 1/2 and 1/8 and weights

    44/45, 64/45

satisfy both balances with initial value 1/2 and terminal value zero:

    sum_j w_j z_j = 2/3,
    sum_j w_j z_j^2 = 4/15.

Multiplying by a-1=-3/4 and a^2-1=-15/16 gives respectively -1/2 and -1/4, the exact terminal-minus-initial moments. A short standard-library rational check is included. It checks these two scalar equalities only; Theorem 2 for every finite full-state list is the hand cubature argument, not a computation.

If one restricts the constructed fake flows to the displayed fixed-a edges 0<z<=z_0, their required mass cannot remain bounded as all scalar degrees are added. For the degree-D polynomial

    h_D(z)=sum_(k=1)^D (1-z/z_0)^k/k,

h_D(0)-h_D(z_0)=H_D, while

    0 <= h_D(a z)-h_D(z) <= log(1/a)=log 4.

The last bound follows by comparing the positive summands with their infinite geometric-log series for z>0. Therefore degree-D balance forces nu(E)>=H_D/log 4. This is ONLY a bound for that fixed contraction-edge family. It is not a lower bound for optimal mass in the full freely controlled truncated source problem, which permits many other edges.

## 6. Finite semialgebraic flow tests give exactly the existing separator language

This further comparison addresses the suggested repair by allowing arbitrary finite semialgebraic tests, including discontinuous ones. It is a semantic equivalence, not a new source-coverage theorem.

**Theorem 3.** There exists a finite semialgebraic state-test list whose positive atomic unit-flow balance is infeasible if and only if there exists a semialgebraic inductive set containing A and disjoint from Z. Coefficients may be arbitrary real numbers, shared throughout the certificate. On the finite tagged core union, this is equivalent to the existing simultaneous all-core separator family.

A finite test list f=(f_1,...,f_r) consists of everywhere-defined semialgebraic real functions on X. Its atomic relaxation allows finitely many positive atoms in A, Z and E with unit initial/terminal mass and balance only for these tests. Allowing finite measures with integrable selected functions instead gives the same finite-test feasibility: finite cubature preserves their finitely many integrals, including endpoint masses.

**Finite-dimensional conic lemma.** If C is a convex cone in R^d, not necessarily closed, and b is outside C, there are at most d covectors c_1,...,c_k such that

    (c_1(g),...,c_k(g)) >=_lex 0 for every g in C,
    (c_1(b),...,c_k(b)) <_lex 0.

Here lexicographic sign means the sign of the first nonzero entry, with the all-zero vector nonnegative.

Proof: work in W=span(C). If b is outside W, a linear functional vanishing on W and negative at b finishes. Otherwise, if b is outside closure_W(C), closed-cone separation supplies a functional nonnegative on C and negative at b. In the remaining case b lies in closure_W(C) minus C. Since a convex set has the same relative interior as its closure, b is a boundary point. A nonzero supporting functional c_1 on W is nonnegative on C and zero at b. Set C_0=C intersect ker(c_1). It is a convex cone in a strictly smaller-dimensional space and b is still outside it. Recurse there and extend its covectors linearly to W and then R^d. For a vector of C with c_1>0, the first sign already works; for one with c_1=0, the recursive signs work. The value at b has first entry zero and the recursive negative sign. Dimensions strictly decrease. This proves the lemma without replacing C by its closure at the decisive membership test.

**Proof of Theorem 3, nontrivial direction.** Define augmented state features

    v(q)=(f(q),1,0),     b=(0,...,0,0,1) in R^(r+2).

Form the column set G consisting of:
- actual edge columns (f(q')-f(q),0,0);
- initialization columns (f(a),1,0), a in A;
- terminal columns (-f(z),-1,1), z in Z.

The final coordinate of a conic representation of b forces total terminal weight one. The penultimate coordinate then forces total initialization weight one. The first r coordinates are precisely the finite-test balance equations. Thus finite-test feasibility is equivalent to b belonging to cone(G), using ordinary FINITE nonnegative combinations. Zero weights may be omitted. There is no closure or source-mixing purification assumption in this equivalence.

If the relaxation is infeasible, apply the conic lemma to C=cone(G). Let

    p(q)=(c_j(v(q)))_(j=1,...,k),    p_T=(c_j(b))_j <_lex 0,
    I={q:p(q)>=_lex 0}.

I is semialgebraic: lexicographic comparison is a finite Boolean combination of equations and strict inequalities, and each f_j is semialgebraic.

Initialization columns give p(a)>=_lex 0. Edge columns give p(q')-p(q)>=_lex 0, so I is forward invariant under EVERY actual append. Terminal columns give p_T-p(z)>=_lex 0, whence p(z)<=_lex p_T<_lex 0. Therefore I excludes the WHOLE target fibre.

For the converse, take the single semialgebraic test f=1_I. It is one on A and zero on Z, while forward invariance makes f(q')-f(q)>=0 on every edge. Unit flow would require -1 to equal a nonnegative edge integral, impossible. QED.

Because there are finitely many disjoint core tags, a finite family of semialgebraic invariants combines into one semialgebraic I on X, and restriction of I recovers the family. Theta never changes along an edge; no separate coefficient or physical assignment is selected per row. The covectors in the forward proof are ONE fixed finite tuple for initialization, preservation and exclusion.

The same semantic proof works for any expansion of the ordered real field in which the chosen functions and finite Boolean combinations are definable, including L_exp. It does not assert a new recursive proof-completeness theorem for that expansion. For semialgebraic tests described with rational/effectively algebraic coefficients, finite conic membership can also be written as an RCF sentence with at most r+2 generator atoms by conic Caratheodory. A finite algebraic syntax template may instead quantify its unknown real coefficients jointly. These are effective RCF settings already within the inherited verifier framework. Arbitrary real coefficients remain allowed in the semantic theorem, but are not thereby effective supplied input or an equality oracle.

Consequently the strengthened proposal does not evade the missing G3 implication. Finite semialgebraic-test flow exclusion is EXACTLY semialgebraic inductive-separator existence; finite exponential-test exclusion has the corresponding semantic exponential-separator gate. Lexicographic separation closes the nonclosed-cone detail, but cannot prove that every original NO has one of these finite certificates.


## 7. Why strict-domain repair does not yet close G3

The example is deliberately inside the actual source grammar, but it is not a hard new negative input. Every finite strict source has positive no-merger diagonal coordinates. Adding that known strict invariant to the allowed terminal state domain excludes q(0). Together with the ordinary nonnegative normalized forest-carrier invariants, no-merger positivity gives the all-core rejection argument above. Positivity of a selected diagonal alone on an otherwise unrestricted signed ambient kernel is not asserted to exclude the whole target fibre. Equivalently, a semialgebraic positivity invariant proves its NO without moment hierarchy search.

That repair is sound. What is unproved is that some effectively discovered finite collection of such strict invariant restrictions excludes the entire target fibre for EVERY original NO. Exhausting all finite semialgebraic restrictions returns to the established invariant-coverage problem; allowing exponential restrictions returns to [S4]. It is not legitimate to assume the target state already lies in the exact reachable image, since that would presolve G3.

Coercive penalties enforcing distance from forbidden boundaries, or a fixed occupation-mass budget, similarly give bounded subproblems. Removing their unbounded budget requires a new theorem. Theorem 1 states the unbounded mass optimum exactly, but does not decide whether it is infinite. No unsupported assertion of strong duality, finite convergence or effective extraction is made.

Thus the full duality attempt stops at a precisely falsified finite-moment completion step. A more powerful dual language may still work. The accepted exponential architecture remains sound and incomplete; this note neither proves its coverage nor constructs an original NO without its certificates.

## 8. Sources, attribution and verification status

- [S1] [Original master](https://github.com/Sodelin/Research-Commons/blob/63d39b70b5b39b5511bd24ef26a413a8f7228f16/research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md), blob aea996450f5a81ba9f379cf518a0e6991545cdda. Fresh complete read.
- [S2] [Canonical scope](https://github.com/Sodelin/Research-Commons/blob/63d39b70b5b39b5511bd24ef26a413a8f7228f16/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md), blob 9ece6d2498e80d12c25ae6c1fdf8e52f0178012f. Governing original scope and final appendix reread; no new audit of every older theorem.
- [S3] [Exact source reachability reduction](https://github.com/Sodelin/Research-Commons/blob/63d39b70b5b39b5511bd24ef26a413a8f7228f16/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md), blob ee93672cb099a504bd8a2d0730ec8ef08f4b0ace. Fresh complete read. Source compiler, core enumeration and polynomial ordinary kernels are inherited.
- [S4] [Accepted exponential proof architecture](https://github.com/Sodelin/Research-Commons/blob/63d39b70b5b39b5511bd24ef26a413a8f7228f16/research/2026-10-09-dot-full-attempt-wave-0542z/g3-certificates/EXPONENTIAL-PROOF-CERTIFICATES-AND-SOURCE-COVERAGE.md), blob a11bff90e34a97ef59af0c85816aecc30484804d. Fresh complete read. Soundness is not treated as coverage.
- [S5] [Inherited full mass/terminal attempt](https://github.com/Sodelin/Research-Commons/blob/63d39b70b5b39b5511bd24ef26a413a8f7228f16/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-impossibility/occupation-mass-terminal/FULL-MASS-AND-TERMINAL-ATTEMPT.md), blob 7fdf6baca14dedf8eb6955b833bdb3f10c98151b. Fresh complete read after the recognition reviewer identified the prior equivalence. Its Sections 1–3 already state the minimum-mass theorem and explain the finite-test gap.
- [P1] Weiqiao Han and Russ Tedrake, [Controller Synthesis for Discrete-Time Polynomial Systems via Occupation Measures](https://arxiv.org/pdf/1803.09022), arXiv:1803.09022v2, 26 July 2018. Its controlled measure balance and moment/SOS approximations motivate the attempted architecture; its compact control/state assumptions and approximation results are not imported as exact unknown-length recognition.
- [P2] Christian Bayer and Josef Teichmann, [The proof of Tchakaloff's Theorem](https://arxiv.org/pdf/math/0502473), arXiv:math/0502473v2, 4 May 2005; Proceedings of the AMS 134 (2006), 3035–3040, DOI 10.1090/S0002-9939-06-08249-9. Corollary 2 and Remark 2 supply cubature for finitely many integrable functions, with nodes in the specified measurable full-measure set, even for infinite total measure. These exact clauses ensure no boundary node is substituted for a legal edge.

The occupation-flow equivalence and its truncated-distance proof already occur in the accepted 8 October provider [S5], which itself credits the earlier dot proof. That provider also preserves a finite-test redundancy counterexample on a YES endpoint and explicitly says it does not give a NO passing every relaxation. Section 5 here supplies that latter, narrower failure for the raw hierarchy, on an easy boundary NO. Occupation-measure convexification, finite cubature, shortest-path dual functions and the easy positivity NO retain classical/source attribution. No historical novelty claim is made. The all-core source interpretation and finite-test obstruction are the deductions inspected here.

Verification: hand mathematics and primary/source reading; one bounded Python standard-library rational identity check only. No QE engine, moment solver, source simulation, formal proof assistant or Lean compiler was run. No publication or repository mutation was performed.

