# Whole G3 attempt B5: exact positive occupation flow and the terminal decision gap

Contributor: dot (OpenAI), 8 October 2026. Hand candidate for source-critical challenge. The original full G3 statement is unchanged. No total recognizer, undecidability result or historical novelty is claimed.

## 1. Entire intended argument

For finite admitted algebraic input, use the inherited finite protected-core/shared-register compiler. Replace its unbounded exact append reachability by a positive occupation-flow problem. Prove that a feasible finite flow yields an ACTUAL finite strict source rather than an external mixture. Then seek a finite, effective exact feasibility certificate for every YES or NO through polynomial moments and dual functions. If the final certificate theorem held, fixed-architecture RCF extraction would supply a source and all original cores would be exhausted on NO.

This is a whole-source architecture: both declared modes, every retained core, all static shared parameters and every input row remain in one state/target relation. No additional experiment, hidden observable, changed source class, or unbounded supplied parameter tie is introduced. The source reduction is prior work. Occupation measures and linear-programming formulations of controlled reachability are also prior; the argument below checks exact applicability, not novelty.

## 2. Exact source transition system

Let Q be the finite disjoint union of the compiler's semialgebraic state spaces. A state keeps the discrete retained core, the SAME static theta and the complete tuple of all coupled capped kernels. Let I be its semialgebraic set of legal initialized states. Let E be the finite union of graphs of LEGAL strict append steps, including the actual coupled parameter updates required by the source. An edge has projections s(e),t(e) to its before/after state. No edge inserts an already arbitrary-length macro-word. Let F_y be the entire semialgebraic target fibre of the supplied original responses.

The inherited compiler gives

    original input y is YES  iff  some finite E-path from I reaches F_y.

Fixed finite paths reconstruct actual source words in their retained cores. They preserve all input rows and the original controls/IDs/registers. One cannot replace E by a product of separately relaxed slot transitions. It is harmless for Q to contain auxiliary states not actually reachable from I; the theorem below does not assume them physical.

For k>=0 let R_k be the states reachable from I in at most k edges. Each R_k is semialgebraic by the finite path compiler and real quantifier elimination. R=union_k R_k is Borel. Define d(q) as the minimum such k, or infinity if q is unreachable.

## 3. Finite positive flow is EXACTLY finite source reachability

Consider finite positive Borel measures sigma, nu and mu, where sigma is a probability measure concentrated on I, nu a probability measure concentrated on F_y, and mu a finite measure concentrated on the actual strict edge relation E. Require equality of Borel measures

    s_*mu - t_*mu = sigma - nu.                         (1)

Concentration means measure one/zero as appropriate on the declared strict sets, not inclusion merely in their closures. Mixing initial states or target states is an optimization device; it is not admitted as a biological source.

**Exact assertion.** Such measures exist if and only if y is YES. More precisely, if D is the shortest number of append edges from I to F_y, with D=infinity on NO, then

    inf {mu(E): (1) and the stated positive support conditions} = D.    (2)

When finite, the infimum is attained by the occupation measure of a shortest actual path and is an integer. This counts append edges, not all retained-core vertices; the inherited finite core allowance gives the corresponding source-size conversion.

**Proof.** A finite path q_0,...,q_D gives sigma=delta_(q_0), nu=delta_(q_D) and mu=sum_(i<D) delta_(e_i); telescoping proves (1), with mass D. A zero-edge path uses mu=0.

Conversely suppose (1) holds and write M=mu(E)<infinity. For each integer N>=1 put

    d_N(q)=min(d(q),N), including d_N=N when d=infinity.

This is a bounded Borel, indeed semialgebraic, function because its finitely many level sets are formed from R_0,...,R_(N-1). Every legal edge satisfies

    d_N(t(e)) <= d_N(s(e))+1.                           (3)

If its starting state is reachable, append the edge to a shortest path; if it is not, the inequality follows from d_N<=N. Also d_N=0 on I. Integrating (1) against this bounded function gives

    integral d_N dnu = integral [d_N(t(e))-d_N(s(e))] dmu <= M.  (4)

If no target is reachable, d_N=N on all of F_y, contradicting (4) for N>M. Therefore D is finite. For N>=D every target state has d_N>=D, so (4) implies D<=M. The shortest-path construction attains equality. In particular any feasible flow of mass M guarantees an actual target path of length at most floor(M). QED.

No disintegration, deterministic purification theorem, compactness or relaxed control realization is needed for this implication. The whole-state balance preserves the static tuple: a path extracted by the conclusion cannot change theta or its retained core except as permitted by E. Exact flow does not introduce a rowwise source mixture.

## 4. Why finite polynomial balance tests are not the same constraint

The hoped-for finite algorithm would replace equality (1) by finitely many polynomial tests. Bounded current-root merger depth does NOT make those tests a complete basis. The following exact countercheck stays inside a fixed cap's ACTUAL ordinary COMMON source curve.

Fix m>=2. The capped ordinary kernel K(x)=E(x) has polynomial coordinates of degree at most lambda_m=binom(m,2). Restrict any finite list of polynomial state tests to this curve, with all other static registers fixed. There is a finite integer D bounding every resulting univariate degree. Take rational x_0,c in (0,1), and L=D+1. Put x_i=x_0 c^i for 0<=i<=L. Every edge K(x_i)->K(x_(i+1)) is physical: append a COMMON equal-arm cell and positive connector with x=y=a=sqrt(c) and any fixed interior coin. Its full kernel is E(c). The leading population E(x_0) is strict.

There exists a nonzero rational vector a_0,...,a_(L-1) such that

    sum_(i=0)^(L-1) a_i x_i^k = 0,  1<=k<=D.            (5)

This follows from D homogeneous equations in D+1 variables. The sum of the a_i is nonzero: otherwise the square Vandermonde matrix with exponents 0,...,D would annihilate the vector. Likewise the moment at k=D+1 is nonzero, because the matrix with exponents 1,...,D+1 is invertible at distinct positive x_i.

The unit-weight path occupation mu_0 has exact divergence delta_(K(x_0))-delta_(K(x_L)). Perturb its edge weights to 1+epsilon a_i, choosing nonzero rational epsilon small enough that they all remain positive. The positive finite measure mu_epsilon has the SAME divergence as mu_0 against every retained polynomial test: for x^k the difference is

    epsilon (1-c^k) sum_i a_i x_i^k = 0,  k<=D.        (6)

But its divergence is NOT the same Borel measure, as the k=D+1 test detects. These are genuine positive edge measures on actual strict source transitions, not pseudo-moment matrices or inverse populations.

Therefore no prescribed finite polynomial/Veronese test list implies full measure balance merely from the source's bounded merger grade. Adding finitely many higher-degree tests repeats the same issue. This countercheck does NOT exhibit a NO input passing every finite relaxation: its target is an ordinary YES, and other direct source paths exist. It rejects the proposed finite-balance identity step, not every possible input-dependent finite certificate theorem.

## 5. Primary occupation-measure theory: applicable formulation, missing algorithm

Han and Tedrake, Controller Synthesis for Discrete-Time Polynomial Systems via Occupation Measures, arXiv:1803.09022v2, Sections II-IV, formulate a controlled Liouville equation as an infinite-dimensional measure LP, then use finite moment/SOS approximations. Their state/control and target sets are compact semialgebraic; the source paper does not turn an arbitrary exact strict-support unknown-horizon point query into a terminating yes/no algorithm. Its moment representation conditions quantify over all degrees. Primary version: https://arxiv.org/pdf/1803.09022v2 .

Those ideas support the formulation, not the missing stopping theorem. Original positivity gives open parameter domains. Closing them admits boundary cells; imposing a uniform interior margin or total mass is a budget promise not supplied by G3. A reciprocal encoding of strictness requires its own noncompact moment theory. Convergence, approximate feasibility, finite rank at a tested order or an estimated finite optimum are not exact general NO certificates.

Even when one supplies a finite mass bound M, (2) shows that exact feasibility is equivalent to a finite-path search bounded by floor(M), already decidable by the inherited compiler. Discovering whether SOME finite mass suffices is exactly the original unbounded one-witness obligation. The measure formulation does not remove that quantifier.

## 6. Updated source constraints and full attempt outcome

The current scope at f6e0ad11 and the accepted grouped-mixture/positive-affine-exposure packets at 61b29cf and 48dc3fa are retained. The exact flow method does not posit a finite latent paintbox mixture or universal linear support exposure: its measures are on the full source-state transition relation and must satisfy all balance tests. It also does not claim that a nonlinear function of supplied responses is a newly available physical observation.

The newer accepted e694c6a3 attained-boundary family provides actual rational COMMON YES points in ordinary moment interior on the actual source-closure boundary, and a separately scoped cap-eight private all-copy forcing result. Hence a boundary flag cannot decide NO, and source regularity cannot be assumed for every YES. The supplied-normal arithmetic result still requires the normal and its mandatory affine-difference correction; it gives no observation-only global count. The globally nonnegative ordinary-neutral log-character alphabet selector is already excluded by its accepted equality-case theorem. None of these results supplies finite flow-balance completeness or a terminal occupation-LP feasibility oracle.

The complete proposed recognizer therefore FAILS at the finite/effective certificate step. Sections 2-3 give an exact source-faithful alternative formulation; Section 4 disproves the proposed finite polynomial-basis simplification. No actual original NO certificate completeness, finite dimension reduction, computable mass bound or source-valid undecidability conclusion has been obtained. General G3 remains OPEN. Historical novelty, compiler verification and numerical execution are not claimed.
