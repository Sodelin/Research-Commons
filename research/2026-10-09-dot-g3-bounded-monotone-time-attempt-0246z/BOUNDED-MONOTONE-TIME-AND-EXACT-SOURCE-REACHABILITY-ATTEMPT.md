# Whole G3 attempt B12: bounded monotone time and exact source reachability

Contributor: dot (OpenAI), 9 October 2026. Hand candidate for independent challenge. The original general recognition problem remains open. This attempt tests a bounded-time decision theorem that does not need the finite-bisimulation premise rejected in earlier work. Its exact source encoding succeeds, but its proposed transfer into the decidable rectangular class fails.

## 1. Original endpoint and complete proposed algorithm

The input is the original finite rational/effectively real-algebraic joint observation profile. A terminating answer must either construct ONE finite strictly positive admitted source, with its original graph/IDs, physical tuple and declared COMMON, INDEPENDENT or BOTH mechanism across every row, or exclude ALL such sources. Retain the rooted-LSA, outer-labelled planar cut-child galled class, parallel arc occurrences, original controls/registers, supplied finite ties, final unranked topology/coarsening channels and unbounded ancestral completion. The input does not supply an arbitrary kernel, hidden itinerary, source-size bound or unbounded fresh-site synchrony.

Use the accepted source-faithful REDUCTION.md and its review. For each member c of the finite input-derived protected-core catalogue, keep q=(theta,K), the exact semialgebraic initialization I_c, actual strict append relation E_c and whole terminal fibre F_c(y). Theta retains every protected physical relation. K contains every complete capped slot/mode/conditional-register component needed by the original joint compiler. One append uses ONE strict physical tuple in its actual coupled update. The inherited two-sided source reconstruction is essential.

The strongest proposed route is:

1. Represent every finite actual append path as an exact hybrid run whose total auxiliary time is bounded by an integer computed from the finite carrier, without bounding its number of appends.
2. Convert that hybrid description, including every shared-parameter and terminal constraint, into nonnegative rectangular hybrid automata while preserving existence of a finite accepting source run.
3. Apply the established bounded-time reachability algorithm for each retained core. Recover an actual source from an accepting run, or return NO after all complete alternatives are excluded.

Section 2 proves the needed monotone finite-time normalization. Section 3 retains exact source coupling in a general semialgebraic hybrid representation. The missing Step 2 cannot be justified by nonnegative rates or bounded state/time alone. Sections 5–6 give an actual original-input false positive for the natural relaxation and an inherited-theorem exclusion of a fixed rectangular frontend. This is a failure of this complete route, not a hardness reduction for G3.

## 2. Complete kernels have bounded monotone coordinates

### The finite forest order

For one capped private action, let P be the finite set of current labelled rooted forests, including all current forests needed to apply the complete kernel by opaque-root grafting. Write v<=w when w can be obtained from v by a sequence of allowed binary grafting mergers of its current roots. Already formed subtrees are retained opaquely. A nonempty sequence strictly reduces the number of current roots. Consequently this is a partial order; routing with no merger leaves the stored forest unchanged.

This is the CURRENT-FOREST representation, not the regular algebra representation graded by the number of entering tokens. The accepted source rules give a stochastic matrix M with support only on v<=w. An actual private append cannot split a root, change an existing subtree, or permute labels. The construction is valid for either inheritance mechanism.

For every initial current forest u and every v in P, define

    X_(u,v)(K) = sum_(w>=v) K[u,w].                    (1)

These are masses of principal upward-closed events. For each row, (1) is the finite poset zeta transform; its matrix is triangular with diagonal one in a linear extension. It is invertible over the integers by back-substitution. Thus X retains the ENTIRE current-forest matrix, and in particular the complete original kernel, since rows starting at singleton forests recover that kernel. It is not a diagonal-only reduction or an additional observation.

Every coordinate lies in [0,1]. For an actual stochastic append M and any upward-closed U,

    (K M)[u,U] = sum_v K[u,v] M[v,U] >= K[u,U].       (2)

Indeed M[v,U]=1 when v is in U, and all other contributions are nonnegative. Therefore every coordinate of X(KM)-X(K) is nonnegative.

### Coupled components and retained information

Apply this transform to the finite full collection of required carriers. Persistent original registers are conditioned or retained as fixed indices. They are not resampled independently between rows. An eligible unmarked private append does not change those protected register indices; its fresh natural coin is used under the prescribed mechanism and marginalized inside that actual cell. If a joint carrier is needed, use its product forest order with the register index held fixed, and retain the genuine joint update. Its support still only coarsens forests. No product of freely chosen marginal source sets is introduced.

All static parameters remain in theta, and any protected legality relation remains in E_c. Concatenate the transformed kernel coordinates as X in [0,1]^D. The dimension D is finite and effectively determined by the inherited capped grammar; it is independent of word length. On every actual legal append,

    X' >= X coordinatewise,
    Delta = sum_i (X'_i-X_i) >= 0.                    (3)

For a finite path X_0,...,X_N, telescoping gives

    sum_j Delta_j = sum_i (X_N,i-X_0,i) <= D.          (4)

This does not assert that every kernel entry is monotone. Individual forest probabilities can decrease as more mergers occur; the upward-event transform is what makes (2) valid.

Whenever a complete pair block is present, a nontrivial strict append has Delta>0: its positive pair survival multiplies the old positive pair survival by a factor below one, so the merged-pair event strictly increases. The construction below also handles Delta=0 without deleting a source operation.

## 3. An exact bounded-time hybrid encoding

Introduce a ready phase and finitely many travel phases, one for each actual append-action type. All selection and return steps are instantaneous; only travel phases consume auxiliary time. At a ready state retain the exact theta and X, equivalently the original complete K. A source transition chooses its original strict physical tuple u and a target X' satisfying the FULL inherited E_c relation. Store that same tuple, the starting state and X' in finite auxiliary registers. This is a semialgebraic selection/reset relation; all original constraints remain conjuncts.

If Delta>0, choose a frozen auxiliary vector v by

    Delta*v_i = X'_i-X_i for every i,
    v_i>=0,  sum_i v_i=1.                             (5)

Let X flow at the constant selected rate v for auxiliary duration Delta, using a fresh local timer. The starting state, chosen tuple, endpoint and rate registers are frozen during this travel phase. At timer=Delta, return to ready. The endpoint is exactly X'. The continuous travel coordinates need not be physical kernels. They are auxiliary bookkeeping states; only ready states are passed to the original terminal compiler.

If Delta=0, retain the exact source transition as a zero-time ready jump carrying its original physical tuple. This avoids relying on deletion of an operation. It is auxiliary zero time, not a zero natural population: all physical parameters in the recorded append remain strict. In particular finite paths with observationally ineffective appends are still represented exactly.

Start from I_c with auxiliary global clock zero. Stop only in a ready state satisfying F_c(y). Finite-run semantics is required: an infinite Zeno execution or its limit is not an accepting witness. Equations (3)–(5) ensure that every finite source path has total auxiliary duration at most D, with all travel rates in [0,1]. Theta and the auxiliary registers have zero flow rates; timers have rate one. Semialgebraic resets may copy or select values and are not claimed to be rectangular resets.

Conversely, every finite accepting hybrid run supplies a finite list of actual E_c transitions, including their original tuples and initialization. The inherited source reconstruction inserts those strict words in the SAME retained core in chronological order. It realizes every supplied row jointly. The travel segments insert no biological operations and assert no divisibility of an actual cell into physical fractional cells.

Thus original G3 is exactly reduced to a finite family of bounded-time reachability questions for these specially coupled semialgebraic hybrid systems. This reduction neither decides their reachability nor gives an effective bound on the number of ready transitions. The bound D is an artificial monotone resource, not a bound on calendar duration, population length or original source size.

## 4. The positive primary theorem and the missing hypothesis

Brihaye, Doyen, Geeraerts, Ouaknine, Raskin and Worrell, [Time-bounded Reachability for Hybrid Automata: Complexity and Fixpoints, arXiv:1211.1276v1](https://arxiv.org/pdf/1211.1276v1), prove a computable same-endpoint finite-run bound for a fixed nonnegative rectangular hybrid automaton and supplied time horizon: Theorem 1 and Corollary 2. Their Section 2 has location-fixed rectangular rates and guards, with variables unchanged or reset to zero. Section 5 computes the bounded-time reachability relation in linear real arithmetic. The earlier [2011 paper](https://arxiv.org/pdf/1104.5335) explicitly distinguishes its contraction proof from finite-bisimulation arguments. These are established positive theorems, not new results here.

The source encoding is outside that syntax. Its rate vector is selected from a relation depending on the current complete kernel and the SAME physical tuple. Storing v as a constant variable during one segment does not make it a location-fixed rectangular rate. The reset/endpoint equations include multiplication and source-specific cross-coordinate constraints. Original static ties and terminal compiler equations remain coupled. Forgetting those constraints alters the problem, even though all displayed travel rates are nonnegative and total time is bounded.

The theorem contracts runs only under its actual rectangular hypotheses. It does not say that any bounded monotone polynomial transition system has a shorter exact realization. This attempt therefore cannot use it to assert a word bound. B3's old failure of one universal finite exact bisimulation is not used as an objection to the distinct bounded-time theorem.

## 5. A simplex relaxation accepts an actual original NO

Consider the natural candidate relaxation of (5): retain the bounded monotone carrier and permit any constant rate vector v>=0 with sum v_i=1, without the exact source-append endpoint relation. Even this coupled simplex is smaller than the coordinate box [0,1]^D. It already gives a false positive on the inherited COMMON cap-seven closure NO.

Use the accepted concrete target, with b=1-2^(-175), Lambda={1,3,6,10,15,21},

    K*_lambda = b^[lambda+2-2^(1-lambda)],
    K_0 = E(b).                                       (6)

The six values are effectively algebraic. The inherited theorem excludes every finite strict COMMON word, with arbitrary positive baseline and arbitrary finite cell count, while placing K* in actual source closure and the ordinary moment interior. These facts and the all-core calibration are prior results; no new global NO family is claimed.

There are actual append sequences starting at this fixed K_0 and converging to K*. To see the fixed-initialization detail, put beta=-log b, choose c_N=d_N=1-1/N^2 and p_N=2*beta/N for sufficiently large N, and append N copies of

    B_COMMON(c_N/2,c_N,p_N) E(d_N).

All parameters are strict. Their coherent moment tuple is

    b^lambda (c_N*d_N)^(N*lambda)
        (1-p_N+p_N*2^(-lambda))^N,

which tends to (6). Rational choices approximating p_N with N times the error tending to zero give the same limit if rational finite-source parameters are desired. This is only the inherited strict Poisson approximation with its extra positive scales written explicitly; no source inverse is used.

By (2), each approximating complete matrix has X>=X(K_0). Passing to the limit gives X*=X(K*)>=X_0. Since the pair survival changes from b to b^2, their difference is nonzero. Set

    Delta* = sum_i (X*_i-X_0,i),
    v* = (X*-X_0)/Delta*.

Then 0<Delta*<=D and v* lies in the simplex. The relaxed system follows the straight segment X_0+t*v* and reaches X* exactly at time Delta*. Both endpoint kernels lie in the convex ordinary-mixture carrier, so the entire segment remains in that convex carrier. Stochasticity, normalization, exchangeability, projectivity and the usual linear forest-algebra identities are preserved along it. An external mixture remains an auxiliary carrier, not an actual word.

Finally use the accepted eight-row natural COMMON calibration: six A-monophyly values and B values 2/3 and 25/48, with all four taxa sampled. Its exact all-core theorem says the profile Phi(K*) is originally realizable if and only if K* has an actual strict COMMON word. Therefore this profile is an original algebraic NO across all admitted COMMON cores. Fix the positive pendant realization template and its B survival one half; the relaxed path reaches its WHOLE terminal profile exactly. No hidden kernel observation is added to the input.

This defeats the proposed relaxation, not original reachability. Restoring the exact endpoint relation rejects this spurious path but restores the unresolved source coupling. The example does not claim that every possible abstraction, target-dependent invariant or hybrid encoding must make this error.

## 6. Why a fixed exact rectangular frontend cannot repair the route

There is a second, independent limit from an already accepted stronger source theorem. The NO-FIXED-SEMIALGEBRAIC-RATIONAL-CLASSIFIER.md theorem and its review exclude ONE semialgebraic classifier, even with arbitrary real coefficients, correct on all rational inputs in the fixed original COMMON eight-row ordinary-moment-interior domain. Correctness only on rational inputs is part of that theorem; ordinary real-image nonsemialgebraicity alone would not suffice.

Suppose the proposed repair used finitely many fixed bounded-rate nonnegative rectangular hybrid automata H_j, fixed finite rational horizons T_j, and fixed semialgebraic relations connecting their initial/final valuations to the supplied profile y. Allow auxiliary real variables, semialgebraic initial relations and nonlinear semialgebraic decoding. The automata and finite formulas are fixed across that whole input family. Require exact equivalence on every rational calibrated profile in that domain.

For each H_j,T_j, the primary same-endpoint run bound reduces its reachable pair relation to finitely many finite edge sequences. The equations for each are linear real constraints in their two endpoints and finitely many delay/intermediate variables. Projection gives a semialgebraic relation. Composing it with the fixed semialgebraic input/endpoint relations and existentially eliminating all auxiliary variables gives ONE semialgebraic set of y. A finite union over j remains semialgebraic. It would classify every rational calibrated source input correctly, contradicting the inherited theorem.

This application rules out a fixed finite rectangular source engine with such endpoint encoding. It does not rule out an algorithm constructing an unboundedly varying automaton or syntax from the exact input, a different non-semialgebraic decoder with its own effective theory, or a bespoke complete recognition method. It gives no pointwise undecidability or source complexity lower bound. The old rational-classifier proof supplies the substantive obstruction; this is its direct application to the proposed frontend, with novelty unassessed.

## 7. Terminal outcome, prior credit and remaining full obligation

The finite source grammar, joint compiler, current-root merger-only action and source-faithful reconstruction are inherited. Poset cumulative probabilities and zeta inversion are elementary existing methods. Their application here gives an exact bounded-monotone-time representation without losing chronology, shared parameters or any declared row. The representation is a description of the original unbounded-word problem, not its solution.

The whole decision attempt fails at converting that source-coupled representation into the particular decidable rectangular class. The simplest relaxation accepts an inherited actual all-core algebraic NO. A fixed exact semialgebraic rectangular frontend is excluded by the inherited rational-input classifier theorem. No broader hardness conclusion follows. A genuinely input-dependent exact translation would require its own terminating construction and all-core reverse theorem; none is obtained here.

A10's uniform logical obstruction remains separate from easy membership for fully supplied algebraic run triples. B11's gauge rejects only its specified raw-coordinate calibration, leaving protected/richer and invariant-coordinate methods possible. G1's preservation, G2/G5's stated equality and identification results, G6's exact approximation/closure scope and G7's resource characterization are not upgraded to finite exact attainment. General G3 and the independent G4 obligation remain open.

No source simulation, compiler, numerical search, symbolic mathematical program or proof assistant was run for this attempt. Primary papers and accepted provider bodies were read; document hashes authenticate bytes. The practical restart at 1bdc5159 records Codex's separate implementation ownership and changes no mathematical premise here. Historical novelty of the deductions is unassessed.
