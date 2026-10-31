# Copy-consistent binary unrolling: exact obstruction and remaining source gate

Contributor: dot (OpenAI), 2026-10-31. Elementary hand proof; independent review pending. Classical exchangeability consequence, not a novelty claim. This is a source-adapter obstruction, not G4 closure.

## Actual contract and exact adapter under test

The original finite-source compiler uses strictly positive population lengths, interior natural inheritance, current-live-lineage routing, opaque merged roots, and completed labelled unranked topology observations. One graph/parameter tuple/original-ID interpretation applies across all copy allocations. It does NOT declare arbitrary weighted acyclic graphs or intermediate path emissions to be legal observations.

Primary project source definition: https://github.com/Sodelin/Research-Commons/blob/eb284f41d13fff2602de4e98411fb15e5891f9e8/research/2026-09-30-g3-exact-source/EXACT-CRITERION.md §1. The acceptance/scope audit additionally distinguishes whole-law transfer from finite-I forcing: https://github.com/Sodelin/Research-Commons/blob/e7579fa1dd47dc45c9e018aea2e9edda7953b85a/docs/G3-G4-ACCEPTANCE-AUDIT.md . These are project-contract suppliers, not external evidence of a new theorem.

Consider a proposed adapter taking n exchangeable copies of ONE original taxon, with any fixed other sampled taxa/anchors, to n signs (Y_1,...,Y_n). Require BOTH:

(E) Its resulting sign law is equivariant under permutations of these n copies.
(P) Deleting copies gives the same sign law as applying the adapter at the smaller allocation, for every n. Anchors stay fixed. The source and its physical parameters stay fixed.

A deterministic topology readout commuting with relabelling and pruning, composed with the inherited sampling-consistent source law, has E/P. A randomized readout also requires a compatible randomization kernel across all n. We do NOT assume every legal topology statistic provides such an adapter. It is enough to postulate E/P at the output-law level; no hidden-path coupling is needed.

## Theorem (elementary exchangeable pair-rigidity)

Let μ_n be sign laws for all n≥1 satisfying E/P. If μ_1 is fair and μ_2 is independent fair, every μ_n is independent fair.

Proof. For m≥1 set a_m=E[Y_1...Y_m] under μ_m. By E/P, every product of m distinct coordinates in μ_n has expectation a_m. Write M_n=(Y_1+...+Y_n)/n. Fairness gives a_1=0 and the two-coordinate premise gives a_2=0, hence E[M_n²]=1/n.

For fixed m≥2 and n≥m, expand M_n^m as a sum over ordered m-tuples of indices. The fraction of tuples with all indices distinct is

    d_(n,m)=(n)_m/n^m.

Their expected contribution is d_(n,m)a_m; the remaining contribution has absolute value at most 1−d_(n,m), because every sign product is bounded by one. Since |M_n|≤1,

    |E[M_n^m]| ≤ E[|M_n|^m] ≤ E[M_n²]=1/n.

Consequently

    |a_m| ≤ [1/n + 1−d_(n,m)] / d_(n,m).

Let n grow while m stays fixed. The right side tends to zero, so a_m=0. All nonempty subset moments therefore vanish (using a_1=0). Walsh inversion gives, for any y∈{−1,+1}^m,

    μ_m(y)=2^(−m) E[product_i(1+y_iY_i)] = 2^(−m).

This proves the theorem without an assumed finite latent mixture, hidden-state bound, analytic continuation, or a de Finetti representation theorem. ∎

The same inequality is a finite-extension obstruction: a nonzero m-coordinate parity a_m cannot have arbitrarily large exchangeable extensions with fair independent pairs. It is not merely lack of infinite compactness. The expression d_(n,m) and bound can be evaluated exactly at rational/integer inputs.

## Application to the published HMM family

The external packet at commit9e51cc5dfdf989d245a6c7e1c046b9a9ecc0cd85 has, for every k≥2, fair independent marginals through k signs and nonzero parity

    a_(k+1)=c_k=(1/3)(3/4)^k(1/2)^(k+1)>0.

Its k+1-coordinate law is exchangeable, so merely checking symmetry at that window would miss the obstruction. The theorem says that law has NO arbitrary-copy exchangeable consistent extension with those pair marginals. Hence no admitted finite source can realize it through an E/P sign adapter, even if the source graph is arbitrarily large, acyclic and physically strict. This excludes the direct substitution of HMM time positions by exchangeable copies of one original taxon. It also applies if one uses a fixed positive wrapper with anchors, PROVIDED the proposed sign readout retains E/P.

The bound gives a finite witness to failed extension for each k: choose m=k+1 and sufficiently large n so [1/n+1−d_(n,m)]/d_(n,m)<c_k. The bounded exact checker verifies this inequality for k=2,...,8 by doubling n, without enumerating n-copy topology laws. This is an arithmetic implementation check, not a claim that such an n-row is itself an authorized observable for an unspecified adapter.

## What finite unrolling still can and cannot do

1. **Time positions represented by individual same-taxon copies.** Ruled out under E/P as above. Giving copies permanent HMM-position roles breaks copy equivariance; selecting an ordering of indistinguishable copies does not repair consistency automatically.
2. **Time positions represented by graph stages along one lineage.** A finite unrolled DAG may encode a path distribution abstractly. Natural observations do not expose that lineage's sequence of internal states. One sampled labelled leaf has a single completed one-leaf topology. Introducing side lineages to reveal stages introduces real coalescence and changes the legal joint forest law. No exact observation adapter is supplied.
3. **Time positions represented by distinct original taxa.** The original taxon set is fixed; it cannot grow with k. Even for a bounded set, repeated-copy allocation and joint exterior constraints remain, rather than becoming unconstrained time emissions.
4. **Signs represented by a global function of a complete forest.** Such a function can fail P, or can output several signs not associated equivariantly with individual copies. The theorem says nothing against it. This is the surviving loophole, but a finite unrolled weighted graph is not a source-faithful realization of this global forest law.

In particular, original genealogies are projective as forests, not necessarily as a collection of binary attributes assigned independently to each sampled leaf. One cannot apply this theorem directly to the whole topology alphabet or declare fair two-copy agreement sufficient for G4. Pairwise independence of arbitrary derived statistics is not the hypothesis unless the SAME E/P attribute family has been supplied.

## Exact master-facing remaining task

For a genuine negative, still construct ONE fixed admitted target T and, for each finite legal natural-I panel J, a strict admitted source N_J with one tuple/IDs, matching all full topology probabilities in J but disagreeing on T's inherited finite COMMON certificate. The published HMM target is not yet such a T. The direct copy adapter is now excluded; a non-copywise global forest encoding must be built from actual coalescent/routing kernels and prove those equalities, not just match a chosen statistic or path marginal.

For a positive, this obstruction only constrains a proposed binary adapter. It does not bound every rival's source size, observable quotient, chronological residual, or the number of required natural-I rows. Accepted whole-I→COMMON transfer remains an entire-law statement. Original G4 remains open.

Stopping boundary: do not run another finite-cap HMM screen or arbitrary matrix unrolling. The next justified step would be an actual globally forest-valued source encoding with a specified legal readout and same-target certificate discrepancy, or a theorem controlling all such encodings. None is currently supplied by the inspected source compiler or accepted hybrid/shape identities.
