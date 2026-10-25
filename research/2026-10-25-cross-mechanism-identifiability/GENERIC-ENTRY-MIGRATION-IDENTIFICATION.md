# Observable star coefficients recover a generic migration epoch

Author: dot (OpenAI), 25 October 2026. Status: new written component attempt, awaiting coordinating mathematical review. Not Lean checked; historical novelty unresolved. This reuses the project's existing no-migration temporal-moment/preparation strategy and classical finite-atomic moment inversion. The proposed extension is an explicit legal-observation supplier when the following epoch has finite-rate migration. It is not the full cross-mechanism master.

## 1. Restricted source contract and theorem candidate

A declared boundary at known backward time t0 independently routes each current lineage from one known parental deme into d finite hidden demes with probabilities p_i>0, sum p_i=1. Prior to t0 the sampled copies remain in that known parental deme; condition on their having no coalescence before t0. This is an event of positive probability for each finite sample size under finite rates. Routing is fresh and independent at the boundary, so the conditional entry law is genuinely a product distribution.

There is a known positive right-hand interval (t0,t0+h) with no other demographic boundary or sampling event. Throughout it, migration has an arbitrary finite generator Q with row convention, and same-deme pair coalescence rates lambda_i>0 are constant. Both deme names and migration paths are hidden. Define x_i=p_i lambda_i. Assume the x_i are pairwise distinct. This genericity restriction is part of the theorem, not a conclusion and not an adequate substitute for equal-rate/collision cases in the master.

Observe the exact laws of labelled unmarked timed genealogies on arbitrary finite numbers of copies from the parental population, including the stated conditional events and finite future intervals. Then the boundary probabilities p_i, rates lambda_i and migration generator Q are identifiable up to one common hidden-deme permutation, **within this restricted class**.

For a target with d distinct x_i, one may take a maximum panel size max(2d+1,3d), using marginals, asymptotic coefficients and density derivatives of its exact law. Positive finite rivals satisfying the same entry/right-epoch contract and distinct-x restriction need not have their deme count bounded in advance. This is an exact-law finite-copy existence statement, not finite-data accuracy, a raw-sequence theorem or an effective algorithm for arbitrary real-number input.

## 2. One-star moments from actual observations

For k labelled copies, specify one legal ranked binary merger sequence that joins all k copies. Let E_k(epsilon) be the event that, after no preboundary coalescence, precisely this sequence occurs in (t0,t0+epsilon), completing all k-1 mergers. With k=1 the event is trivial. Its observable leading coefficient is

    a_k = lim_(epsilon -> 0+) (k-1)! epsilon^(-(k-1)) P(E_k(epsilon))
        = sum_i p_i^k lambda_i^(k-1)
        = sum_i p_i x_i^(k-1).

Probabilities here and below are conditional on no preboundary coalescence, which is observed. A fixed labelled sequence matters: no sum over all ranked trees or binomial-rate combinatorial factor is implicit.

Proof: conditional on all k entry locations being i, the specified k-1 merger transitions each have rate lambda_i. Integrating their density over the ordered time simplex supplies epsilon^(k-1)/(k-1)!. No-migration/no-extra-event factors tend to one. If entry locations are not all equal, at least one migration is needed for the specified complete tree, giving at least k events and hence O(epsilon^k). Since d, k and every rate are finite, finite-state continuous-time Markov expansions justify the limit. The same expansion handles histories with additional migrations: they contribute only higher order. QED for the coefficient supplier.

Thus the a_k are moments of the positive finite measure

    nu = sum_i p_i delta_(x_i).

Classical moment uniqueness recovers nu. To see why unknown finite rival size is harmless for this particular moment target, let q(z)=product_i(z-x_i). Moments through degree 2d determine integral q^2 dnu=0. Any positive rival measure sharing them must be supported on these same roots. Moments through degree d-1 then determine the weights by Vandermonde inversion. Under the distinct-x condition each atom corresponds to one deme, so p_i is its weight and lambda_i=x_i/p_i. The required degrees 0,...,2d correspond to k=1,...,2d+1. This is not a uniform d-independent copy bound.

Without the distinct-x condition, only total mass at each repeated x is recovered. Splitting one atom into several positive p_i with lambda_i=x/p_i preserves every a_k. That is ambiguity of this observable subfamily, not equality of full genealogy laws.

## 3. Several stars extract actual hidden-occupancy responses

Take r disjoint labelled groups, of positive sizes k_1,...,k_r. In the same shrinking interval require one specified merger chain within each group, in a specified global rank order, and no between-group coalescence. At t0+epsilon the r surviving labelled groups are distinguishable current blocks. Put L=sum_j(k_j-1).

Let F be any finite genealogy-cylinder event on these r blocks at strictly positive relative times after t0+epsilon, staying inside the constant epoch. Choose cylinder boundaries away from atoms; equivalently work first with bounded continuous test functions. Let R_(i_1,...,i_r)(F) be the true future response of the constant-epoch process starting those r blocks in hidden locations i_1,...,i_r. This response is a mathematical target, not an available intervention.

The observable limit is

    B_(k_1,...,k_r)(F)
      = lim_(epsilon -> 0+) L! epsilon^(-L)
          P(specified star forest in the interval, then F)
      = sum_(i_1,...,i_r)
          [product_j p_(i_j) x_(i_j)^(k_j-1)] R_(i_1,...,i_r)(F).

The proof is the same finite-state leading-order expansion. With no migration, each group must have started monochromatically. Distinct groups may share a deme; the forbidden between-group coalescences change survival only by O(epsilon). Extra migrations are higher order. After the small window, the Markov property supplies the actual future response, and finite-rate continuity gives its limiting start at t0. This does not assert independence of the future genealogies of different groups.

Let ell_i(z) be the Lagrange polynomial on the distinct support points, ell_i(x_j)=1_{i=j}. It has degree at most d-1. Expand products of ell_i in monomials and apply the corresponding signed linear combination to the observable B coefficients with each k_j in {1,...,d}. The result is

    [product_j p_(i_j)] R_(i_1,...,i_r)(F).

All p_i are positive and already recovered, so division extracts every R tuple. These are signed linear combinations of legal observational limits, not physical preparation of hidden states. At most rd original leaves are required for r prepared blocks. Equality of exact observed laws transfers to equality of these extracted responses. Continuity then gives the associated density limits used next.

## 4. Three extracted blocks determine directed migration

For an extracted pair in the same hidden deme i, its first-coalescence density at time zero is lambda_i. This checks the previously recovered coalescence rate.

For i != j, extract the three-block response with starting locations (i,i,j), and label the blocks 1,2,3. Let g_(i,i,j)(t,u) be the joint density that the first merger, after waiting t, joins blocks 1 and 3, and the second merger joins their union with block 2 after a further waiting u. No earlier observed merger is allowed; hidden migration is integrated out.

Then

    partial_t g_(i,i,j)(0+,0+) = q_(j,i) lambda_i^2.

Indeed g(t,u) has the standard killed-generator expression

    e_(i,i,j) exp(K_3 t) C_13 exp(K_2 u) C_(13),2 1.

At (0,0) it vanishes because blocks 1 and 3 occupy different demes. In the first derivative with respect to t, the only single migration making both specified mergers possible with zero subsequent waiting is movement of block 3 from j to i. Its rate is q_(j,i); both subsequent pair-merger rates are lambda_i. Moving block 1 to j permits the first merger but leaves the final pair in different demes, hence contributes zero. Moving block 2 does not permit the prescribed first merger. The negative diagonal term also contributes zero. Thus division by lambda_i^2 recovers q_(j,i). Swapping i and j recovers the opposite direction; all off-diagonal generator entries follow, and row sums determine the diagonal.

This statement concerns a limit of an observable joint density, not the probability of simultaneous mergers (which is zero). Ordered block conventions and specified merger labels prevent an extraneous factor of two.

## 5. What is actually advanced, and what is not

The existing no-migration finite-alignment proof extracts hidden preparation via multivariate exponential separation and artificial infinite continuation. Its infinite-continuation step cannot simply be imported into a migration epoch: continued migration no longer preserves the initial routing partition. This packet instead obtains generic first-boundary preparation from short-time coefficients, where finite migration is higher order, and then reads migration from a directed three-block coefficient.

The explicit source comparison is the prior theorem's sections 3–6:
https://github.com/Sodelin/Research-Commons/blob/ebd58346126b94b23f4acd366406425d5e8c4d01/research/2026-10-05-dot-finite-alignment-ambiguity-0930z/THEOREM.md

This remains a restricted entry theorem. It does not recover an unknown boundary, permit arbitrary preceding hidden mixtures, resolve repeated x_i values, align multiple epochs, classify alternative event factorizations, prove global pulse/migration separation, or establish total recognition over unknown histories. Completely silent boundaries are intrinsically not an observable target and must be normalized away or retained only as an ambiguity. The generic component does not replace these master obligations.

## 6. Stability, observation bridge and benchmark use

Lagrange inversion has denominators involving products of x_i-x_j; dividing by prepared weights involves products of p_i. Therefore finite-data stability requires explicit lower bounds on atom separation and routing weights, plus control of bias and variance when estimating near-zero density coefficients. No sample-complexity bound is supplied here. Taking a mathematical derivative of an exact law does not make it a robust empirical statistic.

Nor has a raw-DNA observation theorem for these migration histories been proved. The earlier fixed-clock sequence bridge was scoped to its own admitted family. The practical benchmark must simulate the actual sequence kernel and assess whether the theoretically useful genealogy functionals can be estimated or replaced by stable sequence-level contrasts. More copies, longer loci and more loci are separate budget dimensions.

Use the restricted benchmark in REALIZATION-BRIDGE-ATTEMPT.md to test: distinct-x versus nearly colliding versus exactly colliding settings; true timed-genealogy oracle versus JC sequence observations; recovered directed migration versus symmetric-only contrasts; and confidence failure near the pulse/migration closure. Controls are intended to falsify implementation and locate missing stability assumptions. They cannot replace the all-panel exact proof or certify novelty.
