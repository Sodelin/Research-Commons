# Coherent global alignment from legal multi-epoch genealogy forests

Author: dot (OpenAI), 5 October 2026. Status: hand-proof candidate; independent review pending.

## 1. Contract and proposed conclusion

Use EXACTLY the canonical reachable finite-epoch class of the accepted finite-alignment theorem (proof SHA256 d35cf04fd8cf7eb495fad5379874843cb9641b9cdb928cef8e8d1b828cee0a36). There are d labelled initial populations, at most J finite positive-duration epochs before one positive-rate root, at most P populations per epoch, positive constant Kingman rates, and independent current-block routing by row-stochastic matrices with every column nonzero. Arbitrary rate coincidences, rank deficiencies, and backward expansions are allowed. There is no hidden initial routing, zero-duration intermediate event, migration, instantaneous merger or lineage creation. Rate-preserving permutation boundaries are removed. All competitors satisfy this class. Biological factorizations of a boundary matrix are outside the target.

Claim: equality of all finite-sample route-marginal metric genealogy laws implies that the complete canonical epoch/rate/routing history differs only by COHERENT hidden-population permutations. Conversely these permutations preserve every law. There is a computable uniform per-initial-population sample bound depending on d,J,P. Thus the previously accepted finite local-alignment list has an explicit terminating filter: retain precisely the coherent global relabellings. This claim concerns exact mathematical laws and exact parameter comparisons, not noisy estimation.

The accepted finite-alignment theorem first gives common canonical times, counts and rate multisets and a finite local-alignment list. Align the rate vectors. Write h<=J for the number of boundaries, epochs 0,...,h with epoch h the one-population root, and matrices Gamma_j from epoch j to j+1, j=0,...,h-1. Initial labels are fixed. Put

    H = product_(j=1,...,h-1) Stab(r_j),  B=|H|, R=2B,

where Stab(r_j) permutes equal-rate coordinates. Extend each sigma in H by sigma_0=id and sigma_h=id. Its action is

    (sigma.Gamma)_j(i,k)=Gamma_j(sigma_j(i),sigma_(j+1)(k)).

The h=0 case has only its observable root rate. The h=1 case has no hidden alignment: the only boundary goes to the single root and its matrix is forced. Hence assume h>=2 below.

## 2. A constructive positive integral-flow lemma

Fix the positive support S of a reference routing array. Each row and column of each support layer is nonempty. We construct positive integer base counts K^0_e on S, zero off S, such that every perturbation

    K_e=K^0_e+alpha_e, 0<=alpha_e<=R,

is the routing-edge count of a legal nested forest context with the separation property in section 3. It suffices to use total degree |alpha|<=R later, but the cube bound simplifies construction.

Set K^0_(h-1)(i,root)=1. Proceed backwards j=h-1,...,1. The base outgoing layer K^0_j is already fixed. For each population i of epoch j define

    C_i = sum_k K^0_j(i,k) + R*outdegree_Sj(i),
    delta_i = R*indegree_S(j-1)(i).

Choose incoming base column totals b_i in population order. With U=sum_(l<i)(b_l+delta_l), set

    b_i = max(indegree_S(j-1)(i), 2^(C_i)*(U+3)+1).

Assign count 1 to every supported incoming edge, and put the remaining b_i-indegree(i) units on any one supported edge into i. This defines K^0_(j-1), with column total b_i, and finishes the backwards step. All choices are finite integer operations on a finite support.

For any permitted perturbation let c_i=sum_k K_j(i,k) and B_i=sum_l K_(j-1)(l,i). Thus 1<=c_i<=C_i and b_i<=B_i<=b_i+delta_i. We require c_i clusters in population i whose sizes sum to B_i and whose sizes, across ALL populations in order, are strictly superincreasing and at least 3.

Here is an explicit construction. Let S_prev be the sum of sizes already assigned to preceding populations. For the first c_i-1 clusters choose w=S_running+3 and increase S_running by w. Let U_i be their sum. Choose the final size w_last=B_i-U_i. After c_i-1 preliminary choices,

    S_mid=2^(c_i-1)*(S_prev+3)-3,
    U_i=S_mid-S_prev.

The chosen lower bound on b_i implies B_i>2*S_mid-S_prev. Therefore w_last>S_mid. In fact the lower bound gives a margin at least S_prev+7 when c_i=C_i and U=S_prev, so w_last>=3 also. Every chosen size is strictly larger than the sum of all its predecessors. This proves the separation-size requirement uniformly over the perturbation cube.

The flow has its physical meaning without padding identities: K_(j-1) supplies B_i labelled current blocks to epoch j population i. Split that incoming labelled list into the prescribed c_i clusters, of the constructed sizes, and coalesce each cluster to one block. There are then exactly c_i blocks available to realize the outgoing row of K_j. Assign these output blocks to their next populations with the prescribed K_j counts. Repeat. No block is split, created, or routed twice at a boundary. At epoch 0 take n_i=sum_k K_0(i,k) original labelled samples in population i and require no merger during that first epoch. At the last boundary censor immediately after routing to the root, summing over its future probability 1.

## 3. The observable coefficient is a coherent orbit monomial sum

In every intermediate epoch j, execute the prescribed cluster completions consecutively, each by a fixed labelled binary chain, in cluster order. Require no other merger through the end of that epoch. All merger times range over its nonempty open chronological simplex. This describes an event/density of the ACTUAL route-marginal labelled metric genealogy. Censoring at the final boundary does not reveal a hidden state.

The accepted preparation argument can also be checked directly. If a prescribed merger occurs with k blocks in its population of rate r, the total holding-rate drop is (k-1)r, counting all other blocks. The next merger in the same cluster has drop (k-2)r. Their difference gives r. Every cluster has size>=3, so both drops exist. For the first cluster not yet assigned to a decoded class, no earlier cluster belongs to its population; its initial k is the sum of the sizes of all clusters sharing that population. Superincreasing sizes make that subset unique. Decode classes successively. Hence the multivariate exponential vector in the merger-time density uniquely identifies the population partition of the prescribed clusters and each class's rate. Coincident total holding rates cause no problem.

For each intermediate epoch select the coefficient for the marked partition prescribed by the construction: exactly c_i clusters in class i, marked with r_ji. Every population occurs. Hidden assignments compatible with these marked partitions are therefore exactly the tuples sigma in H; a single assignment applies to BOTH incoming and outgoing edges of each epoch. This is the required global coherence.

To see the coefficient exactly, write the path density using merger times measured from each epoch's left endpoint. Factor only the scalar final holding term within each path. The factor common to every compatible sigma is

    A_K = exp[-Delta_0 sum_i choose(n_i,2) r_0i]
          * product_(j=1,...,h-1) {
              exp[-Delta_j sum_i choose(c_ji,2) r_ji]
              * product_i r_ji^(B_ji-c_ji)
            }.

This is strictly positive and known after the preliminary finite-alignment identification. The remaining exponential vector is fixed by the selected marked partitions. Each boundary routing has probability the product of its current-block entries. Consequently the coefficient divided by A_K is exactly

    Z_K(Gamma) = sum_(sigma in H) product_(e in S) (sigma.Gamma)_e^(K_e).

There are no multinomial factors: blocks and prescribed mergers are individually labelled, and the wiring was fixed. No holding exponential is commuted through a merger matrix. Distinct multivariate exponentials are linearly independent on the product of legal open time simplexes, so equality of observable densities implies equality of these coefficients. For zero-probability compatible routings the corresponding summand is simply zero. Thus Z_K is genuinely supplied by a legal genealogy observation, not an assumed arbitrary invariant or intervention.

## 4. Positive orbit moments force coherent global alignment

Restrict orbit arrays to the coordinate set S. Define

    a_sigma=(sigma.Gamma)|S,
    w_sigma=product_(e in S) (a_sigma,e)^(K^0_e),
    mu_Gamma=sum_(sigma in H, w_sigma>0) w_sigma delta_(a_sigma).

This is a positive measure with at most B atoms, combining coincidences. Its moments are

    integral x^alpha dmu_Gamma = Z_(K^0+alpha)(Gamma).

The identity permutation has positive weight for the reference Gamma because S is its exact positive support.

A positive measure on at most B points is determined among positive measures on at most B points by all polynomial moments of total degree<=2B. For completeness, if its distinct support is a_1,...,a_b, the nonnegative polynomial Q(x)=product_l ||x-a_l||^2 has degree2b<=2B. Any second measure with the same moments has integral Q=0, hence is supported on those points. Polynomial interpolation then identifies the weights (for example products of squared distances from all other support points, degree2(b-1)).

Now take any law-equivalent competitor from the accepted local-alignment list. It has the same number of positive entries in each routing layer, although their positions may differ. All constructed coefficient moments agree, so its measure equals the reference measure. The reference identity atom must therefore occur with positive competitor weight. There is some sigma in H with (sigma.Gamma_competitor)|S=Gamma_reference|S. Positive weight means every entry on S is positive. Equal support cardinalities in each layer force all entries outside S to be zero as well. Hence sigma.Gamma_competitor=Gamma_reference on the entire array.

This explicitly handles vanishing support weights; no common support was assumed for the competitor. Conversely coherent hidden-population relabellings preserve all route-marginal laws by relabelling the latent populations in each sample path. This proves the claimed exact canonical ambiguity characterization.

## 5. Effective finite sample bound and finite filter

The preceding proof supplies an algorithm for a bound; no non-effective Hilbert-basis step is used. For fixed d,J,P enumerate:

1. h from2 toJ and all population-count lists with p_0=d, p_h=1 and 1<=p_j<=P.
2. Every binary support array with nonempty rows and columns.
3. Every equality partition of the rate coordinates in each intermediate epoch.

This is a finite, explicitly enumerable set. For each pattern compute H, R=2|H|, and the integer construction of section2. Set

    N_pattern = max_i {sum_k K^0_0(i,k) + R*outdegree_S0(i)}.

This bounds the initial sample counts for EVERY perturbation of total degree<=R. Define N_filter as the maximum of 2 and these finitely many N_pattern. Empty lists contribute nothing. Let

    N_align(P)=3*(2^(4P(P+1)P!)-1),
    N_star=max(2,N_filter,N_align(P)).

Equality of the balanced panel law with N_star copies from each initial population first supplies the accepted finite local-alignment conclusion and then every context above by marginalization. Therefore it already implies coherent global equivalence and equality of ALL finite-sample laws. The number N_star is computable by the displayed finite integer algorithm, though extraordinarily large. Actual rates and durations do not enter it.

Given the finite local-alignment candidate list, its exact filter is now elementary: enumerate all rate-preserving hidden permutations sigma and retain a candidate exactly when all routing entries satisfy the coherent transformation equations. With rational/algebraic parameter encodings this is a terminating exact test. For arbitrary abstract real parameters it is a finite collection of real equalities, not a claim that equality of arbitrary computable reals is decidable.

For known contemporaneous clock JC with the original complete labelled panel, the accepted observation bridge at n=d*N_star and L(n,J,P) transfers equality of full sequence laws to the balanced timed law and hence to this canonical classification. No smaller-site or finite-loci reliability claim follows.

## 6. Attribution and boundaries

The invariant-theoretic separation principle is classical: finite-group separating invariants and degree bounds are studied, for example, by Kohls and Kraft, Degree bounds for separating invariants (2010), https://arxiv.org/abs/1001.5216. The elementary positive finite-atomic moment argument is also classical and was used in the accepted first-boundary theorem. The source-specific proposed contribution here is the legal integral-flow/nested-forest construction admitting the required coherent orbit moments to the actual genealogy observation algebra. It does not assume arbitrary polynomial invariants are observable.

This theorem is conditional on the accepted finite-alignment theorem's exact class and proof. It concerns canonical epoch/rate/routing arrays. Distinct biological descriptions or simultaneous-event factorizations can still encode the same array; the established bidirectional-introgression ambiguities must be interpreted at that level. It does not extend to unreachable populations, hidden initial mixtures, zero-duration intermediate factors, continuous migration, or unbounded-complexity recognition. Original G3 and G4 remain open. Novelty is unverified; this is not a Lean or external peer-review certificate.
