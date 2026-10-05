# Source-dependent quantitative reliability after canonical identification

Author: dot (OpenAI), 5 October 2026. Status: new hand-proof candidate awaiting independent review.

## 1. Purpose, inherited results and experiments

This uses the same homogeneous mutation-scaled clock-JC channel and independent current-block MSci routing as the accepted canonical-history theorem. It does not change to genotypes, unknown locus-rate mixtures, migration, or flag observations. Loci are independent draws from ONE shared source. Multiple sites within a locus share its genealogy.

Two results below distinguish the full positive model class from explicit margin domains. First, no fixed finite sampling budget uniformly resolves canonical parameters over the whole class, even though its exact-law identifiability has been proved. Second, on declared bounded margin domains, a source-specific forward coupling bound supplies a mathematically terminating algorithm for a strictly positive inverse separation modulus. Standard confidence inversion then supplies error-tolerance and confidence guarantees.

The statistical principles are inherited, not new: G6 `research/2026-10-01-g6-effective-certification/PROOF.md`, sections4.4,4.6–4.9, immutable commit5d965cf4695e266352a7eeed1d1addae831ee058, supplies effective image clouds, confidence inversion, channel contraction, rare-switch/nonuniformity arguments and the conservative coordinate concentration bound. Its source class and finite target differ from this MSci parameter problem; its source-specific graph compression is NOT imported. The present new obligation is the MSci-specific forward modulus and effective inverse separation on the stated parameter domains. The accepted global classification and clock-JC finite observation bridge supply injectivity; they are not re-proved here.

## 2. Canonical parameter distance

Fix known labelled initial populations d and finite upper bounds J,P as in the accepted global classification. A shape lists the population counts of the canonical positive-duration epochs, ending at one root. For one shape use the vector of all finite durations Delta, population pair rates r, and routing entries Gamma. Hidden populations may be permuted coherently; initial names remain fixed. Define rho between two histories of the same shape as the minimum, over those coherent permutations, of the coordinate-sup distance, clipped at1. Histories of different shapes have distance1. This is a metric on canonical histories modulo hidden names. All error tolerances below satisfy 0<epsilon<1.

This distance measures the canonical stochastic history, not alternative biological interpretations of its boundary matrices. It deliberately charges a persistent population-rate discrepancy even when that population is rarely occupied.

## 3. Full-class fixed-budget impossibility

Take one initial population of rate4 up to time1. At time1 expand into two populations by the row (1-q,q), where 0<q<1/2. The common population has rate1; the rare population has rate2 in source A_q and rate3 in source B_q. Both join a root of rate5 at time2. This is an admitted positive-duration, reachable, independent-routing canonical history with two boundaries and at most two populations. There is no hidden initial routing. Both histories have rho=1: the aligned rare rates differ by1, and swapping the two intermediate names cannot reduce the sup discrepancy below1.

For a locus with n labelled initial samples, let k<=n be its surviving current-block count at time1. Couple the prehistory, all current-block routing coins, common-population clocks and root clocks. The rare population's rate cannot affect the genealogy if it receives at most one block. Therefore

    TV(G_Aq,G_Bq) <= Pr(Binomial(k,q)>=2)
                     <= binom(n,2)*q^2.

The final inequality uses a union bound over pairs of routing coins and holds after averaging over k. It concerns the complete labelled metric genealogy, not just a finite statistic. The JC channel contracts TV, so the same upper bound holds for every within-locus site length, however large. For m independent loci with at most n samples each,

    TV(data_Aq,data_Bq) <= m*binom(n,2)*q^2.

More generally sum binom(n_l,2)*q^2 over a specified finite design. A decision procedure estimating rho to error epsilon<1/2 with probability at least1-delta at BOTH sources would give a two-point test with error at mostdelta. The classical testing lower bound requires

    m*binom(n,2)*q^2 >= 1-2delta.

For every fixed finite design and 0<delta<1/2 this fails when q is sufficiently small. More sites cannot repair the absence of a rare joint-routing event. This is loss of uniform finite-budget reliability, not a collision of exact observation laws or a denial of pointwise consistency.

A second example shows why inheritance floors alone do not suffice. Fix q=1/2, keep the first boundary at1, and put the root join at1+a with a>0. Compare rare rates2 and3 as above. Couple the rare population with common rate2 clocks plus rate1 extra clocks. A mismatch before the join has probability at most binom(n,2)*a. Thus TV of each complete genealogy, and any sequence observation, is at most that quantity. The histories remain rho=1 while a tends to zero through legal positive durations. The same fixed-budget testing obstruction follows. These examples are model-specific instances of the inherited coupling/two-point principles.

Three further legal families explain the other conditioning knobs for this full-history metric:

- **Near-silent boundary:** one population throughout, root rate2 beginning at time2. Before an intermediate boundary the rate is1 and afterwards1+z, with0<z<1/2. Compare boundary times1/2 and3/2. The duration vectors are distance1 apart, but rates differ between sources only for one time unit and only byz. Common/extra-clock coupling gives genealogy TV at most binom(n,2)*z. All finite durations and rates remain bounded away from zero; the canonical boundary is genuinely visible for everyz>0 but its visibility tends to zero.
- **Vanishing coalescence rates:** use the two-boundary expansion/join history at times1,2, with initial rate1, both intermediate ratesz>0, and root rate5. Compare routing rows(1/4,3/4) and(1/2,1/2). Their canonical distance is1/4, even after hidden permutations. If neither process merges in the intermediate epoch, their shared prehistory and root completion coincide regardless of routing. Thus genealogy TV is at most2*binom(n,2)*z. Routing and duration margins stay fixed.
- **Late or rapidly coalescing initial epoch:** use those same two routing rows, intermediate rates1,2 and root rate5. Give the initial population rate1 up to a first boundary at timeT, then join atT+1. By initial-population pair projectivity, each original pair remains uncoalesced atT with probability exp(-T). A union bound gives probability at most binom(n,2)*exp(-T) that the sample MRCA has not already occurred. Once only one tracked block remains, the subsequent demographic history cannot affect the sample-MRCA-rooted metric tree. Hence this is an upper bound on the two genealogy laws' TV, while their canonical distance remains1/4. Alternatively keep the first boundary at1 and take its initial pair rateR tending to infinity; the same bound is binom(n,2)*exp(-R).

All bounds transfer through the common sequence channel and multiply at most linearly over independent loci. They show explicit failures when the visibility margin, lower rate bound, duration upper bound, or rate upper bound is dropped. They do not assert these particular rectangular-domain restrictions are the only possible useful assumptions, nor that every functional becomes hard at every boundary.

## 4. Explicit domain knobs; no substitution of the full class

The positive result applies to the following DECLARED subset, not to the full class of section3. Choose rational constants

    0<a<=b, 0<r_min<=r_max, 0<eta<=1, 0<v<=1.

Require each finite duration in[a,b], each population pair rate in[r_min,r_max], and each routing entry either0 or at leasteta. Every routing row sums to1 and every output column is nonzero. For each square boundary, require

    min_(permutations pi) max(
        ||Gamma-P_pi||_infinity,
        ||r_new permuted by pi - r_old||_infinity
    ) >= v.

The convention for P_pi and the rate permutation is the same row-to-column matching. This enforces separation from a silent rate-preserving permutation boundary. Nonsquare boundaries automatically change the population count and need no such comparison. Equal rates and rank deficiencies are allowed. All histories remain in the canonical reachable class. Empty parameter domains are detected by rational feasibility and are vacuous.

For each fixed shape and support, the domain is a finite union of compact rational polytopes: rate, duration, stochastic and entry constraints are linear; each max>=v and finite minimum condition can be expanded into finitely many linear alternatives. There are finitely many shapes and supports. Thus the whole domain is a computably compact finite union of polytopes, modulo the finite coherent permutation action. None of the constants a,eta,v is asserted to be bounded away from zero over the original full source class.

## 5. Source-specific forward total-variation modulus

Fix a shape, n labelled sampled copies in total, and two sources in the above bounds with coordinate differences at most d_r,d_Gamma,d_Delta after a chosen common naming. Let C=binom(n,2). Their COMPLETE timed genealogy laws satisfy

    TV(G_theta,G_theta') <=
       [C*J*b + (n-1)/r_min]*d_r
       + n*J*P/2*d_Gamma
       + C*r_max*J*(J+1)*d_Delta.             (1)

The right side may be clipped at1. Hence the same inequality holds after any common fixed observation channel, in particular the entire clock-JC locus law at any site length.

Proof. Couple initial lineages and all current-block routing draws. At one boundary the total variation between two probability rows is at most P*d_Gamma/2; at most n current blocks route there. Summing over at most J boundaries gives the second term.

Write t_j,t_j' for corresponding boundary times. Their displacement is at most j*d_Delta, so the union of the closed intervals between corresponding times has length at most J(J+1)*d_Delta/2. Forbid coalescences in either source during this union. Its total bad-event probability is at most 2*C*r_max times that length, giving the third term. On its complement current blocks are unchanged while differently timed routing operations occur, so their coins can be paired by boundary index and block identity. Even when these windows overlap, after leaving their union both histories have applied the same ordered boundary operations; no unobserved conditioning or new intervention is used. This is only a path coupling.

Outside these windows, whenever populations and partitions match, use common Kingman clocks at the smaller pair rate and extra clocks of rate at most d_r. Until the later root time, which is at most J*b, the total extra intensity is at most C*d_r. This gives C*J*b*d_r.

After both histories enter the root, couple its two homogeneous pair rates. At each remaining merger stage, the probability of an extra-clock event before a common event is at most d_r/r_min, since the binomial number of available pairs cancels in the ratio. There are at most n-1 stages, giving the final root term. If no charged event occurs, the full labelled merger histories and merger times agree. The coupling inequality proves(1). It is valid at tied rates and rank-deficient matrices.

Define the explicit constant

    K = C*J*b + (n-1)/r_min + n*J*P/2
        + C*r_max*J*(J+1).

Then a sup-coordinate cell of diameter h has observed-law TV diameter at most K*h, and probability-coordinate-sup diameter at most K*h. This is an actual-source bound; a grid cell never independently fits its epochs or experimental rows.

## 6. A terminating inverse-separation algorithm

Use the accepted computable canonical-identification sample cap N_star(d,J,P) and its full balanced panel n=d*N_star, followed by the accepted clock-JC bridge length L(n,J,P). Let p_theta be the complete sequence-locus distribution on its finite alphabet of D=4^(n*L) patterns. The same construction can use any separately proved smaller injective panel/site provider for a declared subfamily; it may not simply assume one.

For clarity, the accepted constructive site provider uses

    S=Bell(n)*P^n, E=sum_(i=0,...,n-1) binom(n,2)^i,
    F=J*S^2+S, M=E*(n*E*S)^J,
    L(n,J,P)=4^(n-1)*[2*M*(2*F+1)-1].

Its theorem SHA256 is3430171e587360460219ab78549538dcce7ef395a6a6502795842893de1f33fa. The global copy-cap construction is the finite integer algorithm in theorem SHA2560c512573e097fbc8729860a47f0beeea29bdd0d9f6b66a7390daa84398430646. Thus neither experiment dimension relies on the earlier non-effective Hilbert-basis argument.

The entries of p_theta at rational parameter points are computable with certified error: the accepted bounded-network forward formula consists of finite sums/products, positive-denominator expressions and exponentials, including the positive root tail. Alternatively its finite-state generator recursion gives the same certified calculation. Equal rates are permitted by the accepted forward-map proof. At rational grid representatives, all algebraic rate/routing operations in that formula are rational; exponentials of rational rate-duration combinations admit certified rational enclosures, for example by Taylor bounds and range reduction. The path-comparable denominator factors are positive sums of coalescent rates and nonnegative Fourier killing contributions; zero-reward terminal terms are handled separately by the provider. Thus no undecided resonance, exponential equality test or hidden numerical oracle is required. The present task does not claim that this exponentially large computation is practical.

For a requested rational epsilon in(0,1), consider all pairs in the declared domain satisfying rho(theta,theta')>=epsilon. Within shape pairs this constraint is, after enumerating coherent permutations and absolute-value alternatives, a finite union of rational polytope constraints. Between distinct shapes it is automatic. Thus the pair set is effectively compact. If it is empty, every pair is already within the requested resolution and no separation test is needed.

Otherwise, refine rational coordinate grids with mesh h tending to zero. Intersect every pair-cell with the admissible pair set by exact rational linear feasibility after expansion into its finite polytope union. Discard empty cells, and select an actual rational feasible representative pair from every nonempty cell. Compute

    f(theta,theta')=||p_theta-p_theta'||_infinity

at each representative with certified error at most tau, with tau tending to zero. The forward bound(1) implies that f varies by at most2*K*h over each pair-cell. Therefore

    lower(h,tau) = min_representatives (computed_f - tau - 2*K*h)

is a certified lower bound on the minimum separation over the entire admissible pair set. Stop when it is strictly positive, and return any positive rational Delta below it.

Why does this algorithm terminate? The accepted canonical theorem and finite sequence bridge make f strictly positive on the rho>=epsilon pair set. Continuity and compactness give a strictly positive minimum. The certified grid bounds converge uniformly to it by(1), so the lower bound eventually becomes positive. This uses neither an exact transcendental equality oracle nor an unknown Noetherian stabilization index. It does use the newly established injectivity theorem and the supplied domain margins.

The returned Delta certifies the concrete inverse implication

    ||p_theta-p_theta'||_infinity < Delta
        implies rho(theta,theta') < epsilon

for every pair in the declared domain. For finite comparisons, use a forward grid with K*h<=Delta/16 and an ACTUAL admissible rational source representative in every nonempty source cell. Approximate each representative's probability vector by a rational simplex point q with coordinate error at mostDelta/16. This can be done with certified rational coordinate enclosures and rational linear feasibility enforcing nonnegativity and sum1. The resulting rational cloud approximates every admissible observation law withinDelta/8 and each cloud point has a bound actual-source witness. The proxy q is not itself claimed to be an exactly realized law. All source parameters remain shared; both errors are charged.

## 7. Inherited finite-locus confidence guarantee

For any rational confidence error input 0<delta<1 and the returned Delta, the G6 section4.9 coordinate concentration bound gives

    m >= 32*Delta^(-2)*log(2D/delta)

independent loci as a conservative sufficient budget for coordinate radius at mostDelta/8. Take a rational integer ceiling with outward rounding. Compare the empirical locus distribution with the rational cloud from section6, retaining its points q within Delta/4 in coordinate sup norm. These are exact rational comparisons, including equality; no transcendental threshold decision is required. On the simultaneous coverage event, a point withinDelta/8 of the true law survives. For every retained q, its bound actual-source representative has observation-law distance at most

    Delta/16 + Delta/4 + Delta/8 = 7Delta/16

from the true law, and hence parameter distance belowepsilon. Selecting that actual source witness gives error belowepsilon with probability at least1-delta. Enlarging to its retained source cell adds at mostDelta/16, so the entire resulting parameter region is still withinDelta/2 in observation distance of the true law on the coverage event, and includes the truth. Incomplete probability computation excludes nothing until the declared enclosures are finished.

This is a specialization of the inherited confidence-inversion argument, not a new concentration inequality or a claim of minimax optimality. It gives a mathematically computable design/certificate, not a useful numerical budget at these worst-case bounds. The rare-route and short-epoch examples explain why no domain-free uniform budget can replace it. No fixed95-percent target is imposed. The probability inequality also holds for real delta in(0,1), but an algorithmic budget requires a supplied computable value; rational delta is the explicit input contract here.

## 8. Status and remaining practical task

The candidate supplies explicit source-specific forward conditioning, a terminating inverse-modulus computation and a declared-domain application of existing finite-data certification. It leaves efficient implementations, tighter useful bounds, dependence and misspecification contracts, unknown rate mixtures and phase-coarsened data to their own obligations. The original G3/G4 source-recognition questions are unchanged. Classical net, testing, concentration and channel methods must retain their attribution; novelty of the present application is unverified.
