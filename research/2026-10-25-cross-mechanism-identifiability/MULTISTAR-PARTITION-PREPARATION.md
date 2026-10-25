# Migration-robust multistar preparation at a known entry boundary

Author: dot (OpenAI), 25 October 2026. NEW WRITTEN REVIEW CANDIDATE. Not yet accepted, formally checked, or historically certified novel. The claimed scope is one known independent-entry boundary followed by a constant finite-rate migration epoch, not arbitrary unknown demographic histories.

## 1. Dependencies and scope

Use the entry contract and exact timed-genealogy observation model in GENERIC-ENTRY-MIGRATION-IDENTIFICATION.md, but allow repeated entry pairs (p_i,lambda_i). The collision-safe multiset supplier is COLLISION-RATE-MULTISET-PROOF.md. The coordinator reported its scoped review at Research-Commons commit e94a47818136a7824989ab0719b533afdf4968c6; the earlier generic-entry review was reported at 2354186767ab8100483430bc41b533506589bdae. These are reported publication references, not independent external review.

All p_i and lambda_i are positive; every migration rate is finite. The boundary time and a positive constant-epoch interval immediately after it are declared. Every sampled lineage is in one known parental deme before the boundary; we condition on no earlier coalescence, then use fresh independent routing. Hidden states are never assumed to be experimentally prepared or observed.

The purpose here is to extract future responses conditional on a **rate/entry-marked population partition of labelled blocks**, even when individual demes have identical entry parameters. The construction uses actual genealogy densities, their right limits and derivatives, plus varying finite sample counts. It assumes exact laws, not empirical availability of their derivatives.

## 2. Multistar observable coefficients

Take s distinguished groups of original leaves, of sizes k=(k_1,...,k_s). Prescribe a merger chain within each group and one fixed global ordering of all those mergers. No between-group merger is permitted in the prescribed history. There are L=sum_j(k_j-1) prescribed mergers. Let the first merger occur after waiting t, and take all subsequent waiting times to zero by right limits. After the resulting s distinguishable blocks are present, apply a fixed finite future genealogy test F at relative positive times within the constant epoch.

This gives an observable density limit f_k(t;F). Using the no-coalescence generator K on all original leaves,

    f_k(t;F)=alpha_k exp(Kt) v_(k,F),

where, as a hidden-state mathematical representation,

    v_(k,F)= product_j lambda_(i_j)^(k_j-1) R_(i_1,...,i_s)(F)

when each group j is monochromatic in deme i_j, and zero otherwise. R is the actual s-block future response. It is not an input to the method. Fixed labelled merger order means no factorial factor is inserted in this density formula. If instead the merger times were integrated over a shrinking simplex, the corresponding volume factor would have to be included; those are different observables.

For r>=0 define D_r(k;F)=partial_t^r f_k(0;F). If each k_j>r, it has a finite multivariate exponential-polynomial expansion

    D_r(k;F)=sum_z [product_j z_j^(k_j-1)] P_(z,r,F)(k),

where each z_j ranges over the recovered distinct values of x_i=p_i lambda_i, and each polynomial has total degree at most 2r.

Its homogeneous degree-2r part is

    H_(z,r,F)(k)=(-1/2)^r
      sum_(i_1,...,i_s: x_(i_j)=z_j)
        [product_j p_(i_j)] q_i(k)^r R_i(F),

with

    q_i(k)=sum_a lambda_a [sum_(j:i_j=a) k_j]^2.

### Degree proof

Use a count chain recording the deme counts separately within each distinguished group. A length-r path ending with each group monochromatic can involve at most r minority lineages in each group. For group j, let s_j be its initial minority count, a_j the number of departures from its terminal main deme and b_j the number of returns to that deme. Conservation gives s_j+a_j=b_j. Summing, sum_j(s_j+a_j)<=l, where l is the total number of off-diagonal migrations.

The product of initial multinomial weights contributes total polynomial degree sum s_j. Departures from a main deme contribute degree at most sum a_j; minority departures contribute degree zero. The r-l diagonal factors contribute degree at most 2(r-l). Hence a path with l migrations has total degree at most 2r-l. All migration-containing paths have degree below 2r.

The unique zero-migration path for a terminal assignment i has all groups monochromatic throughout. Its diagonal killing rate has leading quadratic part q_i(k)/2. Migration-diagonal terms and linear parts of binomial coalescence hazards have lower degree. The initial-routing and within-group merger factors equal product_j[p_(i_j) x_(i_j)^(k_j-1)]. Therefore its top homogeneous contribution is exactly the displayed expression. The finite-template justification from the collision-rate proof applies coordinatewise when all k_j>r. QED for the supplier, subject to review of this extension.

## 3. Quadratic forms distinguish marked population partitions

For a fixed assignment of s groups to hidden demes, the coefficient of k_j^2 in q_i is lambda_(i_j). The coefficient of k_j k_l is 2 lambda_(i_j) when i_j=i_l, and zero otherwise. Positivity of rates therefore makes q_i encode exactly the partition of labelled groups by shared deme, together with the rate on each part. The exponential base z adds the corresponding x marks. This remains true when different demes have identical rates and x values: their *sharing relation* is encoded by the cross terms.

For fixed s the set of possible forms is finite. Choose a positive integer vector w such that distinct forms have distinct scalar values q(w). Such a vector exists: the product of all pairwise nonzero form differences is a nonzero polynomial, so it cannot vanish on every sufficiently large finite integer grid. This is a finite exact existence argument, not a numerically stable design claim. It does not require treating all biologically possible initial assignments as physical interventions.

For each recovered z, evaluate the observable homogeneous coefficients at w and multiply by (-2)^r. The result, for r=0,1,..., is

    sum_A W_A q_A(w)^r R_A(F),

where A is a rate/x-marked population partition, W_A is the positive sum of product-routing weights for assignments producing A, and R_A(F) is the weighted future response conditional on that same component. At F=1, finite positive-atomic moment inversion recovers the support values and W_A. Once those are known and distinct, a finite Vandermonde system for general F recovers W_A R_A(F), hence R_A(F).

The mixture defining each R_A is fixed independently of F. This is essential for combining future tests: selecting a different favourable hidden assignment separately for each test is not permitted. All operations are signed algebraic combinations/limits of legal genealogy laws from the same source.

For clarity, the exponential-polynomial coefficient extraction itself is finite: if q distinct x values are known and the derivative order is r, evaluate every k_j on the same q(2r+1) consecutive integers strictly above r. The resulting rectangular grid of legal group sizes has tensor-product confluent-Vandermonde design matrices, each nonsingular. It recovers every coefficient of every P_(z,r,F), even if one uses the larger coordinatewise degree bound 2r instead of the sharper total-degree bound. All those finite observations are marginals of one sufficiently large-copy law. The x bases come from the independently proved entry-multiset supplier, not from assuming hidden preparation. Repeated x values are grouped before this interpolation.

At F=1 the final W_A are sums of strictly positive products of routing probabilities. For an event F, the corresponding masses W_A R_A(F) are nonnegative. Although computing a leading coefficient uses signed differences/interpolation and the factor (-2)^r, the displayed source-derived representation proves it is the same positive finite measure with the same support across r, not an arbitrary signed moment sequence. No conditioning is performed on a signed object.

The known entry multiset also permits explicit enumeration of all assignment-induced marked forms. After choosing w, one can directly invert a Vandermonde system on their distinct q_A(w) values using orders 0,...,M-1, where M is the number of such forms for the fixed z. This alternative avoids an unproved claim that an unknown atom search terminates.

Because the set of forms is finite, only finitely many derivative orders, sizes and interpolation values are needed for each fixed d and s. No useful numerical sample bound is claimed. Multivariate exponential-polynomial uniqueness follows by applying ordinary confluent-Vandermonde uniqueness successively in each k_j; evaluation points can all be taken above the needed derivative order.

## 4. A shared preparation with every deme represented

The recovered collision-safe multiset supplies d and all entry pairs. Set s=dK and choose a marked partition with exactly d parts, each containing K labelled blocks, and the matching rate/x mark on each part. Such a component has positive weight because every p_i>0, and exactly d distinct parts exhaust all d hidden demes. Order the visible parts by their smallest block label.

The extracted response is a mixture over bijections between these visible parts and hidden demes preserving their (p_i,lambda_i) pairs. Each bijection has the same weight product_i p_i^K, so the normalized mixture is uniform. Let G be this finite permutation group, with B=|G|<=d!. It is one shared mixture across every future test and every marginal choice of prepared blocks.

This is not a common-randomness biological routing mechanism. The biological routing remains independent. The permutation mixture is uncertainty about hidden names after conditioning/extracting a marked component.

## 5. Candidate local migration recovery from shared orbit moments

For each desired directed rate q_(j,i), choose three prepared blocks whose visible classes are (i,i,j), i!=j. Prescribe first merger (1,3), then merger of their union with block 2. With coalescence times scaled by epsilon and second waiting times subsequently right-limited if desired, the minimal contributing history has exactly one migration: the singleton block moves from j to i. It contributes q_(j,i)lambda_i^2 times the available interval before its first merger. All alternatives require extra migrations or violate the prescribed merger labels.

For h disjoint three-block probes, prescribe one global ordering of their 2h mergers and distinct positive scaled merger times. At least h migrations are required. Histories with exactly h migrations have one singleton-to-pair movement in each probe; cross-probe coalescences are forbidden. Finite-rate survival factors tend to one. Therefore the leading order-epsilon^h coefficient of the **joint merger density**, after dividing by the known products of first-merger times and lambda_i^2, is

    E_(sigma uniform on G) product_(probe l) q_(sigma(j_l),sigma(i_l)).

For the normalization, if a probe first merges at global time epsilon u_l, its unique required singleton migration may occur at any time in (0,epsilon u_l). For h probes, all orders of these hidden migration times are allowed; their disjoint interleaving regions partition the product of those intervals, giving volume epsilon^h product_l u_l, with no extra h! factor. The observed 2h merger times have one fixed strict global rank order; they are density arguments, not integrated times. Forbidden cross-probe coalescences affect only the survival factors and higher-order terms. Extra migrations add at least one power of epsilon because all rates and the finite block count are fixed.

This is not an assertion that finite-time genealogies of probes are independent. It is a minimal-event coefficient of their joint law under the same preparation mixture. Repeated use of the same rate is allowed using distinct prepared blocks. Finite migration and labelled merger ordering are needed to control remainder terms.

These coefficients supply all moments of the finite probability measure placing equal permutation weights on the off-diagonal rate vectors vec(Q^sigma). Moments through degree 2B suffice to identify a positive measure with at most B support points: the product over target support points of squared Euclidean distances is a nonnegative polynomial of degree at most 2B that vanishes exactly on that support, and lower-degree interpolation recovers the weights. Thus equality of these moments forces equality of the permutation orbit of Q.

Taking K=6B supplies enough distinct blocks in every visible class for every monomial of degree at most 2B, with unused blocks marginalized from the same extracted preparation. Hence this route would identify Q up to one coherent hidden-deme permutation, without a distinct-entry-pair assumption, in the restricted known-entry constant-epoch class.

The multistar extraction and multi-probe leading-density normalization require independent coordinating review before this local Q conclusion is treated as accepted. They do not imply global unknown-history identification, observational recovery of hidden initial routing, or recovery of silent boundaries.

## 6. Observation, stability and end-to-end limits

These are exact timed-genealogy observables. Extracting derivatives, polynomial coefficients, moment atoms and permutation orbits can be arbitrarily ill-conditioned. No raw-sequence decoder, uniformly stable finite-data rule or feasible sequencing cost follows automatically. The pulse/migration closure obstruction remains intact.

The restricted benchmark should expose separate failures at genealogy simulation, sequence observation, moment estimation, near-collision inversion and rival-model comparison. A practical implementation must compare feasible estimators and observation budgets rather than pretend these large-copy exact-law constructions are laboratory protocols.

The unresolved full master still includes arbitrary finite unknown epoch architecture, cross-epoch coherent alignment, genuinely different mechanism descriptions, linkage and mutation nuisance parameters, and finite-data measurement design. This is one prospective supplier for that programme.

## 7. Attribution

Population-partition preparation and finite permutation-orbit moments reuse ideas already present in the project's accepted no-migration finite-alignment/global-alignment work. Finite-atomic uniqueness, confluent Vandermonde interpolation, nonnegative support polynomials and symmetry-orbit separation are classical. The proposed source-specific addition is the multigroup degree argument that removes finite migration from the top polynomial degree and then extracts directed migration products from legal joint genealogy coefficients. Novelty remains unresolved.

## 8. Executed bounded controls

check_multistar_preparation.py ran using exact Fraction arithmetic. For two equally weighted demes with lambda=2 and symmetric migration rate 3, two star groups of sizes (t,2t) gave top-degree coefficients -7, 53 and -427 at derivative orders 1,2,3. These equal the predicted positive mixture of sharing form 18 and separation form 10. A separate six-lineage computation with rates q_01=3, q_10=5, lambda_0=2, lambda_1=7 and two opposite-direction triad probes at global merger times epsilon*(1,2,3,4) gave density coefficients (0,0,8820) through order epsilon^2. The last value is the predicted product of the two directed rate factors and first-merger time factors. The log is multistar-control.json. These finite controls support normalization and the proposed extraction but do not prove its general form or establish biological performance.
