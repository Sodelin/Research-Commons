# Finite COMMON displayed-tree covariance laws admit a joint moment certificate

Contributor: Codex role 5, 8 October 2026. SOURCE/HAND CANDIDATE, unreviewed. No compiler, CI, QE execution, source search or original-source edit. This is an arbitrary-cap, unknown-size positive certificate at the precise private root-output contract below. It is not full original G4 closure: original public-type admission of its diagonal probes and all shared/multi-output contracts are explicit transfer gates, and INDEPENDENT routing is not covered. Historical novelty was not assessed.

## 1. Original obligation and the source class actually used

The original G4 master fixes one positive finite source and asks for a target-derived finite legal certificate against every unknown-size admitted rival. Exact finite-cap testing or a supplied rival count is insufficient. We reuse the accepted single-COMMON-chain sparse-moment certificate in ASTRA `ALL-CAP.md` Section 4, rather than presenting it as new, and investigate joint extension to a whole finite branching source.

For this theorem a source has d labelled lower population entries and ONE ancestral output, natural COMMON inheritance, and no external shared register. Its admitted finite root-retained graph and parameters are unknown. Older input genealogies remain opaque. Every natural hybrid coin is private to this source, once per locus, independent of the input; one coin chooses the parent for all CURRENT roots at that hybrid. A finite authorized forcing/randomization row may be included when its joint finite configuration is private to the source. Different rows use the same actual source promise.

The mathematical input is its full multi-allocation no-merger diagonals. A physical test may supply these only if the root-extension construction in Section 7 is admitted by the ORIGINAL public type. This assumption is not a new forest oracle. Effectivity additionally requires explicitly usable exact algebraic values for these finitely queried responses, as in the inherited COMMON-chain stopping branch. Arbitrary-real Cauchy values do not supply the RCF operations below.

Rivals range over every finite strictly positive source under this same contract, without a size, arm-margin or atom-count bound. At every root allocation and row, one physical tuple remains shared. The target is finite; therefore conditioning on all its finitely many natural/common and private forcing choices yields finitely many ordinary displayed trees. Deleting unused arcs and suppressing unary vertices leaves the labelled rooted tree and an optional stem to the output. Population durations add along a suppressed path. All surviving durations are finite; every pendant duration is strictly positive.

For a displayed tree let `T_i` be the total duration from lower entry i to the output and let `U_ij` be the duration of the common path from the MRCA of entries i,j to that output. Then `T_i>0`, `0<=U_ij<min(T_i,T_j)`. Set

    a_i=exp(-T_i) in (0,1),  z_ij=exp(-U_ij) in (0,1].

There is one finite positive atom law μ on these labelled coordinates. On the event of no merger, each edge carries exactly the sum of the allocated current roots below it. Consequently the actual source diagonal for allocation `n=(n_1,...,n_d)` is

    D(n)=integral [ product_i a_i^binom(n_i,2)
                    product_(i<j) z_ij^(n_i n_j) ] dμ.          (1)

This is an exact COMMON conditional-source identity, not a product of separately averaged paths. No negative population is introduced. The same μ is used at every allocation. A common source with no hybrids is the one-atom case. The diagonal law of an INDEPENDENT current-root source does NOT have this finite displayed-tree representation.

## 2. First force all diagonal coordinates onto finite grids

Allocation `n=k e_i` gives

    D(k e_i)=integral a_i^binom(k,2) dμ.

The inherited sparse Chebyshev exposing-polynomial procedure terminates for each finite target marginal. It uses a nonzero nonnegative polynomial in the sparse exponents `0,1,3,6,...`, with zero expected value. Its finitely many positive roots form a grid A_i containing every rival's possible a_i. A rival's duration is finite and positive, so a_i=0 and a_i=1 are excluded if a computed polynomial also has endpoint roots. Remove such roots from the admissible grid, and keep all remaining roots initially; there is no need to select the true target atoms in advance.

An exposing polynomial exists by the finite-atom target argument in the inherited theorem. For exact algebraic moment input, RCF supplies algebraic coefficients and algebraic finite roots. Some grid entries can have zero target mass. Their inclusion only enlarges a finite grid and does not affect soundness. Every rival matching the finite exposing prefix has its SAME joint law supported on the product of these grids. Marginal support certificates imply this joint support statement by positivity.

## 3. An eventually invertible interpolation matrix isolates cross moments

Fix entries i,j. Write their diagonal grids as distinct positive values

    A_i={a_1,...,a_r}, A_j={b_1,...,b_s}, D=rs.

For every positive integer N divisible by `lcm(1,...,D)`, query allocations

    n_i=c, n_j=N/c, all other n_l=0, c=1,...,D.

The cross exponent `n_i n_j=N` is identical in every row. Define

    M_N[c,(a,b)]=a^binom(c,2) b^binom(N/c,2),
    h_N(a,b)=integral 1{a_i=a,a_j=b} z_ij^N dμ.

Equation (1) gives the EXACT finite system

    (D(c e_i+(N/c)e_j))_(c=1,...,D) = M_N h_N.                (2)

**Interpolation lemma.** `M_N` is invertible for every sufficiently large N along the indicated multiples.

Proof. Expand its determinant over assignments of the rs columns to distinct rows c. A term's N-dependent exponent is

    N^2 sum_c log(b_(assigned c))/(2c^2)
       -N sum_c log(b_(assigned c))/(2c),

and its remaining coefficient is a product of `a^binom(c,2)`. The weights `1/c^2` strictly decrease. Rearrangement therefore maximizes the quadratic coefficient precisely when the largest b values occupy the smallest rows, with r contiguous rows for each b. These assignments have the SAME linear coefficient, since b is constant within each assigned block. Summing them produces, up to one fixed sign and positive b factors, a product of generalized Vandermonde determinants

    det[a_l^binom(c,2)]_(c in its r-row block, l=1,...,r).

Each is nonzero because its exponents strictly increase and its a values are distinct positive numbers. This is the same sparse-monomial zero bound used in the inherited Chebyshev theorem. If a grid has one member the corresponding determinant is a nonzero scalar. Every other assignment has a strictly smaller quadratic coefficient; its linear contribution is only O(N). Thus all nonmaximal terms are exponentially smaller than this nonzero leading coefficient, and cannot cancel it for sufficiently large N. This proves the lemma. Logarithms are a proof device only; effective testing uses exact algebraic powers and determinants.

Hence each pair's conditional power moments are effectively extractable for all sufficiently large multiples N, by querying (2), checking the exact determinant and solving the finite system. No common parameter is fitted independently in different rows.

## 4. Positive conditional moment certificates force every cross coordinate

Let `L=lcm(1,...,D)`. Choose integers R,K for which all matrices at N=`L(R+l)`, `l=0,...,K`, are invertible. Equation (2) supplies, for each diagonal grid pair (a,b), the consecutive moments

    h_(L(R+l))(a,b), l=0,...,K.

They are the ordinary moments of the positive finite measure obtained by setting `v=z_ij^L` and weighting the original conditional measure by `z_ij^(LR)`. Every physical rival has z_ij>0, so this weighting preserves its support.

If the zeroth extracted moment `h_(LR)` is zero, positivity and z_ij>0 force that entire grid-pair branch to be empty for every matching rival. Otherwise normalize by it. Search for a nonzero polynomial p(v), nonnegative on `[0,1]`, whose expectation under those moments is zero. This is a finite RCF formula, with a coefficient normalization excluding p=0. On success, positivity forces v, and hence z_ij, onto the finitely many positive roots. Endpoints z_ij=1 are allowed; z_ij=0 is excluded by finite duration.

Termination does not rely on a known atom count. Every target conditional branch has finite support. A product of squared factors at its distinct v atoms is a nonnegative exposing polynomial of finite degree. For that degree, the interpolation lemma supplies some R for which the entire required consecutive block is invertible. Enumerating `(R,K)` dovetailed, evaluating each finite exact formula, therefore eventually finds certificates for every nonempty branch, and zero-mass certificates for the others. Algebraic input supplies algebraic polynomial roots and effective algebraic z_ij roots. No numerical logarithm comparison or finite-source extraction is required.

Perform this for every pair i,j. Every matching rival's joint latent covariance law is then supported on ONE finite Cartesian grid G in all a_i and z_ij coordinates. Correlations are not discarded: this only establishes finite joint support. Recover them next.

## 5. Recover the entire joint atom law on that finite grid

Distinct coordinate tuples in G correspond to distinct real symmetric covariance matrices A with diagonal T_i and offdiagonal U_ij. Choose a positive integer vector v so that the finitely many numbers

    alpha_A = product_i a_i^(v_i^2)
               product_(i<j) z_ij^(2 v_i v_j)

are distinct. Such a vector exists: equality for two distinct tuples is the zero set of one nonzero real quadratic polynomial in v after taking logarithms; a finite union of these zero sets cannot contain all positive integer vectors. An elementary induction on variables, or the nonzero polynomial's finite integer-root property after fixing other variables, supplies that last fact. Search integer vectors with exact algebraic product comparisons; this halts. Logs again justify existence only.

For allocations n=k v the coefficient of atom A is

    alpha_A^(k^2/2) beta_A^(k/2),
    beta_A=product_i a_i^(-v_i).

Evaluate the coefficient by its original INTEGER powers in (1), so no half-power convention or transcendental arithmetic is needed. With J=|G|, use k=H,H+1,...,H+J-1. After factoring a positive column constant, the determinant expansion's H-dependent exponent is `H sum_r r log(alpha_(assigned r))`. Strictly distinct alpha values make its maximal assignment unique by rearrangement. Its coefficient is nonzero, and every other term is exponentially smaller. Thus the matrix is invertible for sufficiently large H. Exact algebraic determinant testing finds such an H.

Solve that finite system for every joint grid weight. The promised target supplies a consistent nonnegative solution, and every rival matching those rows has EXACTLY the same solution. This recovers the entire joint finite covariance law, including dependence among all entries and correlations caused by shared COMMON choices within this private source. No external product of marginal atom measures was substituted.

## 6. Why this law determines every ordinary displayed-tree kernel

A valid displayed-tree covariance matrix records the root-to-MRCA shared durations U_ij and the root-to-leaf durations T_i. Its threshold clusters recover the labelled rooted hierarchy. The optional common stem is `min_(i<j) U_ij`; subtract it to locate the displayed MRCA. Internal edge durations are differences of successive cluster levels; pendant durations are the corresponding T_i minus its parent's level. Thus a valid tuple determines the ordinary population tree and all its capped forest tensors, including every opaque earlier input genealogy, up to unary path subdivision and arm descriptions that do not change the kernel.

These comparisons and reconstructed survivals use algebraic coordinate ratios. For example an internal edge survival is `z_child/z_parent`, and a pendant survival is `a_i/z_parent`. An absent zero-duration stem is not asserted to be a positive population. Invalid tuples in the Cartesian grid must have zero recovered weight, because the actual finite target is a mixture of valid displayed trees. They need not be realized as sources. A false input promise may instead yield inconsistent or negative weights.

The recovered finite joint law therefore determines the complete source tensor at EVERY allocation. Any future allowed completion that composes independently with that private tensor has the same law. The original target/source promise, rather than a free-mixture realization argument, supplies an actual finite source; we have proved unknown-size equality forcing, not G3 sufficiency for arbitrary proposed mixture weights.

For a finite private forcing menu, run the construction on each authorized marginal row with its original labels and joint configuration distribution. This determines future allocations of those SAME rows. It does not infer unobserved deterministic summands or a joint counterfactual tensor from marginal rows. Arbitrary external shared registers or multiple ancestral output ports need their own source/observer bridge and are not silently included.

## 7. Actual diagonal probe and the unresolved original-type admission

If the public type permits a root-extension completion, attach the source's single ancestral output to one side of a new ordinary branching root and attach a fresh outside taxon B on the other side. Positive connectors and the B edge are supplied; above the new root use the original unbounded ancestral completion. The old binary source root becomes an ordinary indegree-one/degree-two vertex. Existing cut-child hybrids and outer embedding are preserved by attaching B at the outside. The box occurs once; its internals are unchanged.

For total internal allocation N, sample N copies of B. Choose a fixed completed rooted tree with cherries pairing each internal labelled copy with one B copy, and join those cherries by a fixed comb. The event forbids every internal-only merger before the groups meet, and every B-only merger before they meet. Given both no-merger events, the common ancestral ordinary Kingman completion assigns that labelled topology a known positive rational probability κ_N. Hence

    P(probe_N)=κ_N * known_positive_connector_factors * D(n).

Division is exact postprocessing of a legal final-topology probability, not a hidden-forest measurement or inverse population. Restricting extra context taxa, if present, uses ordinary selected-label projectivity. This is the same no-internal-merger cherry principle as the inherited legal chain tomography and the independently proposed sealed-pendant crossed-cherry channel.

HOWEVER, a public type that fixes the whole taxon menu and excludes a fresh outside B need not admit this completion. A general shared-register box may also correlate its hidden common choice with the exterior, invalidating the private factorization used here. Those are genuine original-contract gates, not routine assumptions. The theorem does not replace them by a richer oracle. It provides a concrete positive source/observer construction to check against the actual declared type.

## 8. Status relative to full G3/G4

Under the precise private root-output/probe and exact-algebraic response contract, the procedure terminates for every finite COMMON target and gives a finite joint certificate against EVERY finite unknown-size COMMON rival. It needs no input source count or parameter margin, and proves arbitrary future tensor equality at that contract.

This candidate is stronger than applying separate one-dimensional stopping rules without reconstructing their joint dependence. It remains a proof candidate until independent review. The original broad G4 master also includes INDEPENDENT routing, external shared registers, general typed output boundaries and declared observation menus that may lack these probes. Their forcing and effective stopping are not supplied here. The original finite-input G3 problem additionally needs one actual source realizing an arbitrary finite response profile; a finite mixture of ordinary trees alone does not provide that source. No full-master closure, undecidability result or formal novelty is claimed.
