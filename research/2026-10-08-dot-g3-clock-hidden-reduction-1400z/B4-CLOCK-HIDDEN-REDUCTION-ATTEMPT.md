# Whole negative attempt: clock-hidden automata and original source enforcement

Contributor: dot (OpenAI), 8 October 2026. Failed complete-reduction architecture; source-specific checks submitted for review. No original G3 undecidability or general recognition theorem is claimed.

## 1. Complete reduction attempted

B1's literal group embedding retained a pair-survival target, which bounded every fixed strict alphabet. B4 instead tries to encode a recursively undecidable finite computation in a coarsened scalar output while leaving its contracting clock unobserved. A complete argument would compute a finite algebraic original G3 input y(P) from a Diophantine/automaton instance P, realize every accepting computation by one finite strict source, and prove that EVERY source realizing y(P), across every admitted core, decodes to an accepting computation. Only original finite controls and observables are allowed.

Bell's Polynomially Ambiguous Probabilistic Automata on Restricted Languages gives a closer ambient model than arbitrary matrix mortality. Its Theorem 1 uses commuting upper-triangular rational stochastic matrices and letter-monotone inputs. The arithmetic counters survive stochastic scaling. Upper-triangularity and polynomial path ambiguity therefore do not by themselves prove decidability. The paper's construction is not an actual-source encoding.

Primary source, Theorem 1 and Section 3.1:
https://drops.dagstuhl.de/storage/00lipics/lipics-vol132-icalp2019/LIPIcs.ICALP.2019.105/LIPIcs.ICALP.2019.105.pdf

## 2. Actual private kernels have a stronger spectral restriction

Fix a copy cap m and use the finite CURRENT-FOREST state representation. A state is a current forest, whose completed subtrees are carried opaquely. Applying a private natural kernel K either leaves that forest unchanged or merges at least two current roots. Routing without merger cannot permute the labels or alter the completed subtrees. Consequently, after ordering states by their current number j of roots, the diagonal block is b_j(K) I and every other block strictly lowers j.

For an actual strict private word W, extract one positive ordinary population E(z), 0<z<1. The no-merger coordinates multiply under concatenation. On each remaining natural COMMON or INDEPENDENT factor, projectivity/coupling gives b_(j+1)<=b_j. For an INDEPENDENT bigon this is seen directly by coupling the j Bernoulli route choices with an extra choice: whichever arm receives the extra root, its added pair hazard is nonnegative. COMMON uses the same arm choice. Since lambda_(j+1)-lambda_j=j for lambda_j=binom(j,2),

    0<b_(j+1)(W)<=z^j b_j(W)<b_j(W),
    1=b_1(W)>b_2(W)>...>b_m(W)>0.

The current-forest matrix is therefore diagonalizable over the reals: it is block triangular with scalar diagonal blocks whose scalars are distinct between grades. Equivalently, successive block elimination removes all off-grade blocks and its minimal polynomial divides product_(j=1)^m (t-b_j). The empty forest, if included, is a separate invariant identity block and may be omitted or grouped with the constant eigenvalue.

This is a restriction on each actual private kernel, in both natural modes. It is not an assertion about arbitrary retained multiport cores or changing exposed registers. Invariant-subspace restrictions and quotient representations of a diagonalizable operator are again diagonalizable. A literal intertwining realization of a nontrivial Jordan counter by one strict private source letter is therefore impossible.

Bell's Section 3.1 starts with counters having equal diagonal entries and a nonzero same-eigenvalue superdiagonal, so powers record the integer repetition count. Scaling them to stochastic matrices preserves that Jordan structure. The direct identification of those letters with physical private source letters fails. This does not preclude a different nonlinear or noncommuting computational encoding.

## 3. Hiding the clock still does not rescue a fixed commuting physical alphabet

This check assumes a FINITE FIXED alphabet K_1,...,K_s of actual strict private words with effectively algebraic capped kernels; the letters commute. The observation is a FIXED finite list of affine functionals of the product kernel with fixed effectively algebraic targets. No unknown continuously varying exterior padding or static coefficients are included in this check.

Diagonalize K_1 by a block-unitriangular change of basis respecting the current-root filtration. Its root-grade eigenvalues are distinct. Since every K_i commutes with it, every off-grade block of the transformed K_i is zero; the unchanged diagonal block is b_(j,i) I. Thus the letters share projectors P_j and

    K_i=sum_j b_(j,i) P_j,
    product_i K_i^(n_i)=sum_j [product_i b_(j,i)^(n_i)] P_j,
    1=b_(1,i)>b_(2,i)>...>b_(m,i)>0.

An affine endpoint equality, after absorbing its constant and target into the j=1 coefficient, is exactly

    sum_j c_j product_i b_(j,i)^(n_i)=0,

with effectively algebraic c_j. If every coefficient vanishes, the equality is automatic on the whole alphabet monoid. Otherwise let j0 be the first nonzero coefficient. If no later coefficient is nonzero, equality is impossible. In the remaining case set

    C=sum_(j>j0) |c_j|,
    r=max_(j>j0, i) b_(j,i)/b_(j0,i)<1.

For total letter count n=sum_i n_i, the absolute tail, divided by the positive leading monomial, is at most C r^n. Exact algebraic comparisons find an N with C r^N<|c_j0|. Equality is impossible whenever n>=N. Checking the finitely many shorter words therefore decides this affine equality. For finitely many simultaneous equalities, any nonautomatic equality supplies the bound; if all are automatic, any permitted word satisfies them. The empty-word convention can be handled separately.

This source-specific argument uses ordered root-grade eigenvalues. It is not a generic theorem for commuting triangular PFA and does not conflict with Bell's Jordan-counter construction. It also does not extend the bound to the full continuously varying source alphabet, noncommuting letters, unknown exterior parameters, or nonlinear output constraints.

## 4. Direct nonnegative selectors do not enforce an unbounded physical alphabet

Even if a different family of computational letters were physically realized, G3 admits all fresh parameters and all alternative cores. A construction using selected letters supplies only the forward implication. The reverse implication requires an original observation mechanism that excludes every unencoded realization.

For INDEPENDENT private natural sources, the inherited ALL-STRICT-CONVEX-COROLLARY-V2 rules out a nontrivial nonnegative affine endpoint functional that vanishes on any strict source. That cannot serve as the missing alphabet selector.

For a COMMON private word, a finite-cap affine full-kernel score has form E[P(X)], where X in (0,1) is total path survival and P is a polynomial in the retained sparse moment functions and a constant. Suppose the proposed selector uses a nonzero P nonnegative on (0,1) and requires E[P(X)]=0. Every support atom must then lie in the finite root set of P. With L unequal Bernoulli factors, the partial products b,bq_1,...,bq_1...q_L give at least L+1 distinct support points, each with positive probability. Hence L is bounded by the number of roots minus one. Equal-arm factors carry no discrete information and are absorbed into ordinary time. If P is identically zero, it imposes no restriction.

This is the familiar exposed-moment/support argument already used by the prior Chebyshev and count-admission work, not a new source theorem. It shows that this direct selector enforces bounded factor count rather than an unbounded computation. It does not say every polynomial of endpoint probabilities has a pointwise nonnegative latent-polynomial representation.

Finite protected original IDs can constrain their retained sites. They do not authorize a new equality on every unknown fresh position. Existing nonlinear COMMON calibration fixes total survival or equal arms; no accepted original-menu selector forcing an arbitrary unbounded discrete alphabet was identified. A nonlinear, stateful, or whole-fibre selector would need an actual construction and proof; it is not supplied by postprocessing observations with arbitrary polynomials.

## 5. Complete attempt outcome

The source encoding fails before a valid reduction is obtained: the closest commuting Jordan-counter letters do not satisfy the physical spectral restriction; their fixed commuting physical substitutes have an effective coarsened affine-output search; and direct nonnegative endpoint selectors cannot enforce the missing unbounded alphabet. No effective map y(P), source-admitted equivalence, or all-core converse was constructed.

None of this proves G3 decidable or undecidable. Noncommuting diagonalizable alphabets, variable small clocks, and more complicated original coupled selectors are not excluded as possible ingredients. They cannot simply be asserted to simulate the cited PFA. The whole negative proof remains incomplete, and the failures above record why this particular instantiated architecture does not establish it.

## 6. Next whole-proof direction

A positive alternative must exploit the actual ordered root-grade structure while allowing noncommutativity, continuously varying strict parameters, all retained cores and the original coupled target. The tempting next architecture is a source-specific elimination of long root-graded words by finite critical/pivot normal forms, followed by effective algebraic feasibility and a complete boundary branch. It must provide a bound on at least one realizing word from initialization, not a finite exact quotient for every reachable prefix. Existing unbounded-count and fixed-target quotient checks prevent replacing that input-dependent obligation by a menu-only or all-prefix claim.
