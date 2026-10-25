# Collision-safe recovery of entry weights and coalescence-rate multiplicities

Author: dot (OpenAI), 25 October 2026. Written proof attempt awaiting coordinating review. This develops, rather than retrospectively upgrades, the higher-order candidate in COLLIDED-ENTRY-CHECKPOINT.md. No Lean verification, historical novelty or full migration-generator identification is asserted.

## 1. Statement

Retain the known independent-entry boundary and positive-duration constant-epoch contract of GENERIC-ENTRY-MIGRATION-IDENTIFICATION.md. All p_i and lambda_i are positive, migration rates are finite, and the number d of hidden demes is finite but not supplied. Remove the distinctness restriction on x_i=p_i lambda_i.

The exact unmarked timed genealogy laws for all finite copy counts determine the **multiset** of pairs (p_i,lambda_i), including multiplicity. Migration Q may be arbitrary and need not preserve p. This does not yet determine Q or separately prepare equal-parameter hidden demes.

For a target with d demes and q distinct x values, the proof gives the sufficient finite-copy cap

    N = 2d + q(4d+1) <= 4d^2+3d.

This is a target-dependent existence bound for exact genealogy laws and their derivatives, against unknown finite-size rivals obeying the same entry/epoch contract. It is not a practical recommendation, a finite-locus confidence theorem or an effective numerical stopping rule for arbitrary real parameters.

## 2. Observable derivatives

Use f_k(t)=alpha_k exp(K_k t)v_k as in COLLIDED-ENTRY-CHECKPOINT.md: one specified ranked merger chain, first waiting time t, subsequent waits taken to zero by right limits. For r>=0 put

    D_r(k)=f_k^(r)(0)=alpha_k K_k^r v_k.

For k>r, there exist polynomials P_(x,r)(k), one for each distinct x, of degree at most 2r, such that

    D_r(k) = sum_x x^(k-1) P_(x,r)(k).

Their leading coefficients satisfy

    [k^(2r)]P_(x,r) = (-1)^r / 2^r
                         * sum_(i:x_i=x) p_i lambda_i^r.

These statements include r=0, where P_(x,0)=sum_(i:x_i=x)p_i. The crucial point is that finite-rate migration affects only lower polynomial degrees when r is fixed and k varies.

## 3. Count-state proof of the degree bound

Because the entry distribution and v_k are invariant under permutation of the k labelled lineages, compute the scalar alpha_k K_k^r v_k in the occupancy-count chain. Counts c=(c_1,...,c_d) sum to k. Its off-diagonal transition from c to c-e_a+e_b has rate c_a q_ab. Its diagonal entry is

    -sum_a c_a sum_(b!=a)q_ab - sum_a lambda_a binom(c_a,2).

The initial count probability is multinomial(k;c) product_a p_a^(c_a). The terminal vector v_k is zero except at pure states k e_i, where it equals lambda_i^(k-1).

Expand the matrix product K_k^r as a sum over length-r count-state paths, where a diagonal factor leaves counts unchanged and an off-diagonal factor makes one migration. Fix the terminal pure state k e_i, and let l be the number of off-diagonal factors. Since l<=r<k, every state on such a path has at most r lineages outside deme i. Its minority-count template therefore ranges over a finite set independent of k. Conversely, every admissible template is valid for every integer k>r: its main-deme count k-minus-minorities remains positive whenever a main-deme departure is required.

Let s be the number of minority lineages at the initial state, a the number of migrations from i to a minority deme, and b the number of migrations from a minority deme into i. Conservation of the total minority count gives

    s+a-b=0,

so s+a=b<=l. Migrations between two minority demes do not change this equation.

For this fixed path template, the multinomial initial factor is

    (k)_s p_i^k * p_i^(-s)
      * product_(j!=i) p_j^(c_j)/c_j!,

where (k)_s is the falling factorial and the minority initial counts sum to s. It is p_i^k times a polynomial of degree s with a k-independent coefficient. Each of the a main-deme departure rates is linear in k. All minority-departure rates have counts bounded independently of k and hence degree zero. Each diagonal factor has degree at most two. Therefore, after multiplication by the terminal lambda_i^(k-1), this path's contribution is

    p_i x_i^(k-1) times a polynomial of degree
      at most s+a+2(r-l) <= 2r-l.

If l>=1, the degree is at most 2r-1. Thus no path containing an off-diagonal migration contributes to degree 2r. This degree argument explicitly includes the multinomial factor; counting generator degrees alone would miss it.

If l=0, the whole path is the pure state k e_i. Its contribution is exactly

    p_i x_i^(k-1)
      [-k sum_(j!=i)q_ij - lambda_i binom(k,2)]^r.

Its degree-2r coefficient is p_i(-lambda_i/2)^r. Summing all finite templates and then grouping equal x_i proves both claims. Diagonal migration terms are linear, so they cannot alter the top coefficient. QED for the derivative decomposition.

## 4. Recovering the hidden multiset

The r=0 moments recover the distinct positive x-support and its combined weights, as previously proved. Distinct positive x yield linearly independent sequences k^j x^(k-1), with j=0,...,2r. Equivalently, they solve a linear recurrence with characteristic roots x and specified multiplicities; the corresponding consecutive-value confluent Vandermonde matrix is nonsingular. Thus the observable D_r(k) determine every polynomial P_(x,r).

Extracting its top coefficient recovers, for every x, all moments

    m_(x,r) = sum_(i:x_i=x) p_i lambda_i^r

of the positive finite measure

    mu_x = sum_(i:x_i=x) p_i delta_(lambda_i).

Finite-atomic moment uniqueness recovers mu_x. For an atom lambda of mu_x with combined weight W, every underlying deme has the same p=x/lambda. Its multiplicity is therefore

    multiplicity(x,lambda) = W lambda / x.

It is a positive integer because the observations arise from an admitted source. Consequently the complete multiset of (p_i,lambda_i) is identified, including repeated identical pairs.

This is an identification theorem on the admitted source image, not a procedure declaring arbitrary moment inputs biologically realizable. Integer validation, unknown-source recognition and finite-precision certification remain separate questions.

## 5. Why a finite target-dependent cap suffices

Let the target have d demes and q distinct x values.

1. Single-star moments through degree 2q, requiring k<=2q+1, force any positive rival's x-support onto the target support and determine its combined weights.
2. The b_k=f'_k(0) identity in COLLIDED-ENTRY-CHECKPOINT.md, using 2q consecutive k values starting at k=2, determines the two coefficients U_x and m_x for each x. Thus any matching rival has exactly the same number m_x of demes at each support value, and hence the same total d. This is a consequence, not an assumed rival-size bound.
3. For r<=2d, there are q(2r+1) polynomial coefficients in the exponential-polynomial decomposition. Consecutive values k=r+1,...,r+q(2r+1) determine them. Their largest needed copy count is N=2d+q(4d+1).
4. The resulting rate moments through order 2d determine each positive finite mu_x, since it has at most d support atoms. The square-annihilator/Vandermonde argument applies again.

All quantities are derived from marginals of the exact N-copy genealogy law. No finite number of realized loci is claimed to yield those exact derivatives. The resulting bound is deliberately conservative.

## 6. Remaining master-facing obstruction

The generic-entry theorem extracts individual hidden occupancy responses by separating distinct x_i. This collision-safe result identifies the multiset of entry parameters, but **does not yet extend that preparation step to repeated identical pairs (p_i,lambda_i)**. Equal-parameter demes may have different incoming/outgoing migration patterns. Determining those patterns requires joint observable preparation that distinguishes assignments or population partitions rather than only one-star moments.

One candidate next route is to use several large labelled star groups and recover the top-degree coalescence-killing form as their sizes vary. Its cross terms encode whether two groups occupy the same deme; finite migration is lower order in the relevant count variables. This must be proved for actual legal labelled-history coefficients, including group interleavings and noncommuting operators. It is not supplied by this packet and should not be replaced by assuming hidden deme preparation.

## 7. Evidence and attribution

The proof is written, not formally checked. The existing check_entry_coefficients.py and unchanged entry-coefficient-control.json verify the predicted leading coefficients for r=1,2,3 in one fully collided three-deme case using exact rational arithmetic. They do not certify the general path-template proof or finite-copy bound. The finite-atomic and confluent-Vandermonde steps are classical; prior no-migration temporal preparation is explicitly credited in the generic-entry packet. Novelty of this migration extension remains unresolved.
